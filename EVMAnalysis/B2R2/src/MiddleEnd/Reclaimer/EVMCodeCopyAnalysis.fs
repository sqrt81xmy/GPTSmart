(*
  B2R2 - the Next-Generation Reversing Platform

  Copyright (c) SoftSec Lab. @ KAIST, since 2016

  Permission is hereby granted, free of charge, to any person obtaining a copy
  of this software and associated documentation files (the "Software"), to deal
  in the Software without restriction, including without limitation the rights
  to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
  copies of the Software, and to permit persons to whom the Software is
  furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in all
  copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.
*)

namespace B2R2.MiddleEnd.Reclaimer

open B2R2
open B2R2.FrontEnd.BinFile
open B2R2.FrontEnd.BinInterface
open B2R2.FrontEnd.BinLifter.EVM
open B2R2.MiddleEnd.BinEssence

type EVMCodeCopyAnalysis () =

  let updatePushList (evmIns: EVMInstruction) pushList =
    match evmIns.Info.Opcode with
    | Opcode.PUSH1 bv
    | Opcode.PUSH2 bv
    | Opcode.PUSH3 bv
    | Opcode.PUSH4 bv -> BitVector.toUInt64 bv :: pushList
    | _ -> []

  let tryResolveOffset pushList =
    match pushList with
    | dstOffset :: srcOffset :: _ when dstOffset = 0UL -> Some (int srcOffset)
    | _ -> None

  // XXX. TODO: Use IR CFG to find and analyze codecopy instruction. Currently
  // the basic block is not reachable in our CFG.
  let rec findCodeCopyOffset hdl bp pushList =
    if not (BinaryPointer.IsValid bp) then failwith "Failed to find codecopy"
    match BinHandle.TryParseInstr (hdl, bp = bp) with
    | Error _ -> failwith "Failed to find codecopy"
    | Ok ins ->
      let nextBP = BinaryPointer.Advance bp (int ins.Length)
      let evmIns = ins :?> EVMInstruction
      if evmIns.Info.Opcode = Opcode.CODECOPY then
        match tryResolveOffset pushList with
        | Some offset -> offset
        | None -> findCodeCopyOffset hdl nextBP pushList
      else findCodeCopyOffset hdl nextBP (updatePushList evmIns pushList)

  let recoverCopiedCode (ess: BinEssence) =
    let hdl = ess.BinHandle
    let initBp = hdl.FileInfo.ToBinaryPointer hdl.FileInfo.BaseAddress
    let codeCopyOffset = findCodeCopyOffset hdl initBp []
    let bytes = hdl.FileInfo.BinReader.Bytes
    let len = bytes.Length
    if len <= codeCopyOffset then failwith "Invalid codecopy offset"
    let copiedBytes = bytes.[codeCopyOffset .. (len - 1)]
    let newHdl = BinHandle.Init (hdl.FileInfo.ISA, copiedBytes)
    BinEssence.init(newHdl)

  interface IAnalysis with
    member __.Name = "EVM Code Copy Analysis"

    member __.Run ess hint =
      recoverCopiedCode ess, hint
