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

open FSharp.Data
open FSharp.Data.JsonExtensions
open B2R2
open B2R2.BinIR.LowUIR
open B2R2.FrontEnd.BinFile
open B2R2.FrontEnd.BinInterface
open B2R2.MiddleEnd.BinGraph
open B2R2.MiddleEnd.BinEssence

type EVMTrampolineAnalysis (abiFile) =

  let keccak = SHA3Core.Keccak.Keccak(SHA3Core.Enums.KeccakBitType.K256)

  let computeKeccak256 (str: string) =
      let hashStr = keccak.Hash(str).[0..7]
      System.UInt32.Parse(hashStr, System.Globalization.NumberStyles.HexNumber)

  // Parse function information and update signature to name mapping.
  let parseFunc accMap (funcJson: JsonValue) =
    let name = funcJson?name.AsString()
    let argTypes = [ for v in funcJson?inputs -> v?``type``.AsString() ]
    let argStr = String.concat "," argTypes
    let signature = sprintf "%s(%s)" name argStr |> computeKeccak256
    Map.add signature name accMap

  // Returns a mapping from a function signature to its name.
  let parseABI () =
    let abiStr = System.IO.File.ReadAllText(abiFile)
    let abiJson = JsonValue.Parse(abiStr)
    let isFunc (json: JsonValue) = json?``type``.AsString() = "function"
    let funcJsons = [ for v in abiJson -> v ] |> List.filter isFunc
    List.fold parseFunc Map.empty funcJsons

  // Find functions from the IR statements of a basic block.
  let rec findFuncsFromBlock curState stmts accMap =
    match stmts with
    | [] -> accMap
    | [ { S = InterCJmp(condExp, tExp, fExp) } ] ->
      let condV = StackAnalysis.eval condExp.E curState
      let tTarg = StackAnalysis.eval tExp.E curState
      let fTarg = StackAnalysis.eval fExp.E curState
      match condV, tTarg, fTarg with
      | CmpWith s, Fixed a, Fixed _ when 0I < s && s <= BigInteger.getMask 32 ->
        Map.add (uint32 s) (uint64 a) accMap
      | _ -> accMap
    | headStmt :: tailStmts ->
      let curState = StackAnalysis.exec headStmt curState
      findFuncsFromBlock curState tailStmts accMap

  // Find functions from the CFG.
  let rec findFuncsFromCFG cfg acc (bb: Vertex<IRBasicBlock>) =
    let (accVisited, accMap) = acc
    let accVisited = Set.add bb.VData.PPoint accVisited
    let stmts = bb.VData.GetIRStatements () |> Array.concat |> Array.toList
    // Run intra-basic-block analysis that starts with an empty state.
    let accMap = findFuncsFromBlock State.init stmts accMap
    // Stop recursing into function entries or already visited blocks.
    let isValidSucc (b: Vertex<IRBasicBlock>) =
      not (Set.contains b.VData.PPoint accVisited) &&
      not (Map.exists (fun _ a -> a = b.VData.PPoint.Address) accMap)
    let nextBBs = List.filter isValidSucc (DiGraph.getSuccs cfg bb)
    List.fold (findFuncsFromCFG cfg) (accVisited, accMap) nextBBs

  // Returns a mapping from function signature to its address.
  let findFuncs (ess: BinEssence) =
    match ess.GetFunctionCFG(0UL) with
    | Error _ -> failwith "Failed to retrieve entry CFG"
    | Ok (cfg, root) -> findFuncsFromCFG cfg (Set.empty, Map.empty) root |> snd

  let makeSymbol name addr =
    { Address = addr
      Name = name
      Kind = FunctionType
      Target = TargetKind.StaticSymbol
      LibraryName = ""
      ArchOperationMode = ArchOperationMode.NoMode }

  let updateSymbol (fi: FileInfo) sigToName sigToAddr sign =
    match Map.tryFind sign sigToName, Map.tryFind sign sigToAddr with
    | Some name, Some addr -> fi.AddSymbol addr (makeSymbol name addr)
    | _ -> ()

  let updateSigMaps (ess: BinEssence) sigToName sigToAddr =
    Map.iter (fun s n -> ess.SigToName.[s] <- n) sigToName
    Map.iter (fun s a -> ess.SigToAddr.[s] <- a) sigToAddr

  let analyzeTrampoline ess =
    let hdl = ess.BinHandle
    let bytes = hdl.FileInfo.BinReader.Bytes
    let newHdl = BinHandle.Init (hdl.FileInfo.ISA, bytes)
    let sigToName = if abiFile <> "" then parseABI () else Map.empty
    let sigToAddr = findFuncs ess
    let entrySigs = if abiFile <> "" // If ABI is given, use it as a baseline
                    then Map.toList sigToName |> List.unzip |> fst
                    else Map.toList sigToAddr |> List.unzip |> fst
    List.iter (updateSymbol newHdl.FileInfo sigToName sigToAddr) entrySigs
    let folder acc s = try Map.find s sigToAddr :: acc with _ -> acc
    let entryAddrs = 0UL :: List.fold folder [] entrySigs
    let essEntries = List.map (fun a -> a, ArchOperationMode.NoMode) entryAddrs
    match BinEssence.initByEntries newHdl essEntries with
    | Error _ -> failwith "Failed to analyze trampoline code"
    | Ok ess -> updateSigMaps ess sigToName sigToAddr
                ess

  interface IAnalysis with
    member __.Name = "EVM Trampoline Analysis"

    member __.Run ess hint =
      analyzeTrampoline ess, hint
