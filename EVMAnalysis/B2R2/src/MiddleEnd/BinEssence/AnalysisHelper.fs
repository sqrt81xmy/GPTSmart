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

module B2R2.MiddleEnd.BinEssence.AnalysisHelper

open B2R2
open System.Collections.Generic

let EVM_WORDSIZE = 32I
let STACK_PTR = "SP"

let tmpVarToVar tmpVarNo =
  sprintf "T_%d" tmpVarNo

let bigIntToStr (i: bigint) =
  if i >= 0I then i.ToString("X")
  else "-" + (-i).ToString("X")

// Records of how stack pointer changes by calling each function.
type StackLiftInfo = Dictionary<Addr,bigint>

module StackLiftInfo =

  let update func lift (info: StackLiftInfo) =
    info.[func] <- lift

  let tryLookup func (info: StackLiftInfo) =
    if info.ContainsKey(func) then Some info.[func] else None
