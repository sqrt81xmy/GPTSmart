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

namespace B2R2.MiddleEnd.BinEssence

open B2R2
open System.Collections.Generic
open AnalysisHelper

type ValueDom =
  | Fixed of bigint
  | CmpWith of bigint
  | Unknown

module ValueDom =

  let MAX_UINT256 = System.Numerics.BigInteger.Pow(2I, 256) - 1I

  let toString = function
    | Fixed i -> bigIntToStr i
    | CmpWith i -> sprintf "(? == %s)" (bigIntToStr i)
    | Unknown -> "unknown"

  let zero = Fixed 0I

  let add v1 v2 =
    match v1, v2 with
    | Fixed i1, Fixed i2 -> Fixed ((i1 + i2) &&& MAX_UINT256)
    | _, _ -> Unknown

  let sub v1 v2 =
    match v1, v2 with
    | Fixed i1, Fixed i2 -> Fixed (i1 - i2) // No masking to retain negative.
    | _, _ -> Unknown

  let mul v1 v2 =
    match v1, v2 with
    | Fixed i1, Fixed i2 -> Fixed ((i1 * i2) &&& MAX_UINT256)
    | _, _ -> Unknown

  let div v1 v2 =
    match v1, v2 with
    | Fixed i1, Fixed i2 -> Fixed (i1 / i2)
    | _, _ -> Unknown

  let andOp v1 v2 =
    match v1, v2 with
    | Fixed i1, Fixed i2 -> Fixed (i1 &&& i2)
    | _, _ -> Unknown

  let orOp v1 v2 =
    match v1, v2 with
    | Fixed i1, Fixed i2 -> Fixed (i1 ||| i2)
    | _, _ -> Unknown

  let eq v1 v2 =
    match v1, v2 with
    | Fixed i, _ | _, Fixed i-> CmpWith i
    | _, _ -> Unknown

  let extractLSB v =
    match v with
    | Fixed i -> Fixed (i &&& 1I)
    | CmpWith i -> CmpWith i
    | Unknown -> Unknown

type State = {
  RegMap: Map<string,ValueDom>
  Stack: Map<bigint, ValueDom> // Mapping from stack offset to content.
}

module State =

  let init =
    { RegMap = Map.add STACK_PTR ValueDom.zero Map.empty
      Stack = Map.empty }

  let readVar reg state =
    match Map.tryFind reg state.RegMap with
    | None -> Unknown
    | Some x -> x

  let readTempVar tmpNo state =
    match Map.tryFind (tmpVarToVar tmpNo) state.RegMap with
    | None -> Unknown
    | Some x -> x

  let private filterStack spVal stack =
    match spVal with
    | Fixed n -> Map.filter (fun k _ -> k <= n) stack
    | CmpWith _ | Unknown -> stack

  let updateVar reg v state =
    let newRegMap = Map.add reg v state.RegMap
    let newStack = if reg = STACK_PTR then filterStack v state.Stack
                   else state.Stack
    { RegMap = newRegMap; Stack = newStack }

  let updateTempVar tmpNo v state =
    { state with RegMap = Map.add (tmpVarToVar tmpNo) v state.RegMap }

  let tryResolveStackPtr state =
    match Map.tryFind STACK_PTR state.RegMap with
    | Some (Fixed x) -> Some x
    | Some _ | None -> None

  let loadFromStackPtr offset state =
    match tryResolveStackPtr state with
    | Some x when Map.containsKey (x + offset) state.Stack ->
      Map.find (x + offset) state.Stack
    | Some _ | None -> Unknown

  let storeToStackPtr offset v state =
    match tryResolveStackPtr state with
    | Some x -> { state with Stack = Map.add (x + offset) v state.Stack }
    | None -> state

  let isInlineCall (curAddr: Addr) state =
    let checker k = function
      | Fixed n -> n = bigint curAddr + 1I
      | CmpWith _ | Unknown -> false
    Map.exists checker state.Stack

  let private liftStackPtr delta state =
    match Map.tryFind STACK_PTR state.RegMap with
    | Some (Fixed x) -> updateVar STACK_PTR (Fixed (x + delta)) state
    | Some _ | None -> state

  let private cleanUpInlinedCallArgs (curAddr: Addr) state =
    let entries = Map.toList state.Stack
    let rec findNewSPVal acc = function
      | [] -> failwith "Must be preceded by isInlineCall()"
      | (k, Fixed n) :: _ when n = bigint curAddr + 1I -> k
      | head :: tails -> findNewSPVal (head :: acc) tails
    let newSPVal = findNewSPVal [] entries
    updateVar STACK_PTR (Fixed newSPVal) state

  let fixForInlinedFallthrough srcAddr liftOpt state =
    match liftOpt with
    | Some delta -> liftStackPtr delta state
    | None -> // Fall back to heuristic and adjust SP to the saved return addr.
      printfn "Stack lift offset not found @ %x" srcAddr
      cleanUpInlinedCallArgs srcAddr state

  // DEBUG
  let printStack state =
    let stackPtr = readVar STACK_PTR state
    printfn "SP : %s" (ValueDom.toString stackPtr)
    let iterator (k: bigint, v) =
      printfn "[%s] : %s" (bigIntToStr k) (ValueDom.toString v)
    Map.toList state.Stack |> List.rev |> List.iter iterator

type StateMap = Dictionary<ProgramPoint, State>

module StateMap =

  let contains ppoint (map: StateMap) =
    map.ContainsKey(ppoint)

  let read ppoint (map: StateMap) =
    map.[ppoint]

  // Our analysis is one-time, without join or fixpoint. This means we assume
  // that even if a basic block has incoming edges, its outgoing edges must not
  // be affected by which incoming edge was taken. For this assumption to hold,
  // we must detect (intra-contract) inlined function calls with heuristics.
  let update ppoint state (map: StateMap) =
    if not (map.ContainsKey(ppoint)) then map.[ppoint] <- state

  let propagate isFallThrough src dst inMap outMap liftOpt =
    let outState = read src outMap
    let srcAddr = src.Address
    if isFallThrough && State.isInlineCall srcAddr outState then
      let newState = State.fixForInlinedFallthrough srcAddr liftOpt outState
      update dst newState inMap
    else update dst outState inMap
