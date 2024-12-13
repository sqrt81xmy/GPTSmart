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
open B2R2.BinIR
open B2R2.BinIR.LowUIR
open System.Collections.Generic
open AnalysisHelper

module StackAnalysis =

  exception private NonLinearBlockException

  let rec eval valExp state =
    match valExp with
    | Num bv -> ValueDom.Fixed (bv.BigValue())
    | Var (_, _, r, _) -> State.readVar r state
    | TempVar (_, tmpVarNo) -> State.readTempVar tmpVarNo state
    // Binary operations
    | BinOp (BinOpType.ADD, _, { E = exp1 }, { E = exp2 }, _) ->
      ValueDom.add (eval exp1 state) (eval exp2 state)
    | BinOp (BinOpType.SUB, _, { E = exp1 }, { E = exp2 }, _) ->
      ValueDom.sub (eval exp1 state) (eval exp2 state)
    | BinOp (BinOpType.MUL, _, { E = exp1 }, { E = exp2 }, _) ->
      ValueDom.mul (eval exp1 state) (eval exp2 state)
    | BinOp (BinOpType.DIV, _, { E = exp1 }, { E = exp2 }, _) ->
      ValueDom.div (eval exp1 state) (eval exp2 state)
    | BinOp (BinOpType.AND, _, { E = exp1 }, { E = exp2 }, _) ->
      ValueDom.andOp (eval exp1 state) (eval exp2 state)
    | BinOp (BinOpType.OR, _, { E = exp1 }, { E = exp2 }, _) ->
      ValueDom.orOp (eval exp1 state) (eval exp2 state)
    | RelOp (RelOpType.EQ, { E = exp1 }, { E = exp2 }, _) ->
      ValueDom.eq (eval exp1 state) (eval exp2 state)
    // Special cases of casting operation.
    | Extract (e, 1<rt>, 0, _) -> eval e.E state |> ValueDom.extractLSB
    | Cast (CastKind.ZeroExt, 256<rt>, e, _) -> eval e.E state
    // [SP]
    | Load (_, _, { E = Var (_, _, r, _) }, _) when r = STACK_PTR ->
      State.loadFromStackPtr 0I state
    // [SP - n]
    | Load (_, _, { E = BinOp (BinOpType.SUB, _,
                              { E = Var (_, _, r, _) },
                              { E = Num bv }, _) }, _) when r = STACK_PTR ->
      let offset = -(bv.BigValue())
      State.loadFromStackPtr offset state
    | _ -> ValueDom.Unknown

  let exec stmt state =
    match stmt.S with
    // Reg := exp
    | Put ({ E = Var (_, _, r, _)}, { E = valExp }) ->
      State.updateVar r (eval valExp state) state
    // TempReg := exp
    | Put ({ E = TempVar (_, tmpVarNo)}, { E = valExp }) ->
      State.updateTempVar tmpVarNo (eval valExp state) state
    // [SP] := exp
    | Store (_, { E = Var (_, _, r, _)}, { E = valExp }) when r = STACK_PTR ->
      State.storeToStackPtr 0I (eval valExp state) state
    // [SP - n] := exp
    | Store (_, { E = BinOp (BinOpType.SUB, _,
                            { E = Var (_, _, r, _) },
                            { E = Num bv }, _) },
              { E = valExp }) when r = STACK_PTR ->
      let offset = -(bv.BigValue())
      State.storeToStackPtr offset (eval valExp state) state
    | Jmp _ | CJmp _ -> raise NonLinearBlockException
    | _ -> state

  let private runOnStmts inStateMap outStateMap addr inState stmts =
    let folder accState i stmt =
      let curPPoint = ProgramPoint (addr, i)
      StateMap.update curPPoint accState inStateMap
      let outState = exec stmt accState
      StateMap.update curPPoint outState outStateMap
      outState
    Array.foldi folder inState stmts |> fst

  let private runOnAddrs instrMap inStateMap outStateMap sAddr addrs =
    let startState = StateMap.read (ProgramPoint(sAddr, 0)) inStateMap
    let folder accState addr =
      let stmts = (instrMap: InstrMap).[addr].Stmts
      runOnStmts inStateMap outStateMap addr accState stmts
    ignore (List.fold folder startState addrs)

  // Runs stack state analysis on a basic block starting at 'sAddr' and composed
  // of 'blockAddrs'. Aborts if its IR-level CFG is non-linear). Calculates the
  // state after the execution of the block and updates outStateMap with it.
  let rec run sAddr blockAddrs instrMap inStateMap outStateMap =
    try runOnAddrs instrMap inStateMap outStateMap sAddr blockAddrs with
    | NonLinearBlockException -> printfn "Skip non-linear block at 0x%x" sAddr
    | :? KeyNotFoundException -> printfn "State not found for 0x%x" sAddr
