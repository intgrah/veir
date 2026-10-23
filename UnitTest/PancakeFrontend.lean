module

import Veir.Frontend.Pancake
import Veir.Interpreter.Basic
meta import Veir.Frontend.Pancake
meta import Veir.Interpreter.Basic

open Veir Veir.PancakeSource Veir.PancakeFrontend

private def localKey : Variable := ⟨.local, .implode [0, 128, 255]⟩
private def globalKey : Variable := ⟨.global, .implode [0, 128, 255]⟩
private def variableExpr (key : Variable) : ExpHOL 8 := .var key.kind key.name

private def nested : ExpHOL 8 := .op .add [
  .panop .mul [variableExpr localKey, .const 3],
  .cmp .less (variableExpr globalKey) (.const 0),
  .op .sub [variableExpr localKey, .const 1]]

private def inputs (key : Variable) : Option (BitVec 8) :=
  if key = localKey then some 5 else if key = globalKey then some 255 else none

/- Exercise the entire AST → serialized SSA → parser → verifier → interpreter path. -/
private def execute {width : Nat} [NeZero width] (expression : ExpHOL width)
    (environment : Variable → Option (BitVec width)) : Except String (Array RuntimeValue) := do
  let parsed ← toIR expression
  let args ← parsed.inputs.mapM fun key => do
    let some value := environment key | throw "missing input"
    return PancakeScalar.encodeWord value
  if h : parsed.function.InBounds parsed.context.raw then
    let some function := FunctionOp.of? parsed.function parsed.context.raw
      | throw "expected a function"
    match interpretFunction (ctx := parsed.context) function args.toArray MemoryState.empty h with
    | .ok (_, values) => return values
    | .fail _ => throw "interpreter failed"
    | .ub _ => throw "interpreter produced UB"
  else throw "invalid function pointer"

#guard execute nested inputs == .ok #[PancakeScalar.encodeWord (20#8)]
#guard Id.run do
  let .ok emitted := toMLIR nested | return false
  return emitted.inputs == [localKey, globalKey]

/- A variable-only expression needs no operations; repeated variables share a block argument. -/
#guard execute (variableExpr localKey) inputs == .ok #[PancakeScalar.encodeWord (5#8)]
#guard Id.run do
  let .ok emitted := toMLIR (.op .add [variableExpr localKey, variableExpr localKey]) | return false
  return emitted.inputs == [localKey]
#guard execute (.op .add [variableExpr localKey, variableExpr localKey]) inputs ==
  .ok #[PancakeScalar.encodeWord (10#8)]

#guard execute (.op .and [] : ExpHOL 32) (fun _ => none) ==
  .ok #[PancakeScalar.encodeWord (0xffffffff#32)]
#guard execute (.panop .mul [.const 0x8000000000000000, .const 2] : ExpHOL 64) (fun _ => none) ==
  .ok #[PancakeScalar.encodeWord (0#64)]
#guard execute (.cmp .less (.const 1) (.const 0) : ExpHOL 1) (fun _ => none) ==
  .ok #[PancakeScalar.encodeWord (1#1)]
#guard execute (.const 255 : ExpHOL 8) (fun _ => none) ==
  .ok #[PancakeScalar.encodeWord (255#8)]

/- Missing inputs fail in both expression and runtime semantics. -/
#guard Id.run do
  let some fragment := translate nested | return false
  return evaluateRuntime 8 (fun _ => none) fragment == none &&
    evaluateRuntime 8 (fun key => (inputs key).map PancakeScalar.encodeWord) fragment ==
      some (PancakeScalar.encodeWord (20#8))

#guard !(toMLIR (.op .sub [] : ExpHOL 8)).isOk
#guard !(toMLIR (.panop .mul [.const 1] : ExpHOL 8)).isOk
#guard !(toMLIR (.op .add [.load32 (.const 0)] : ExpHOL 8)).isOk
#guard !(toMLIR (.shift .lsl (.const 1) (.const 2) : ExpHOL 8)).isOk
#guard !(toMLIR (.rstruct [] : ExpHOL 8)).isOk

/-- info: 'Veir.PancakeFrontend.translate_runtime_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms translate_runtime_correct
