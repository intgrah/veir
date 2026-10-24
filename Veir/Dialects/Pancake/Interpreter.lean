module

public import Veir.Dialects.Pancake.OpInfo
public import Veir.Interpreter.Memory
public import Veir.Interpreter.RuntimeValue.Basic
public import Flapjack.Pancake.WordLang
public import Flapjack.Compiler.Encoders.Asm
public import Flapjack.Pancake.Semantics.PanSemStateEval
import all Veir.IR.Attribute

namespace Veir.Pancake
public section

/-- A source word has concrete bits: poison is outside the Pancake value representation. -/
@[expose] def encodeWord (value : BitVec width) : RuntimeValue := .int width (.val value)

@[expose] def decodeWord (width : Nat) : RuntimeValue → Option (BitVec width)
  | .int actual (.val value) => if h : actual = width then some (h ▸ value) else none
  | _ => none

@[simp] theorem decodeWord_encodeWord (value : BitVec width) :
    decodeWord width (encodeWord value) = some value := by simp [encodeWord, decodeWord]

@[simp] theorem decodeWord_poison : decodeWord width (.int otherWidth .poison) = none := rfl

theorem encodeWord_injective : Function.Injective (encodeWord (width := width)) := by
  intro a b h
  have := congrArg (decodeWord width) h
  simpa using this

/-- Use the imported semantics directly; no source syntax or evaluator is duplicated. -/
@[expose] def evalWords {width : Nat} [NeZero width]
    (opType : Pancake) (props : propertiesOf opType) (values : List (BitVec width)) :
    Option (BitVec width) :=
  match opType, props with
  | .const, props =>
    if values.isEmpty && props.value.type == IntegerType.signless width then
      some (BitVec.ofInt width props.value.value)
    else none
  | .op, props => Flapjack.wordOpHOL props.operator values
  | .panop, props => Flapjack.panOpHOL props.operator values
  | .cmp, props => match values with
    | [left, right] => some (Flapjack.Compiler.Encoders.Asm.wordCmpResultHOL props.operator left right)
    | _ => none

@[expose] def interpretScalar (opType : Pancake) (props : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) : Option (Array RuntimeValue) := do
  let [resultType] := resultTypes.toList | none
  let .integerType intType := resultType.val | none
  if intType.signedness != .signless then none else do
    if h : intType.bitwidth = 0 then none else do
      let _ : NeZero intType.bitwidth := ⟨h⟩
      let values ← operands.toList.mapM (decodeWord intType.bitwidth)
      let result ← evalWords opType props values
      return #[encodeWord result]

/-- Scalar instructions preserve memory, produce no control-flow action, and never return UB. -/
@[expose] def interpretOp' (opType : Pancake) (props : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    (blockOperands : Array BlockPtr) (memory : MemoryState) :
    Interp (Array RuntimeValue × MemoryState × Option ControlFlowAction) := do
  if !blockOperands.isEmpty then none else do
    let values ← interpretScalar opType props resultTypes operands
    return (values, memory, none)

@[simp] theorem decodeWords_encodeWords (values : List (BitVec width)) :
    (values.map encodeWord).mapM (decodeWord width) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [List.mapM_cons, ih]

/-- The runtime adapter preserves both successful word results and source-operation failure. -/
theorem interpret_encoded {width : Nat} [NeZero width] (opType : Pancake)
    (props : propertiesOf opType) (values : List (BitVec width)) :
    interpretScalar opType props #[TypeAttr.of IntegerType (.signless width)]
      (values.map encodeWord).toArray = (evalWords opType props values).map (fun value => #[encodeWord value]) := by
  simp only [interpretScalar, TypeAttr.of_val]
  change (if (IntegerType.signless width).signedness != .signless then none else _) = _
  simp only [IntegerType.signless, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    NeZero.ne width, decodeWords_encodeWords]
  simp only [↓reduceDIte]
  cases h : evalWords opType props values <;> simp [h]

theorem interpretOp_of_scalar (opType : Pancake) (props : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands values : Array RuntimeValue)
    (memory : MemoryState) (h : interpretScalar opType props resultTypes operands = some values) :
    interpretOp' opType props resultTypes operands #[] memory = .ok (values, memory, none) := by
  simp [interpretOp', h]

theorem interpretOp_ne_ub (opType : Pancake) (props : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    (blockOperands : Array BlockPtr) (memory : MemoryState) (location : Option OperationPtr) :
    interpretOp' opType props resultTypes operands blockOperands memory ≠ .ub location := by
  simp only [interpretOp']
  split
  · simp
  · cases interpretScalar opType props resultTypes operands <;> simp

end
end Veir.Pancake
