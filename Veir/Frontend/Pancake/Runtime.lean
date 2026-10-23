module

public import Veir.Frontend.Pancake.SourceCorrectness
import all Veir.Frontend.Pancake.Basic
import all Veir.Dialects.Pancake.Scalar

namespace Veir.PancakeFrontend
public section

@[expose] def Instruction.opType (instruction : Instruction) : Pancake :=
  match instruction.operation with
  | .constant _ => .const
  | .binop _ => .op
  | .multiply => .panop
  | .compare _ => .cmp

@[expose] def Instruction.properties (instruction : Instruction) : Pancake.propertiesOf instruction.opType :=
  match instruction.operation with
  | .constant value => Pancake.constantProperties value
  | .binop operator => Pancake.operatorProperties (PancakeScalar.binOpName operator)
  | .multiply => Pancake.operatorProperties "mul".toUTF8
  | .compare operator => Pancake.operatorProperties (PancakeScalar.cmpName operator)

/-- Dispatch through the real Pancake opcode/property decoder, not a second arithmetic evaluator. -/
@[expose] def runRuntime (width : Nat) (inputs : Variable → Option RuntimeValue) :
    List Instruction → List RuntimeValue → Option (List RuntimeValue)
  | [], values => some values
  | instruction :: rest, values => do
    let operands ← instruction.operands.mapM (Ref.read inputs values)
    let results ← Pancake.interpretScalar instruction.opType instruction.properties
      #[TypeAttr.of IntegerType (.signless width)] operands.toArray
    let [result] := results.toList | none
    runRuntime width inputs rest (values ++ [result])

@[expose] def evaluateRuntime (width : Nat) (inputs : Variable → Option RuntimeValue)
    (fragment : Fragment) : Option RuntimeValue := do
  let values ← runRuntime width inputs fragment.code []
  fragment.result.read inputs values

theorem instruction_correspondence {width : Nat} [NeZero width]
    (instruction : Instruction) (values : List (BitVec width)) :
    Pancake.interpretScalar instruction.opType instruction.properties
      #[TypeAttr.of IntegerType (.signless width)] (values.map PancakeScalar.encodeWord).toArray =
      (PancakeScalar.evaluate instruction.operation values).map
        (fun value => #[PancakeScalar.encodeWord value]) := by
  have h : Pancake.scalarOperation? instruction.opType instruction.properties = some instruction.operation := by
    cases instruction with
    | mk operation operands => cases operation <;>
      simp only [Instruction.opType, Instruction.properties, Pancake.scalarOperation_const,
        Pancake.scalarOperation_binop, Pancake.scalarOperation_mul, Pancake.scalarOperation_cmp]
  simp only [Pancake.interpretScalar, h]
  exact PancakeScalar.interpret_encoded instruction.operation values

theorem Ref.read_map (f : α → β) (inputs : Variable → Option α) (values : List α) (ref : Ref) :
    ref.read (fun key => (inputs key).map f) (values.map f) = (ref.read inputs values).map f := by
  cases ref <;> simp [Ref.read]

theorem refs_read_map (f : α → β) (inputs : Variable → Option α) (values : List α) (refs : List Ref) :
    refs.mapM (Ref.read (fun key => (inputs key).map f) (values.map f)) =
      (refs.mapM (Ref.read inputs values)).map (List.map f) := by
  induction refs with
  | nil => rfl
  | cons ref refs ih =>
    simp only [List.mapM_cons, Ref.read_map, ih]
    cases ref.read inputs values <;> cases refs.mapM (Ref.read inputs values) <;> rfl

theorem runRuntime_encode {width : Nat} [NeZero width]
    (inputs : Variable → Option (BitVec width)) (code : List Instruction)
    (initial : List (BitVec width)) :
    runRuntime width (fun key => (inputs key).map PancakeScalar.encodeWord) code
      (initial.map PancakeScalar.encodeWord) =
      (run inputs code initial).map (List.map PancakeScalar.encodeWord) := by
  induction code generalizing initial with
  | nil => rfl
  | cons instruction rest ih =>
    simp only [runRuntime, run, refs_read_map]
    cases hop : instruction.operands.mapM (Ref.read inputs initial) with
    | none => rfl
    | some operands =>
      dsimp only [Option.map, Bind.bind, Option.bind]
      rw [instruction_correspondence]
      cases hv : PancakeScalar.evaluate instruction.operation operands with
      | none => rfl
      | some value =>
        simpa [List.map_append, Option.map] using ih (initial ++ [value])

theorem evaluateRuntime_encode {width : Nat} [NeZero width]
    (inputs : Variable → Option (BitVec width)) (fragment : Fragment) :
    evaluateRuntime width (fun key => (inputs key).map PancakeScalar.encodeWord) fragment =
      (evaluate inputs fragment).map PancakeScalar.encodeWord := by
  simp only [evaluateRuntime, evaluate]
  rw [show ([] : List RuntimeValue) = ([] : List (BitVec width)).map PancakeScalar.encodeWord from rfl,
    runRuntime_encode]
  cases run inputs fragment.code [] <;> simp [Ref.read_map]

/-- Only source word values cross the runtime boundary. -/
@[expose] def sourceRuntime {width : Nat} [NeZero width] : PancakeSource.ValueHOL width → Option RuntimeValue
  | .val (.word value) => some (PancakeScalar.encodeWord value)
  | _ => none

/-- The frontend theorem for the emitted SSA sequence and VeIR's scalar interpreter. -/
theorem translate_runtime_correct {width : Nat} [NeZero width]
    (inputs : Variable → Option (BitVec width)) (expression : PancakeSource.ExpHOL width)
    (fragment : Fragment) (h : translate expression = some fragment) :
    evaluateRuntime width (fun key => (inputs key).map PancakeScalar.encodeWord) fragment =
      (PancakeSource.evalScalarHOL (sourceState inputs) expression).bind sourceRuntime := by
  rw [evaluateRuntime_encode, ← translate_correct inputs expression fragment h]
  cases evaluate inputs fragment <;> rfl

end
end Veir.PancakeFrontend
