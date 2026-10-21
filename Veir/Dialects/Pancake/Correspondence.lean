module

public import Veir.Dialects.Pancake.Interpreter
import all Veir.Dialects.Pancake.Scalar
import all Veir.IR.Attribute

namespace Veir.Pancake

public section

/-!
Operation-level correspondence to the pinned Flapjack word semantics. These
lemmas cover the actual property decoder and runtime-value adapter used by
VeIR's interpreter, at every positive word width. They are not a theorem about
a source frontend, a whole program, or Pancake's stateful operations.
-/

@[expose]
def operatorProperties (name : ByteArray) : DictionaryAttr :=
  { entries := #[("operator".toUTF8, .stringAttr { value := name })] }

@[expose]
def constantProperties (value : IntegerAttr) : DictionaryAttr :=
  { entries := #[("value".toUTF8, .integerAttr value)] }

@[simp] theorem scalarOperation_binop (operator : PancakeSource.BinOp) :
    scalarOperation? .op (operatorProperties (PancakeScalar.binOpName operator)) =
      some (.binop operator) := by
  simp only [scalarOperation?, property?, operatorProperties, Array.findSome?_singleton,
    ↓reduceIte, PancakeScalar.parseBinOp_name]
  rfl

@[simp] theorem scalarOperation_cmp (operator : PancakeSource.Cmp) :
    scalarOperation? .cmp (operatorProperties (PancakeScalar.cmpName operator)) =
      some (.compare operator) := by
  simp only [scalarOperation?, property?, operatorProperties, Array.findSome?_singleton,
    ↓reduceIte, PancakeScalar.parseCmp_name]
  rfl

@[simp] theorem scalarOperation_const (value : IntegerAttr) :
    scalarOperation? .const (constantProperties value) = some (.constant value) := by
  simp only [scalarOperation?, property?, constantProperties, Array.findSome?_singleton, ↓reduceIte]
  rfl

@[simp] theorem scalarOperation_mul :
    scalarOperation? .panop (operatorProperties "mul".toUTF8) = some .multiply := by
  simp only [scalarOperation?, property?, operatorProperties, Array.findSome?_singleton,
    ↓reduceIte]

/-- This covers empty and variadic lists as well as subtraction's arity failures. -/
theorem interpret_binop_eq_flapjack {width : Nat} [NeZero width]
    (operator : PancakeSource.BinOp) (values : List (BitVec width)) :
    interpretScalar .op (operatorProperties (PancakeScalar.binOpName operator))
      #[TypeAttr.of IntegerType (.signless width)] (values.map PancakeScalar.encodeWord).toArray =
      (PancakeSource.wordOpHOL operator values).map (fun value => #[PancakeScalar.encodeWord value]) := by
  simp only [interpretScalar, scalarOperation_binop]
  exact PancakeScalar.interpret_encoded (.binop operator) values

theorem interpret_mul_eq_flapjack {width : Nat} [NeZero width]
    (values : List (BitVec width)) :
    interpretScalar .panop (operatorProperties "mul".toUTF8)
      #[TypeAttr.of IntegerType (.signless width)] (values.map PancakeScalar.encodeWord).toArray =
      (PancakeSource.panOpHOL .mul values).map (fun value => #[PancakeScalar.encodeWord value]) := by
  simp only [interpretScalar, scalarOperation_mul]
  exact PancakeScalar.interpret_encoded .multiply values

/-- Signed, unsigned, and bit-test comparisons all return a word containing 0 or 1. -/
theorem interpret_cmp_eq_flapjack {width : Nat} [NeZero width]
    (operator : PancakeSource.Cmp) (left right : BitVec width) :
    interpretScalar .cmp (operatorProperties (PancakeScalar.cmpName operator))
      #[TypeAttr.of IntegerType (.signless width)]
      #[PancakeScalar.encodeWord left, PancakeScalar.encodeWord right] =
      some #[PancakeScalar.encodeWord
        (PancakeSource.Compiler.Encoders.Asm.wordCmpResultHOL operator left right)] := by
  simpa [interpretScalar, PancakeScalar.evaluate] using
    PancakeScalar.interpret_encoded (.compare operator) [left, right]

/-- Integer attributes encode precisely the source word's bits, including negative literals. -/
theorem interpret_const_eq_word {width : Nat} [NeZero width] (value : Int) :
    interpretScalar .const (constantProperties ⟨value, .signless width⟩)
      #[TypeAttr.of IntegerType (.signless width)] #[] =
      some #[PancakeScalar.encodeWord (BitVec.ofInt width value)] := by
  simpa [interpretScalar, PancakeScalar.evaluate] using
    PancakeScalar.interpret_encoded (width := width) (.constant ⟨value, .signless width⟩) []

/-- The interpreter wrapper preserves memory and returns no control-flow action. -/
theorem interpretOp_of_scalar (opType : Pancake) (props : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands values : Array RuntimeValue)
    (memory : MemoryState)
    (h : interpretScalar opType props resultTypes operands = some values) :
    interpretOp' opType props resultTypes operands #[] memory = .ok (values, memory, none) := by
  simp [interpretOp', h]

end

end Veir.Pancake
