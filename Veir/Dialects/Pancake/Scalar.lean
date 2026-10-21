module

public import Veir.Dialects.Pancake.Flapjack
public import Veir.Interpreter.RuntimeValue.Basic
import all Veir.IR.Attribute

namespace Veir.PancakeScalar

public section

/-!
The scalar boundary uses positive-width, signless integer types. A Pancake
word is represented by `RuntimeValue.int width (.val bits)`; poison, pointers,
and values of other widths are rejected. Comparison results are words of the
operand width containing zero or one, not MLIR-style `i1` results.
-/

@[expose]
def encodeWord (value : BitVec width) : RuntimeValue := .int width (.val value)

@[expose]
def decodeWord (width : Nat) : RuntimeValue → Option (BitVec width)
  | .int actual (.val value) =>
    if h : actual = width then some (h ▸ value) else none
  | _ => none

@[simp] theorem decodeWord_encodeWord (value : BitVec width) :
    decodeWord width (encodeWord value) = some value := by
  simp [encodeWord, decodeWord]

theorem encodeWord_injective : Function.Injective (encodeWord (width := width)) := by
  intro a b h
  have := congrArg (decodeWord width) h
  simpa using this

@[simp] theorem decodeWord_poison :
    decodeWord width (.int otherWidth .poison) = none := rfl

@[expose]
def binOpName : PancakeSource.BinOp → ByteArray
  | .add => "add".toUTF8
  | .sub => "sub".toUTF8
  | .and => "and".toUTF8
  | .or => "or".toUTF8
  | .xor => "xor".toUTF8

@[expose]
def parseBinOp (name : ByteArray) : Option PancakeSource.BinOp :=
  if name = "add".toUTF8 then some .add
  else if name = "sub".toUTF8 then some .sub
  else if name = "and".toUTF8 then some .and
  else if name = "or".toUTF8 then some .or
  else if name = "xor".toUTF8 then some .xor
  else none

@[expose]
def cmpName : PancakeSource.Cmp → ByteArray
  | .equal => "equal".toUTF8
  | .lower => "lower".toUTF8
  | .less => "less".toUTF8
  | .test => "test".toUTF8
  | .notEqual => "notEqual".toUTF8
  | .notLower => "notLower".toUTF8
  | .notLess => "notLess".toUTF8
  | .notTest => "notTest".toUTF8

@[expose]
def parseCmp (name : ByteArray) : Option PancakeSource.Cmp :=
  if name = "equal".toUTF8 then some .equal
  else if name = "lower".toUTF8 then some .lower
  else if name = "less".toUTF8 then some .less
  else if name = "test".toUTF8 then some .test
  else if name = "notEqual".toUTF8 then some .notEqual
  else if name = "notLower".toUTF8 then some .notLower
  else if name = "notLess".toUTF8 then some .notLess
  else if name = "notTest".toUTF8 then some .notTest
  else none

@[simp] theorem parseBinOp_name (operator : PancakeSource.BinOp) :
    parseBinOp (binOpName operator) = some operator := by
  cases operator <;> simp [parseBinOp, binOpName, String.toByteArray_inj]

@[simp] theorem parseCmp_name (operator : PancakeSource.Cmp) :
    parseCmp (cmpName operator) = some operator := by
  cases operator <;> simp [parseCmp, cmpName, String.toByteArray_inj]

inductive Operation where
  | constant (value : IntegerAttr)
  | binop (operator : PancakeSource.BinOp)
  | multiply
  | compare (operator : PancakeSource.Cmp)

/-- Dispatch to Flapjack's source definitions, without introducing poison or UB. -/
@[expose]
def evaluate {width : Nat} [NeZero width] (operation : Operation)
    (operands : List (BitVec width)) : Option (BitVec width) :=
  match operation with
  | .constant value =>
    if operands.isEmpty && value.type == IntegerType.signless width then
      some (BitVec.ofInt width value.value)
    else none
  | .binop operator => PancakeSource.wordOpHOL operator operands
  | .multiply => PancakeSource.panOpHOL .mul operands
  | .compare operator =>
    match operands with
    | [left, right] => some (PancakeSource.Compiler.Encoders.Asm.wordCmpResultHOL operator left right)
    | _ => none

@[expose]
def interpret (operation : Operation) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) : Option (Array RuntimeValue) := do
  let [resultType] := resultTypes.toList | none
  let .integerType intType := resultType.val | none
  if intType.signedness != .signless then none else do
    if h : intType.bitwidth = 0 then none else do
      let _ : NeZero intType.bitwidth := ⟨h⟩
      let words ← operands.toList.mapM (decodeWord intType.bitwidth)
      let result ← evaluate operation words
      return #[encodeWord result]

@[simp] theorem decodeWords_encodeWords (values : List (BitVec width)) :
    (values.map encodeWord).mapM (decodeWord width) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [List.mapM_cons, ih]

/-- Marshalling is lossless for every positive width and every operand list. -/
theorem interpret_encoded {width : Nat} [NeZero width] (operation : Operation)
    (values : List (BitVec width)) :
    interpret operation #[TypeAttr.of IntegerType (IntegerType.signless width)] (values.map encodeWord).toArray =
      (evaluate operation values).map (fun value => #[encodeWord value]) := by
  simp only [interpret, TypeAttr.of_val]
  change (if (IntegerType.signless width).signedness != .signless then none else _) = _
  simp only [IntegerType.signless, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    NeZero.ne width, decodeWords_encodeWords]
  simp only [↓reduceDIte]
  cases h : evaluate operation values <;> simp [h]

end

end Veir.PancakeScalar
