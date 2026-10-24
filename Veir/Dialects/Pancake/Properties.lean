module

public import Veir.IR.Attribute
public import Flapjack.Pancake.PanLang

namespace Veir
public section

@[expose] def Pancake.binOpName : Flapjack.BinOp → ByteArray
  | .add => "add".toUTF8
  | .sub => "sub".toUTF8
  | .and => "and".toUTF8
  | .or => "or".toUTF8
  | .xor => "xor".toUTF8

@[expose] def Pancake.parseBinOp (name : ByteArray) : Option Flapjack.BinOp :=
  if name = "add".toUTF8 then some .add
  else if name = "sub".toUTF8 then some .sub
  else if name = "and".toUTF8 then some .and
  else if name = "or".toUTF8 then some .or
  else if name = "xor".toUTF8 then some .xor
  else none

@[expose] def Pancake.cmpName : Flapjack.Cmp → ByteArray
  | .equal => "equal".toUTF8
  | .lower => "lower".toUTF8
  | .less => "less".toUTF8
  | .test => "test".toUTF8
  | .notEqual => "notEqual".toUTF8
  | .notLower => "notLower".toUTF8
  | .notLess => "notLess".toUTF8
  | .notTest => "notTest".toUTF8

@[expose] def Pancake.parseCmp (name : ByteArray) : Option Flapjack.Cmp :=
  if name = "equal".toUTF8 then some .equal
  else if name = "lower".toUTF8 then some .lower
  else if name = "less".toUTF8 then some .less
  else if name = "test".toUTF8 then some .test
  else if name = "notEqual".toUTF8 then some .notEqual
  else if name = "notLower".toUTF8 then some .notLower
  else if name = "notLess".toUTF8 then some .notLess
  else if name = "notTest".toUTF8 then some .notTest
  else none

@[simp] theorem Pancake.parseBinOp_name (operator : Flapjack.BinOp) :
    parseBinOp (binOpName operator) = some operator := by
  cases operator <;> simp [parseBinOp, binOpName, String.toByteArray_inj]

@[simp] theorem Pancake.parseCmp_name (operator : Flapjack.Cmp) :
    parseCmp (cmpName operator) = some operator := by
  cases operator <;> simp [parseCmp, cmpName, String.toByteArray_inj]

structure PancakeConstantProperties where
  value : IntegerAttr
  deriving Inhabited, Repr, Hashable, DecidableEq

structure PancakeBinOpProperties where
  operator : Flapjack.BinOp := .add
  deriving Inhabited, Repr, DecidableEq

structure PancakePanOpProperties where
  operator : Flapjack.PanOp := .mul
  deriving Inhabited, Repr, DecidableEq

structure PancakeCmpProperties where
  operator : Flapjack.Cmp := .equal
  deriving Inhabited, Repr, DecidableEq

instance : Hashable PancakeBinOpProperties where
  hash props := hash (Pancake.binOpName props.operator)
instance : Hashable PancakePanOpProperties where
  hash _ := hash "mul"
instance : Hashable PancakeCmpProperties where
  hash props := hash (Pancake.cmpName props.operator)

private def requiredProperty (dict : Std.HashMap ByteArray Attribute)
    (opName key : String) : Except String Attribute := do
  if dict.size != 1 then throw s!"{opName}: expected only '{key}' property"
  let some value := dict[key.toUTF8]? | throw s!"{opName}: missing '{key}' property"
  return value

private def requiredOperator (dict : Std.HashMap ByteArray Attribute)
    (opName : String) : Except String ByteArray := do
  let .stringAttr value ← requiredProperty dict opName "operator"
    | throw s!"{opName}: expected string 'operator' property"
  return value.value

def PancakeConstantProperties.fromAttrDict (dict : Std.HashMap ByteArray Attribute) :
    Except String PancakeConstantProperties := do
  let .integerAttr value ← requiredProperty dict "pancake.const" "value"
    | throw "pancake.const: expected integer 'value' property"
  return ⟨value⟩

def PancakeBinOpProperties.fromAttrDict (dict : Std.HashMap ByteArray Attribute) :
    Except String PancakeBinOpProperties := do
  let name ← requiredOperator dict "pancake.op"
  let some operator := Pancake.parseBinOp name | throw "pancake.op: unknown operator"
  return ⟨operator⟩

def PancakePanOpProperties.fromAttrDict (dict : Std.HashMap ByteArray Attribute) :
    Except String PancakePanOpProperties := do
  let name ← requiredOperator dict "pancake.panop"
  if name = "mul".toUTF8 then return ⟨.mul⟩ else throw "pancake.panop: unknown operator"

def PancakeCmpProperties.fromAttrDict (dict : Std.HashMap ByteArray Attribute) :
    Except String PancakeCmpProperties := do
  let name ← requiredOperator dict "pancake.cmp"
  let some operator := Pancake.parseCmp name | throw "pancake.cmp: unknown operator"
  return ⟨operator⟩

end
end Veir
