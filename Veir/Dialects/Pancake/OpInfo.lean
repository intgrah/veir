module

public import Veir.IR.OpInfo
public import Veir.Dialects.Pancake.Properties
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode

namespace Veir
public section

/-!
Pancake's scalar operations, using Flapjack's operator types directly.
Words use positive-width signless integers; comparisons return a word of the
same width. Other source expressions and programs are outside this dialect subset.
-/

@[opcodes]
inductive Pancake where
  | const
  | op
  | panop
  | cmp
  deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of] def Pancake.propertiesOf : Pancake → Type
  | .const => PancakeConstantProperties
  | .op => PancakeBinOpProperties
  | .panop => PancakePanOpProperties
  | .cmp => PancakeCmpProperties

def Pancake.fromAttrDict (opType : Pancake) (dict : Std.HashMap ByteArray Attribute) :
    Except String (propertiesOf opType) :=
  match opType with
  | .const => PancakeConstantProperties.fromAttrDict dict
  | .op => PancakeBinOpProperties.fromAttrDict dict
  | .panop => PancakePanOpProperties.fromAttrDict dict
  | .cmp => PancakeCmpProperties.fromAttrDict dict

def Pancake.toAttrDict (opType : Pancake) (props : propertiesOf opType) :
    Std.HashMap ByteArray Attribute :=
  match opType, props with
  | .const, props => Std.HashMap.ofList [("value".toUTF8, .integerAttr props.value)]
  | .op, props => Std.HashMap.ofList [("operator".toUTF8, .stringAttr ⟨binOpName props.operator⟩)]
  | .panop, _ => Std.HashMap.ofList [("operator".toUTF8, .stringAttr ⟨"mul".toUTF8⟩)]
  | .cmp, props => Std.HashMap.ofList [("operator".toUTF8, .stringAttr ⟨cmpName props.operator⟩)]

@[get_effects] def Pancake.getEffects (opType : Pancake) (_ : propertiesOf opType) : MemoryEffects := .none

def Pancake.isConstantLike : Pancake → Bool
  | .const => true
  | _ => false

def Pancake.hasSSADominance (_ : Pancake) (_ : Nat) : Bool := true

#generate_dialect Pancake

instance : IsOpCode Pancake where
  fromName := Pancake.fromName
  name := Pancake.name
  propertiesOf := Pancake.propertiesOf
  fromAttrDict := Pancake.fromAttrDict
  toAttrDict := Pancake.toAttrDict

@[expose] def Pancake.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Pancake] (opType : Pancake) (operation : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : operation.InBounds ctx.raw) : Except String PUnit := do
  let props := operation.getProperties! ctx.raw opType
  let count := match opType, props with
    | .const, _ => 0
    | .op, props => match props.operator with
      | .sub => 2
      | _ => operation.getNumOperands ctx.raw opIn
    | .panop, _ | .cmp, _ => 2
  operation.verifyPlainOpCounts ctx opIn count 1
  let instrName := String.fromUTF8! (Pancake.name opType)
  let resultType := (operation.getResult 0).getType! ctx.raw
  let .integerType wordType := resultType.val
    | throw s!"{instrName}: expected a signless integer result"
  if wordType.bitwidth == 0 || wordType.signedness != .signless then
    throw s!"{instrName}: expected a nonzero-width signless integer result"
  for operandType in operation.getOperandTypes! ctx.raw do
    if operandType.val != resultType.val then
      throw s!"{instrName}: operand types must match the result word type"
  match opType, props with
  | .const, props =>
    if props.value.type != wordType then
      throw s!"{instrName}: constant property type must match the result word type"
  | _, _ => pure ()

instance : HasOpInfo Pancake where
  verifyLocalInvariants := Pancake.verifyLocalInvariants
  getEffects := Pancake.getEffects
  isConstantLike := Pancake.isConstantLike
  hasSSADominance := Pancake.hasSSADominance

end
end Veir
