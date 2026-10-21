module

public import Veir.IR.OpInfo
public import Veir.Dialects.Pancake.Properties
public import Veir.Verifier.Basic
meta import Veir.Meta.OpCode

namespace Veir

public section

/-!
Syntax-level definitions following Flapjack's `ExpHOL`, `ProgHOL`, and `DeclHOL`:
https://github.com/flamingoponderado/flapjack/tree/65fb1aa2d846adc590677994ccf92821fc9781e7/Flapjack/Pancake/PanLang

Constructor names use snake_case in the textual dialect (`ite` stays `ite`).
Names, shapes, operator selectors, and call metadata are validated and preserved
as properties. Recursive expression/program children belong to the IR rather
than the property dictionary. These definitions do not implement a translation
from Flapjack, Pancake's type checking, evaluation, or lowering, and do not claim
that expressions are safe to discard or speculate.
-/

@[opcodes]
inductive Pancake where
-- Expressions (`ExpHOL`).
| const
| var
| rstruct
| rfield
| nstruct
| nfield
| load
| load32
| load_byte
| op
| panop
| cmp
| shift
| base_addr
| top_addr
| bytes_in_word
-- Statements (`ProgHOL`).
| skip
| dec
| assign
| primitive
| store
| store32
| store_byte
| seq
| ite
| «while»
| «break»
| «continue»
| call
| dec_call
| ext_call
| raise
| «return»
| sh_mem_load
| sh_mem_store
| tick
| annot
-- Top-level declarations (`DeclHOL`).
| function
| decl
| exn_decl
/-- `DeclHOL.name`; avoid the generated `Pancake.name` lookup function. -/
| name_decl
deriving Inhabited, Repr, Hashable, DecidableEq

#generate_dialect Pancake

/-- Nonrecursive constructor fields; child expressions/programs are represented in the IR. -/
def Pancake.propertySchema (opType : Pancake) : List (String × PancakePropertyKind) :=
  open PancakePropertyKind in
  match opType with
  | .const => [("value", .word)]
  | .var | .assign => [("kind", varKind), ("name", .bytes)]
  | .rfield => [("index", .natural)]
  | .nstruct => [("name", .bytes), ("fields", .array .bytes)]
  | .nfield => [("name", .bytes)]
  | .load => [("shape", .shape)]
  | .op => [("operator", .choice #["add", "sub", "and", "or", "xor"])]
  | .panop => [("operator", .choice #["mul"])]
  | .cmp => [("operator", .choice #["equal", "lower", "less", "test",
      "notEqual", "notLower", "notLess", "notTest"])]
  | .shift => [("operator", .choice #["lsl", "lsr", "asr", "ror"])]
  | .dec | .decl => [("name", .bytes), ("shape", .shape)]
  | .primitive => [("name", .bytes), ("operator", .choice #["addCarry"])]
  | .call => [("name", .bytes), ("info", callInfo)]
  | .dec_call => [("name", .bytes), ("shape", .shape), ("function", .bytes)]
  | .ext_call => [("function", .bytes)]
  | .raise => [("exception", .bytes)]
  | .sh_mem_load => [("size", opSize), ("kind", varKind), ("name", .bytes)]
  | .sh_mem_store => [("size", opSize)]
  | .annot => [("tag", .bytes), ("text", .bytes)]
  | .function => [("name", .bytes), ("inline", .boolean), ("exported", .boolean),
      ("params", namedShapes), ("return_shape", .shape)]
  | .exn_decl => [("exception", .bytes), ("shape", .shape)]
  | .name_decl => [("struct", .bytes), ("fields", namedShapes)]
  | .rstruct | .load32 | .load_byte | .base_addr | .top_addr | .bytes_in_word
  | .skip | .store | .store32 | .store_byte | .seq | .ite | .«while»
  | .«break» | .«continue» | .«return» | .tick => []

/-- Preserve source metadata, including properties not yet interpreted by VeIR. -/
@[expose, properties_of]
def Pancake.propertiesOf (_op : Pancake) : Type :=
  DictionaryAttr

def Pancake.fromAttrDict
    (opType : Pancake) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Pancake.propertiesOf opType) := do
  let props := DictionaryAttr.fromArray attrDict.toArray
  match PancakePropertyKind.verify (.record (Pancake.propertySchema opType)) (.dictionaryAttr props) with
  | .ok () => return props
  | .error error => throw s!"{String.fromUTF8! (Pancake.name opType)}: {error}"

def Pancake.toAttrDict
    (_op : Pancake) (props : Pancake.propertiesOf _op) :
    Std.HashMap ByteArray Attribute :=
  Std.HashMap.ofList props.entries.toList

/-- Remain conservative until Pancake's execution semantics are implemented. -/
@[get_effects]
def Pancake.getEffects
    (_op : Pancake) (_props : Pancake.propertiesOf _op) : MemoryEffects :=
  .unknown

def Pancake.isConstantLike (_op : Pancake) : Bool :=
  false

/-- Expression SSA values must be defined before use, even with named mutable variables. -/
def Pancake.hasSSADominance (_op : Pancake) (_index : Nat) : Bool :=
  true

/-- Structured source bodies can fall through without an explicit block terminator. -/
def Pancake.hasNoTerminator (opType : Pancake) (_index : Nat) : Bool :=
  match opType with
  | .dec | .seq | .ite | .«while» | .call | .dec_call | .function | .decl => true
  | _ => false

@[is_terminator]
def Pancake.isTerminator (opType : Pancake) : Bool :=
  match opType with
  | .«break» | .«continue» | .raise | .«return» => true
  | _ => false

instance : IsOpCode Pancake where
  fromName := Pancake.fromName
  name := Pancake.name
  propertiesOf := Pancake.propertiesOf
  fromAttrDict := Pancake.fromAttrDict
  toAttrDict := Pancake.toAttrDict

/-- Also check properties of operations created directly through the rewriter. -/
@[expose]
def Pancake.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Pancake] (opType : Pancake) (operation : OperationPtr)
    (ctx : WfIRContext OpInfo) (_opIn : operation.InBounds ctx.raw) : Except String PUnit := do
  let props : Pancake.propertiesOf opType := operation.getProperties! ctx.raw opType
  let _ ← Pancake.fromAttrDict opType (Pancake.toAttrDict opType props)

instance : HasOpInfo Pancake where
  verifyLocalInvariants := Pancake.verifyLocalInvariants
  getEffects := Pancake.getEffects
  isConstantLike := Pancake.isConstantLike
  hasSSADominance := Pancake.hasSSADominance
  hasNoTerminator := Pancake.hasNoTerminator
  isTerminator := Pancake.isTerminator

end

end Veir
