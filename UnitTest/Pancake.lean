module

import Veir.GlobalOpInfo
meta import Veir.GlobalOpInfo

open Veir

example : HasDialect OpCode Pancake := inferInstance

/- Every source constructor is registered, including escaped Lean keywords. -/
private def operationNames : Array String := #[
  "const", "var", "rstruct", "rfield", "nstruct", "nfield", "load", "load32",
  "load_byte", "op", "panop", "cmp", "shift", "base_addr", "top_addr", "bytes_in_word",
  "skip", "dec", "assign", "primitive", "store", "store32", "store_byte", "seq",
  "ite", "while", "break", "continue", "call", "dec_call", "ext_call", "raise",
  "return", "sh_mem_load", "sh_mem_store", "tick", "annot",
  "function", "decl", "exn_decl", "name_decl"
]

#guard operationNames.all fun mnemonic => Id.run do
  let name := s!"pancake.{mnemonic}".toUTF8
  let some opType := Pancake.fromName name | return false
  return Pancake.name opType == name &&
    OpCode.fromName name == some (.pancake opType) &&
    OpCode.name (.pancake opType) == name

#guard Pancake.fromName "pancake.unknown".toUTF8 == none
#guard Pancake.fromName "test.test".toUTF8 == none

/- Raw bytes, nested shapes, ordering, and extension metadata survive serialization. -/
private def byteName : Attribute := .stringAttr { value := ⟨#[0, 128, 255]⟩ }

private def shape : Attribute := .arrayAttr { value := #[
  .integerAttr (IntegerAttr.mk 1 (.signless 64)), byteName,
  .arrayAttr { value := #[] }
] }

private def metadata : Std.HashMap ByteArray Attribute := Std.HashMap.ofList [
  ("struct".toUTF8, byteName),
  ("fields".toUTF8, .arrayAttr { value := #[
    .arrayAttr { value := #[byteName, shape] },
    .arrayAttr { value := #[byteName, shape] }
  ] }),
  ("future_property".toUTF8, .unitAttr {})
]

#guard Id.run do
  let .ok props := Properties.fromAttrDict (.pancake .name_decl) metadata | return false
  let restored := Properties.toAttrDict (.pancake .name_decl) props
  return restored.size == metadata.size &&
    metadata.toArray.all fun (key, value) => restored[key]? == some value

private def property (key : String) (value : Attribute) : Std.HashMap ByteArray Attribute :=
  Std.HashMap.ofList [(key.toUTF8, value)]

#guard (Pancake.fromAttrDict .load (property "shape" shape)).isOk
#guard !((Pancake.fromAttrDict .load (property "shape" (.integerAttr (IntegerAttr.mk 2 (.signless 64))))).isOk)
#guard (Pancake.fromAttrDict .const (property "value" (.integerAttr (IntegerAttr.mk 7 (.signless 32))))).isOk
#guard !((Pancake.fromAttrDict .const (property "value" (.integerAttr (IntegerAttr.mk 0 (.signless 0))))).isOk)
#guard !((Pancake.fromAttrDict .const {}).isOk)
#guard !((Pancake.fromAttrDict .rfield (property "index" (.integerAttr (IntegerAttr.mk (-1) (.signless 64))))).isOk)
#guard (Pancake.fromAttrDict .cmp (property "operator" (.stringAttr { value := "notLower".toUTF8 }))).isOk
#guard !((Pancake.fromAttrDict .cmp (property "operator" (.stringAttr { value := "unsigned_lt".toUTF8 }))).isOk)

/- The outer option distinguishes tail calls from ordinary calls with no destination. -/
private def returningInfo : Attribute := .dictionaryAttr (DictionaryAttr.fromArray #[
  ("destination".toUTF8, .unitAttr {}), ("handler".toUTF8, .unitAttr {})
])

private def callProperties (info : Attribute) : Std.HashMap ByteArray Attribute :=
  Std.HashMap.ofList [("name".toUTF8, byteName), ("info".toUTF8, info)]

#guard (Pancake.fromAttrDict .call (callProperties (.unitAttr {}))).isOk
#guard (Pancake.fromAttrDict .call (callProperties returningInfo)).isOk
#guard Id.run do
  let .ok tailProps := Pancake.fromAttrDict .call (callProperties (.unitAttr {})) | return false
  let .ok returningProps := Pancake.fromAttrDict .call (callProperties returningInfo) | return false
  return (Pancake.toAttrDict .call tailProps)["info".toUTF8]? !=
    (Pancake.toAttrDict .call returningProps)["info".toUTF8]?
#guard !((Pancake.fromAttrDict .call (callProperties (.dictionaryAttr DictionaryAttr.empty))).isOk)

/- Effects remain conservative while stateful execution semantics are incomplete. -/
#guard OpCode.getEffects (.pancake .load) DictionaryAttr.empty == .unknown
#guard OpCode.getEffects (.pancake .call) DictionaryAttr.empty == .unknown
#guard !OpCode.isConstantLike (.pancake .const)
#guard OpCode.hasSSADominance (.pancake .function) 0
#guard OpCode.getRegionKind (.pancake .function) 0 == .SSACFG
#guard OpCode.hasNoTerminator (.pancake .ite) 0
#guard OpCode.isTerminator (.pancake .«return»)
#guard OpCode.isTerminator (.pancake .«break»)
#guard !OpCode.isTerminator (.pancake .call)
