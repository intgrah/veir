module

public import Veir.IR.Attribute

namespace Veir

public section

/-!
Property encodings for Flapjack's `ExpHOL`, `ProgHOL`, and `DeclHOL`, inspected at
commit 65fb1aa2d846adc590677994ccf92821fc9781e7:
https://github.com/flamingoponderado/flapjack/tree/65fb1aa2d846adc590677994ccf92821fc9781e7/Flapjack/Pancake/PanLang

Names use `StringAttr`'s raw bytes, matching the byte-string carrier of `MlS`;
they are never decoded as UTF-8. A word is a nonzero-width integer attribute.
Shapes encode `one` as integer 1, `comb` as an array of shapes, and `named` as
a byte string. Lists of named fields/parameters use arrays of `[name, shape]`
pairs, preserving order and duplicate names. Operator selectors use Flapjack's
Lean constructor names.

An option is a unit attribute for `none`, or its payload for `some`. Thus call
`info = unit` is a tail call, while `info = {destination = unit, handler = unit}`
is a returning call without a destination or handler. Handler program bodies
are regions, separate from the handler's exception and variable-name metadata.
-/

/-- The attribute schema for a nonrecursive payload of a Flapjack constructor. -/
inductive PancakePropertyKind where
| bytes
| word
| natural
| boolean
| shape
| choice (values : Array String)
| array (element : PancakePropertyKind)
| pair (first second : PancakePropertyKind)
| record (fields : List (String × PancakePropertyKind))
| optional (element : PancakePropertyKind)

namespace PancakePropertyKind

/-- Validate payloads without changing their byte strings or attribute representation. -/
partial def verify (kind : PancakePropertyKind) (attr : Attribute) : Except String Unit := do
  match kind, attr with
  | .bytes, .stringAttr _ => pure ()
  | .word, .integerAttr value =>
    if value.type.bitwidth == 0 then throw "expected a nonzero-width word"
  | .natural, .integerAttr value =>
    if value.type.bitwidth == 0 || value.value < 0 then
      throw "expected a nonnegative integer"
  | .boolean, .integerAttr value =>
    if value.type != IntegerType.signless 1 || (value.value != 0 && value.value != 1) then
      throw "expected an i1 boolean"
  | .shape, .integerAttr value =>
    if value.type.bitwidth == 0 || value.value != 1 then
      throw "expected shape one (integer 1), an array of shapes, or a named shape string"
  | .shape, .stringAttr _ => pure ()
  | .shape, .arrayAttr fields =>
    for field in fields.value do verify .shape field
  | .choice values, .stringAttr value =>
    if !values.any (fun candidate => candidate.toUTF8 == value.value) then
      throw s!"expected one of {values.toList}"
  | .array element, .arrayAttr values =>
    for value in values.value do verify element value
  | .pair first second, .arrayAttr values =>
    if values.value.size != 2 then throw "expected a two-element array"
    verify first values.value[0]!
    verify second values.value[1]!
  | .record fields, .dictionaryAttr values =>
    let dict := Std.HashMap.ofList values.entries.toList
    for (name, fieldKind) in fields do
      let some value := dict[name.toUTF8]? | throw s!"missing '{name}'"
      match verify fieldKind value with
      | .ok () => pure ()
      | .error error => throw s!"'{name}': {error}"
  | .optional _, .unitAttr _ => pure ()
  | .optional element, value => verify element value
  | .bytes, _ => throw "expected a byte string"
  | .word, _ => throw "expected an integer word attribute"
  | .natural, _ => throw "expected a nonnegative integer"
  | .boolean, _ => throw "expected an i1 boolean"
  | .shape, _ => throw "expected shape one (integer 1), an array of shapes, or a named shape string"
  | .choice _, _ => throw "expected an operator string"
  | .array _, _ => throw "expected an array"
  | .pair _ _, _ => throw "expected a two-element array"
  | .record _, _ => throw "expected a dictionary"

def varKind : PancakePropertyKind := .choice #["local", "global"]

def opSize : PancakePropertyKind := .choice #["op8", "opW", "op32", "op16"]

def namedShapes : PancakePropertyKind := .array (.pair .bytes .shape)

def callInfo : PancakePropertyKind :=
  .optional (.record [
    ("destination", .optional (.record [("kind", varKind), ("name", .bytes)])),
    ("handler", .optional (.record [("exception", .bytes), ("name", .bytes)]))
  ])

end PancakePropertyKind

end

end Veir
