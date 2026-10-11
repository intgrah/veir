module

public import Veir.Parser.BuffedIR

/-!
# Generic-form printer for parsed IR

Prints a buffered IR context in MLIR's generic operation form. Values and blocks are named by
their buffer address, so the output round-trips through the parser. The printer only reads the
buffer (through the `!` accessors), so it needs no proofs.
-/

public section

namespace Veir.Parser.PrintIR

open Veir
open Veir.Buffed

/-- An unused name, so block-argument names stay distinct from result names. -/
private def valueName (value : ValueImplMPtr) : String := s!"%v{value}"

private def blockName (block : BlockMPtr) : String := s!"^b{block}"

private def indent (n : Nat) : String := String.ofList (List.replicate (2 * n) ' ')

/-- The type of the value at the given address. -/
private def valueType (buf : IRBufContext) (value : ValueImplMPtr) : Attribute :=
  buf.attributes[(ValueImplMPtr.readType! buf value).toNat]!

/-- Print the properties of an operation, if any. -/
private def propertiesString (buf : IRBufContext) (op : OperationMPtr) : String :=
  let opType : OpCode := SerializableOpInfo.decode (OperationMPtr.readOpType! buf op)
  match HasBuffedProperties.readPropertyAt opType (op + Operation.Offsets.properties) buf with
  | none => ""
  | some props =>
    let dict := Properties.toAttrDict opType props
    if dict.isEmpty then "" else s!" <{DictionaryAttr.fromArray dict.toArray}>"

private def opNameString (buf : IRBufContext) (op : OperationMPtr) : String :=
  let opType : OpCode := SerializableOpInfo.decode (OperationMPtr.readOpType! buf op)
  match opType with
  | .builtin .unregistered =>
    match (HasBuffedProperties.readPropertyAt (OpCode.builtin .unregistered) (op + Operation.Offsets.properties) buf : Option UnregisteredProperties) with
    | some props => String.fromUTF8! props.opName
    | none => "builtin.unregistered"
  | _ => String.fromUTF8! opType.name

mutual

partial def printOp (ctx : IR.Ctx) (op : OperationMPtr) (depth : Nat) : IO Unit := do
  let buf := ctx.buf
  let mut line := indent depth
  let numResults := OperationMPtr.readNumResults! buf op
  let results := (List.range numResults.toNat).map fun i =>
    op + OperationMPtr.computeResultOffset! buf op i.toUInt64
  if numResults ≠ 0 then
    line := line ++ String.intercalate ", " (results.map valueName) ++ " = "
  line := line ++ s!"\"{opNameString buf op}\""
  let numOperands := OperationMPtr.readNumOperands! buf op
  let operands := (List.range numOperands.toNat).map fun i =>
    OpOperandMPtr.readValue! buf (op + OperationMPtr.computeOperandOffset! (OpInfo := OpCode) buf op i.toUInt64)
  line := line ++ "(" ++ String.intercalate ", " (operands.map valueName) ++ ")"
  let numSuccessors := OperationMPtr.readNumBlockOperands! buf op
  if numSuccessors ≠ 0 then
    let successors := (List.range numSuccessors.toNat).map fun i =>
      blockName (BlockOperandMPtr.readValue! buf (op + OperationMPtr.computeBlockOperandOffset! (OpInfo := OpCode) buf op i.toUInt64))
    line := line ++ " [" ++ String.intercalate ", " successors ++ "]"
  line := line ++ propertiesString buf op
  let numRegions := OperationMPtr.readNumRegions! buf op
  if numRegions ≠ 0 then
    IO.print (line ++ " (")
    for i in [0:numRegions.toNat] do
      if i ≠ 0 then IO.print ", "
      printRegion ctx (OperationMPtr.readNthRegion! (OpInfo := OpCode) buf op i.toUInt64) depth
    IO.print ")"
    line := ""
  let attrs := Sim.OperationPtr.getAttributes! ctx ⟨op, ⟨op.toNat⟩⟩
  if !attrs.entries.isEmpty then
    line := line ++ s!" {attrs}"
  let operandTypes := operands.map fun v => toString (valueType buf v)
  let resultTypes := results.map fun v => toString (valueType buf v)
  let resultsString := match resultTypes with
    | [ty] => ty
    | tys => "(" ++ String.intercalate ", " tys ++ ")"
  line := line ++ s!" : ({String.intercalate ", " operandTypes}) -> {resultsString}"
  IO.println line

partial def printBlock (ctx : IR.Ctx) (block : BlockMPtr) (depth : Nat) : IO Unit := do
  let buf := ctx.buf
  let numArgs := BlockMPtr.readNumArguments! buf block
  let args := (List.range numArgs.toNat).map fun i =>
    let value := block + BlockMPtr.computeArgumentOffset! i.toUInt64
    s!"{valueName value} : {valueType buf value}"
  IO.println s!"{indent depth}{blockName block}({String.intercalate ", " args}):"
  let mut op := BlockMPtr.readFirstOp! buf block
  while op ≠ OperationOPtr.none do
    printOp ctx op (depth + 1)
    op := OperationMPtr.readNext! buf op

partial def printRegion (ctx : IR.Ctx) (region : RegionMPtr) (depth : Nat) : IO Unit := do
  let buf := ctx.buf
  IO.println "{"
  let mut block := RegionMPtr.readFirstBlock! buf region
  while block ≠ BlockOPtr.none do
    printBlock ctx block (depth + 1)
    block := BlockMPtr.readNext! buf block
  IO.print s!"{indent depth}}"

end

/-- Print the operation `op` and everything nested inside it. -/
def printModule (ctx : IR.Ctx) (op : IR.Op) : IO Unit :=
  printOp ctx op.toM 0

end Veir.Parser.PrintIR

end
