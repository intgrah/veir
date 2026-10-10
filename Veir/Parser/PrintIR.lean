module

public import Veir.Parser.BuffedIR

/-!
# Generic-form printer for parsed IR

Prints a buffered IR context in MLIR's generic operation form. Values and blocks are named by
their buffer address, so the output round-trips through the parser.
-/

public section

namespace Veir.Parser.PrintIR

open Veir
open Veir.Buffed

/-- An unused name, so block-argument names stay distinct from result names. -/
private def valueName (value : IR.Value) : String := s!"%v{value}"

private def blockName (block : IR.Block) : String := s!"^b{block}"

private def indent (n : Nat) : String := String.ofList (List.replicate (2 * n) ' ')

/-- Print the properties of an operation, if any. -/
private def propertiesString (ctx : IRBufContext) (op : IR.Op) : String :=
  let opType : OpCode := SerializableOpInfo.decode (OperationMPtr.readOpType! ctx op)
  match HasBuffedProperties.readPropertyAt opType (op + Operation.Offsets.properties) ctx with
  | none => ""
  | some props =>
    let dict := Properties.toAttrDict opType props
    if dict.isEmpty then "" else s!" <{DictionaryAttr.fromArray dict.toArray}>"

private def opNameString (ctx : IRBufContext) (op : IR.Op) : String :=
  let opType : OpCode := SerializableOpInfo.decode (OperationMPtr.readOpType! ctx op)
  match opType with
  | .builtin .unregistered =>
    match (HasBuffedProperties.readPropertyAt (OpCode.builtin .unregistered) (op + Operation.Offsets.properties) ctx : Option UnregisteredProperties) with
    | some props => String.fromUTF8! props.opName
    | none => "builtin.unregistered"
  | _ => String.fromUTF8! opType.name

mutual

partial def printOp (ctx : IRBufContext) (op : IR.Op) (depth : Nat) : IO Unit := do
  let mut line := indent depth
  let numResults := OperationMPtr.readNumResults! ctx op
  if numResults ≠ 0 then
    let results := (List.range numResults.toNat).map fun i => valueName (IR.opResult ctx op i.toUInt64)
    line := line ++ String.intercalate ", " results ++ " = "
  line := line ++ s!"\"{opNameString ctx op}\""
  let numOperands := OperationMPtr.readNumOperands! ctx op
  let operands := (List.range numOperands.toNat).map fun i =>
    OpOperandMPtr.readValue! ctx (op + OperationMPtr.computeOperandOffset! (OpInfo := OpCode) ctx op i.toUInt64)
  line := line ++ "(" ++ String.intercalate ", " (operands.map valueName) ++ ")"
  let numSuccessors := OperationMPtr.readNumBlockOperands! ctx op
  if numSuccessors ≠ 0 then
    let successors := (List.range numSuccessors.toNat).map fun i =>
      blockName (BlockOperandMPtr.readValue! ctx (op + OperationMPtr.computeBlockOperandOffset! (OpInfo := OpCode) ctx op i.toUInt64))
    line := line ++ " [" ++ String.intercalate ", " successors ++ "]"
  line := line ++ propertiesString ctx op
  let numRegions := OperationMPtr.readNumRegions! ctx op
  if numRegions ≠ 0 then
    IO.print (line ++ " (")
    for i in [0:numRegions.toNat] do
      if i ≠ 0 then IO.print ", "
      printRegion ctx (OperationMPtr.readNthRegion! (OpInfo := OpCode) ctx op i.toUInt64) depth
    IO.print ")"
    line := ""
  let attrs := Sim.OperationPtr.getAttributes! (IR.toSim ctx) (IR.toSimOp op)
  if !attrs.entries.isEmpty then
    line := line ++ s!" {attrs}"
  let operandTypes := operands.map fun v => toString (IR.valueType ctx v)
  let resultTypes := (List.range numResults.toNat).map fun i =>
    toString (IR.valueType ctx (IR.opResult ctx op i.toUInt64))
  let resultsString := match resultTypes with
    | [ty] => ty
    | tys => "(" ++ String.intercalate ", " tys ++ ")"
  line := line ++ s!" : ({String.intercalate ", " operandTypes}) -> {resultsString}"
  IO.println line

partial def printBlock (ctx : IRBufContext) (block : IR.Block) (depth : Nat) : IO Unit := do
  let numArgs := BlockMPtr.readNumArguments! ctx block
  let args := (List.range numArgs.toNat).map fun i =>
    let value := IR.blockArgument block i.toUInt64
    s!"{valueName value} : {IR.valueType ctx value}"
  IO.println s!"{indent depth}{blockName block}({String.intercalate ", " args}):"
  let mut op := BlockMPtr.readFirstOp! ctx block
  while op ≠ OperationOPtr.none do
    printOp ctx op (depth + 1)
    op := OperationMPtr.readNext! ctx op

partial def printRegion (ctx : IRBufContext) (region : IR.Region) (depth : Nat) : IO Unit := do
  IO.println "{"
  let mut block := RegionMPtr.readFirstBlock! ctx region
  while block ≠ BlockOPtr.none do
    printBlock ctx block (depth + 1)
    block := BlockMPtr.readNext! ctx block
  IO.print s!"{indent depth}}"

end

/-- Print the operation `op` and everything nested inside it. -/
def printModule (ctx : IRBufContext) (op : IR.Op) : IO Unit :=
  printOp ctx op 0

end Veir.Parser.PrintIR

end
