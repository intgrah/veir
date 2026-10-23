module

public import Veir.Frontend.Pancake.Runtime
public import Veir.Parser.MlirParser
public import Veir.Verifier

namespace Veir.PancakeFrontend
public section

/-- Inputs are deduplicated by kind and raw mlstring bytes, in first-use order. -/
@[expose] def Fragment.inputs (fragment : Fragment) : List Variable :=
  let refs := (fragment.code.flatMap Instruction.operands) ++ [fragment.result]
  refs.foldl (fun found ref => match ref with
    | .temp _ => found
    | .input key => if key ∈ found then found else found ++ [key]) []

@[expose] def Ref.name (inputs : List Variable) : Ref → String
  | .temp index => s!"%v{index}"
  | .input key => s!"%arg{inputs.findIdx (fun candidate => decide (candidate = key))}"

@[expose] def Instruction.propertyText (instruction : Instruction) : String :=
  match instruction.operation with
  | .constant value => s!"value = {value.value} : i{value.type.bitwidth}"
  | .binop operator => s!"operator = \"{String.fromUTF8! (PancakeScalar.binOpName operator)}\""
  | .multiply => "operator = \"mul\""
  | .compare operator => s!"operator = \"{String.fromUTF8! (PancakeScalar.cmpName operator)}\""

/-- A standalone `func.func @main`; its arguments follow `inputs` in order. -/
structure Emitted where
  inputs : List Variable
  text : String

/-- Text serialization is tested through VeIR's parser/verifier, outside the semantic theorem. -/
@[expose] def emit (width : Nat) (fragment : Fragment) : Emitted := Id.run do
  let inputs := fragment.inputs
  let ty := s!"i{width}"
  let types := String.intercalate ", " (inputs.map fun _ => ty)
  let args := String.intercalate ", " (inputs.zipIdx.map fun (_, index) => s!"%arg{index}: {ty}")
  let mut text := s!"\"func.func\"() <\{sym_name = \"main\", function_type = ({types}) -> {ty}}> (\{\n^entry({args}):\n"
  for (instruction, index) in fragment.code.zipIdx do
    let name := String.fromUTF8! (Pancake.name instruction.opType)
    let operands := String.intercalate ", " (instruction.operands.map (Ref.name inputs))
    let operandTypes := String.intercalate ", " (instruction.operands.map fun _ => ty)
    text := text ++ s!"  %v{index} = \"{name}\"({operands}) <\{{instruction.propertyText}}> : ({operandTypes}) -> {ty}\n"
  text := text ++ s!"  \"func.return\"({fragment.result.name inputs}) : ({ty}) -> ()\n}) : () -> ()\n"
  return ⟨inputs, text⟩

/-- The entry point consumes Flapjack's exact AST, not Pancake source text. -/
@[expose] def toMLIR {width : Nat} [NeZero width]
    (expression : PancakeSource.ExpHOL width) : Except String Emitted := do
  let some fragment := translate expression
    | throw "unsupported Pancake expression or invalid scalar operator arity"
  return emit width fragment

structure Parsed where
  inputs : List Variable
  context : WfIRContext OpCode
  function : OperationPtr

/-- Compile, parse, and verify a scalar expression as a standalone VeIR function. -/
def toIR {width : Nat} [NeZero width]
    (expression : PancakeSource.ExpHOL width) : Except String Parsed := do
  let emitted ← toMLIR expression
  let some (context, _) := WfIRContext.create OpCode
    | throw "could not create VeIR context"
  let parser ← (Parser.ParserState.fromInput emitted.text.toUTF8).mapError toString
  let (function, state, _) ←
    (Parser.parseTopLevelOp.run (Parser.MlirParserState.fromContext context) parser).mapError toString
  state.ctx.verify function
  return ⟨emitted.inputs, state.ctx, function⟩

end
end Veir.PancakeFrontend
