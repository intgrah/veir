module

public import Veir.Parser.AttrParser
public import Veir.Parser.IRState

/-!
# MLIR generic-form parser

The parser builds the IR directly in the buffered representation through the verified state
operations of `Veir.Parser.IRState`: every pointer it stores is kept in bounds and the context is
kept well-formed by construction, so the parser itself contains no proofs.

Following MLIR, the parser handles values referenced before their definition with placeholder
operations, and blocks referenced before their definition by looking ahead in the enclosing
region for the block's label to learn its argument types.
-/

public section

open Veir.Parser.Lexer
open Veir.Parser
open Veir.AttrParser

namespace Veir.Parser

open Veir.Parser.ParserError

structure MlirParserState where
  /-- The IR context and the tables of pointers, with their invariant. -/
  ir : IRState
  /--
    The values defined in each currently active nested scope.
    Each scope sees all values defined in parent scopes (those that appear earlier in the array).
  -/
  definitionsPerScope : Array (Std.HashSet ByteArray)
  /-- Whether to accept ops/types/attrs from unregistered dialects. -/
  allowUnregisteredDialect : Bool := false
  /-- Type aliases defined so far, keyed by name without the `!`. -/
  typeAliases : Std.HashMap ByteArray TypeAttr := {}
  /-- The location of each parsed operation. -/
  opLocations : Std.HashMap IR.Op Location := {}
  deriving Inhabited

def MlirParserState.initial (allowUnregisteredDialect : Bool := false) : MlirParserState :=
  {
    ir := IRState.initial
    allowUnregisteredDialect
    definitionsPerScope := #[Std.HashSet.emptyWithCapacity 2]
  }

abbrev MlirParserM := StateT MlirParserState (EStateM ParserError ParserState)

/--
  Execute the action with the given initial state.
  Returns the result along with the final state, or an error message.
-/
def MlirParserM.run (self : MlirParserM α)
  (mlirParserState : MlirParserState) (parserState: ParserState) :
    Except ParserError (α × MlirParserState × ParserState) :=
  match (StateT.run self mlirParserState).run parserState with
  | .ok (a, mlirParserState) parserState => .ok (a, mlirParserState, parserState)
  | .error err _ => .error err

/--
  Execute the action with the given initial state.
  Returns the result or an error message.
-/
def MlirParserM.run' (self : MlirParserM α)
  (mlirParserState : MlirParserState) (parserState: ParserState) : Except ParserError α :=
  match self.run mlirParserState parserState with
  | .ok (a, _, _) => .ok a
  | .error err => .error err

/-- Get the IR state, for read-only queries. -/
@[inline]
def getIR : MlirParserM IRState := do
  return (← get).ir

/--
  Modify the IR state.

  The state is taken out of the parser state before `f` runs, so that it is uniquely referenced
  and the IR buffer is updated in place.
-/
@[inline]
def modifyIR' (f : IRState → Except ParserError (α × IRState)) : MlirParserM α := do
  let ir ← modifyGet fun s => (s.ir, { s with ir := IRState.dummy })
  match f ir with
  | .error err => throw err
  | .ok (r, ir) =>
    modify fun s => { s with ir }
    pure r

/-- Modify the IR state (see `modifyIR'`). -/
@[inline]
def modifyIR (f : IRState → Except ParserError IRState) : MlirParserM Unit :=
  modifyIR' fun ir => (f ir).map fun ir => ((), ir)

/--
  Get the original input that is being parsed.
-/
def getInput : MlirParserM ByteArray := do
  return (← getThe ParserState).input

/--
  Run an action within a new nested scope. This scope will be able to see all definitions in
  parent scopes and any definitions it add will only be visible within it and child scopes.
-/
def inChildScope {α : Type} (m : MlirParserM α) : MlirParserM α := do
  /- Push a new scope. -/
  modify fun s => { s with definitionsPerScope := s.definitionsPerScope.push (.emptyWithCapacity 128) }

  let result ← m

  /- Erase each value defined in the last scope, and pop the scope. -/
  let names := (← get).definitionsPerScope.back!
  for name in names do
    modifyIR' fun ir => .ok ((), ir.eraseValueName name)
  modify fun s => { s with definitionsPerScope := s.definitionsPerScope.pop }

  return result

/--
  Register the values `startIndex, ..., startIndex + count - 1` of the operation created last
  under the given name, in the current scope. If the name was forward-referenced earlier, the
  placeholders created for it are resolved to these values.
-/
def registerResultDefs (name : ByteArray) (pos : Location) (startIndex count : Nat) :
    MlirParserM Unit := do
  modifyIR (·.defineResults name pos startIndex count)
  modify fun s =>
    { s with definitionsPerScope :=
        s.definitionsPerScope.modify (s.definitionsPerScope.size - 1) (·.insert name) }

/--
  Register the argument `index` of the block being parsed under the given name, in the current
  scope.
-/
def registerBlockArgumentDef (name : ByteArray) (pos : Location) (index : Nat) :
    MlirParserM Unit := do
  modifyIR (·.defineBlockArgument name pos index)
  modify fun s =>
    { s with definitionsPerScope :=
        s.definitionsPerScope.modify (s.definitionsPerScope.size - 1) (·.insert name) }

/--
  Parse an operation result and the number of values it defines.
  This corresponds to the syntax `%name` and `%name:numberOfResults`.
-/
def parseOpResult : MlirParserM (ByteArray × Nat × Location) := do
  let nameToken ← parseToken .percentIdent "operation result expected"
  let tokenPos := nameToken.slice.start
  let slice := { nameToken.slice with start := nameToken.slice.start + 1 } -- skip % character
  let name := slice.of (← getInput)

  /- If the next token is ':', we parse the expected result count, otherwise we return the name. -/
  if !(← parseOptionalToken .colon).isSome then
    return (name, 1, tokenPos)

  let count := (← parseInteger false false).toNat
  if count ≤ 1 then
    throwAt tokenPos "expected named operation to have at least 1 result"

  return (name, count, tokenPos)

/--
  Parse the results before an operation definition,
  either as a list of values followed by '=', or nothing.
-/
def parseOpResults : MlirParserM (Array (ByteArray × Nat × Location)) := do
  let .percentIdent := (← peekToken).kind | return #[]
  let results ← parseList parseOpResult
  parsePunctuation "=" "'=' expected after operation results"
  return results

/--
  An operand whose type has not yet been resolved.
  This is used during parsing to allow parsing operands before their types.
  Once the operation type is known, `resolveOperand` can be used to create an SSA value and
  check that the type matches with previous uses.

  `index` is used for the `%name#index` syntax to refer to an indexed result
  when multiple are defined for the same value.
-/
structure UnresolvedOperand where
  name : ByteArray
  index : Option Nat
  pos : Location

/--
  Get the name of an UnresolvedOperand as a String.
-/
def UnresolvedOperand.nameString (operand : UnresolvedOperand) : String :=
  String.fromUTF8! operand.name

/--
  Get the result index of an UnresolvedOperand. If one was not specified explicitly, this
  defaults to 0.
-/
def UnresolvedOperand.indexD (operand : UnresolvedOperand) : Nat :=
  operand.index.getD 0

instance : ToString UnresolvedOperand where
  toString operand :=
    match operand.index with
    | none => s!"%{operand.nameString}"
    | some n => s!"%{operand.nameString}#{n}"

/--
  Parse an operation operand.
  This has the syntax `%name` or `%name#resultCount`.
-/
def parseOperand : MlirParserM UnresolvedOperand := do
  let nameToken ← parseToken .percentIdent "operand expected"
  let tokenPos := nameToken.slice.start
  let name : ByteArray := { nameToken.slice with start := nameToken.slice.start + 1 }.of (← getInput)

  /- If no result number is specified, return without one. -/
  let some resultCount ← parseOptionalToken .hashIdent
    | return UnresolvedOperand.mk name none tokenPos

  /- Parse the result count as a Nat. -/
  let hashPos := resultCount.slice.start
  let resultCount := { resultCount.slice with start := resultCount.slice.start + 1 }.of (← getInput) -- skip # character
  let some resultCount := String.fromUTF8? resultCount >>= String.toNat?
    | throwAt hashPos "invalid SSA value result number"
  return UnresolvedOperand.mk name resultCount tokenPos

/--
  Parse a list of operation operands delimited by parentheses.
-/
def parseOperands : MlirParserM (Array UnresolvedOperand) := do
  parseDelimitedList .paren parseOperand

/--
  Parse a block operand, returning its name and location. It is resolved later, with
  `resolveBlockOperand`.
-/
def parseBlockOperand : MlirParserM (ByteArray × Location) := do
  let labelToken ← parseToken .caretIdent "block name expected"
  let slice := { labelToken.slice with start := labelToken.slice.start + 1 } -- skip ^ character
  let name := slice.of (← getInput)
  return (name, labelToken.slice.start)

/--
  Parse a list of block operands delimited by square brackets, if present.
-/
def parseBlockOperands : MlirParserM (Array (ByteArray × Location)) := do
  return (← parseOptionalDelimitedList .square parseBlockOperand).getD #[]

/--
  Resolve an operand to an SSA value of the expected type and push it as an operand of the
  operation being parsed.
  If the value has not yet been defined, a forward-reference placeholder is created;
  it will be resolved when the definition is parsed, or reported as an error once
  top-level parsing finishes if the value is never defined.
-/
def resolveOperand (operand : UnresolvedOperand) (expectedType : TypeAttr) :
    MlirParserM Unit :=
  modifyIR (·.resolveOperand operand.name operand.indexD expectedType operand.pos
    (toString operand))

/-- The attribute parser state derived from the current parser state. -/
def attrParserState : MlirParserM AttrParserState := do
  let state ← get
  return {
    allowUnregisteredDialect := state.allowUnregisteredDialect
    typeAliases := state.typeAliases
  }

/--
  Parse a type, if present.
-/
def parseOptionalType : MlirParserM (Option TypeAttr) := do
  match AttrParser.parseOptionalType.run (← attrParserState) (← getThe ParserState) with
  | .ok (ty, _, parserState) =>
    set parserState
    return ty
  | .error err => throw err

/--
  Parse a type, otherwise return an error.
-/
def parseType (errorMsg : String := "type expected") : MlirParserM TypeAttr := do
  match ← parseOptionalType with
  | some ty => return ty
  | none => throwAtCurrentPos errorMsg

/--
  Parse an operation type, consisting of a colon followed by a function type.
-/
def parseOperationType : MlirParserM (Array TypeAttr × Array TypeAttr) := do
  parsePunctuation ":"
  let inputs ← parseDelimitedList .paren parseType
  parsePunctuation "->"
  if (←peekToken).kind = .lParen then
    let outputs ← parseDelimitedList .paren parseType
    return (inputs, outputs)
  else
    let outputType ← parseType
    return (inputs, #[outputType])

/--
  Parse an SSA value followed by a colon and a type, if present.
  Also returns the location of the value definition.
-/
def parseTypedValue : MlirParserM (ByteArray × TypeAttr × Location) := do
  let nameToken ← parseToken .percentIdent "value expected"
  let tokenPos := nameToken.slice.start
  let slice := { nameToken.slice with start := nameToken.slice.start + 1 } -- skip % character
  let name := slice.of (← getInput)
  parsePunctuation ":"
  let ty ← parseType
  return (name, ty, tokenPos)

/--
  Look ahead in the enclosing region for the label of the block `name`, and return the types of
  its arguments. Returns an empty array if the label is not found (the block is then reported as
  undefined when the region ends) or is malformed (the error is then reported when the label is
  actually parsed). The parser position is restored afterwards.

  Labels are only looked for at the nesting level of the enclosing region: nested regions are
  skipped, and block references inside square brackets are ignored.
-/
def scanForwardBlockArgTypes (name : ByteArray) : MlirParserM (Array TypeAttr) := do
  let saved ← getThe ParserState
  let input ← getInput
  let result ← tryCatch (do
    let mut depth := 0
    let mut squareDepth := 0
    let mut result : Array TypeAttr := #[]
    repeat
      let token ← consumeToken
      match token.kind with
      | .eof => break
      | .lBrace => depth := depth + 1
      | .rBrace =>
        if depth = 0 then break
        depth := depth - 1
      | .lSquare => squareDepth := squareDepth + 1
      | .rSquare => squareDepth := squareDepth - 1
      | .caretIdent =>
        if depth = 0 ∧ squareDepth = 0 then
          let labelName := { token.slice with start := token.slice.start + 1 }.of input
          if labelName == name then
            let arguments := (← parseOptionalDelimitedList .paren parseTypedValue).getD #[]
            result := arguments.map (·.2.1)
            break
      | _ => pure ()
    return result)
    (fun _ => pure #[])
  set saved
  return result

/--
  Resolve a block operand of the operation being parsed and push it. If the block is not yet
  known in the enclosing region, it is forward-declared, with the argument types found by
  looking ahead for its label.
-/
def resolveBlockOperand (name : ByteArray) (loc : Location) : MlirParserM Unit := do
  match (← getIR).lookupBlock name with
  | some _ => modifyIR (·.pushKnownBlockOperand name loc)
  | none =>
    let argTypes ← scanForwardBlockArgTypes name
    modifyIR (·.declareBlockUse name argTypes loc)

/--
  Parse the properties of an operation.
  The integer literals in a `mod_arith` operation's properties are kept as written (see
  `AttrParserState.rawIntegerLiterals`).
-/
def parseOpProperties (opCode : OpCode) : MlirParserM (propertiesOf opCode) := do
  let propertiesStart ← getPos
  if not (← parseOptionalPunctuation "<") then
    match Properties.fromAttrDict opCode {} with
    | .ok properties => return properties
    | .error err => throwAtCurrentPos err
  let rawIntegerLiterals :=
    (String.fromUTF8! opCode.name).startsWith "mod_arith."
  let attrState := { (← attrParserState) with rawIntegerLiterals }
  match AttrParser.parseAttributeDictionary.run attrState (← getThe ParserState) with
  | .ok (properties, _, parserState) =>
    set parserState
    parsePunctuation ">"
    match Properties.fromAttrDict opCode (Std.HashMap.ofList properties.toList) with
    | .ok properties => return properties
    | .error err => throwAt propertiesStart err
  | .error err => throw err

/--
Record the source operation name in the properties of a `builtin.unregistered`
operation.
-/
private def optionallySetUnregisteredOpName (opCode : OpCode)
    (properties : propertiesOf opCode) (opName : ByteArray) :
    propertiesOf opCode :=
  match opCode, properties with
  | .builtin .unregistered, properties => UnregisteredProperties.mk opName properties.properties
  | _, properties => properties

/--
  Parse the attributes of an operation, if present.
-/
def parseOpAttributes : MlirParserM DictionaryAttr := do
  match AttrParser.parseOptionalAttributeDictionary.run (← attrParserState) (← getThe ParserState) with
  | .ok (attrs, _, parserState) =>
    set parserState
    match attrs with
    | none => return DictionaryAttr.empty
    | some attrs => return DictionaryAttr.fromArray attrs
  | .error err => throw err

/--
  Define the block `name` with the given argument types in the region being parsed, make it the
  block being parsed, and register the names of its arguments.
-/
def defineBlock (name : ByteArray) (arguments : Array (ByteArray × TypeAttr × Location))
    (loc : Location) : MlirParserM Unit := do
  let numArgs ← modifyIR' fun ir =>
    (ir.defineBlock name (arguments.map (·.2.1)) loc).map fun (ir, numArgs) => (numArgs, ir)
  if numArgs ≠ arguments.size then
    throwAt loc "internal error: block argument count mismatch"
  /- Register the block argument names in the parser state. -/
  for ((argName, _argType, tokenPos), index) in arguments.zipIdx do
    registerBlockArgumentDef argName tokenPos index

/--
  Parse a block label, if present, and define the block (see `defineBlock`).
  Returns whether a label was parsed.
-/
def parseOptionalBlockLabel : MlirParserM Bool := do
  /- Parse the block name. -/
  let some labelToken ← parseOptionalToken .caretIdent
    | return false
  let slice := { labelToken.slice with start := labelToken.slice.start + 1 } -- skip ^ character
  let name := slice.of (← getInput)
  /- Parse the arguments. -/
  let arguments := (← parseOptionalDelimitedList .paren parseTypedValue).getD #[]
  parsePunctuation ":" "':' expected after block label"
  defineBlock name arguments labelToken.slice.start
  return true

/--
  Parse the label of an entry block and define the block.
  Since the entry block does not need a label, if no label is found,
  a block with an empty name is created.
-/
def parseEntryBlockLabel : MlirParserM Unit := do
  /- Try to parse a block label. -/
  if ← parseOptionalBlockLabel then
    return
  else -- Otherwise, create a block with an empty name.
    defineBlock ByteArray.empty #[] (← getPos)

mutual

/--
  Parse the regions of an operation, returning how many were parsed.
-/
partial def parseOpRegions : MlirParserM Nat := do
  return ((← parseOptionalDelimitedList .paren parseRegion).getD #[]).size

/--
  Parse an operation, if present, and insert it at the end of the block being parsed (or leave
  it detached, at top level).
-/
partial def parseOptionalOp : MlirParserM (Option IR.Op) := do
  /- Parse the operation. -/
  let opStart ← getPos
  let results ← parseOpResults
  let opNameStart ← getPos
  let some opName ← parseOptionalStringLiteral | return none
  let some opNameStr := String.fromUTF8? opName
    | throwAt opNameStart s!"op '{escapeStringLiteral (String.fromUTF8! opName)}' not a valid UTF8 string."
  let operands ← parseOperands
  let blockOperands ← parseBlockOperands

  /- Get the operation opcode. -/
  let opId := OpCode.fromName opName

  if opId = .builtin .unregistered then
    if !(← get).allowUnregisteredDialect then
      throwAt opNameStart
        s!"op '{opNameStr}' is not registered. Consider using --allow-unregistered-dialect."

  let properties ← parseOpProperties opId
  /- For `builtin.unregistered`, record the original op name in the properties so it can be
     printed back out. The properties dictionary itself has already been populated by
     `Properties.fromAttrDict` (see `UnregisteredProperties.fromAttrDict`). -/
  let properties := optionallySetUnregisteredOpName opId properties opName
  let numRegions ← parseOpRegions
  let attrs ← parseOpAttributes
  let (inputTypes, outputTypes) ← parseOperationType

  /- Results can have multiple parts so sum the sizes. -/
  let numResults := results.foldl (· + ·.2.1) 0

  /- Check that the number of results matches with the operation type. -/
  if outputTypes.size ≠ numResults then
    throwAt opNameStart s!"operation '{opNameStr}' declares {outputTypes.size} result types, but {numResults} result values were provided"

  /- Check that the number and types of operands matches with the operation type. -/
  if inputTypes.size ≠ operands.size then
    throwAt opNameStart s!"operation '{opNameStr}' declares {inputTypes.size} operand types, but {operands.size} operands were provided"
  for (operand, type) in operands.zip inputTypes do
    resolveOperand operand type
  for (name, loc) in blockOperands do
    resolveBlockOperand name loc

  let (op, createdResults) ← modifyIR' fun ir =>
    (ir.createOp opId outputTypes properties attrs operands.size blockOperands.size numRegions
      opNameStart).map fun (ir, op, createdResults) => ((op, createdResults), ir)
  if createdResults ≠ numResults then
    throwAt opNameStart "internal error: result count mismatch"
  /- Record where the operation started for diagnostics. -/
  modify fun state => { state with opLocations := state.opLocations.insert op opStart }

  /- Register the values for each result name. -/
  let mut index := 0
  for (name, count, tokenPos) in results do
    registerResultDefs name tokenPos index count
    index := index + count
  return op

/--
  Parse a region, leaving it available to the operation being parsed.
-/
partial def parseRegion : MlirParserM Unit := do
  /- Ensure variables defined in this region do not leak out of it. -/
  inChildScope do

  /- Create the region and parse the open delimiter. Blocks are local to regions: the region
     comes with a fresh block table. -/
  let regionStart ← getPos
  parsePunctuation "{"
  modifyIR (·.openRegion regionStart)

  /- Case where there are no blocks inside the region. -/
  if (← parseOptionalPunctuation "}") then
    modifyIR (·.closeRegion regionStart)
    return

  /- Parse the first block separately, as it may not have a label. -/
  parseEntryBlock
  /- Parse the following blocks. -/
  while true do
    if !(← parseOptionalBlock) then
      break

  /- Parse the closing delimiter. -/
  parsePunctuation "}"

  /- Check that all blocks in the regions that were forward declared were parsed. -/
  for (blockName, forwardLoc) in (← getIR).undefinedBlocks do
    throwAt forwardLoc s!"block %{String.fromUTF8! blockName} was used but never defined"

  modifyIR (·.closeRegion regionStart)

/--
  Parse the entry block of the region being parsed.
  Compared to a normal block, the entry block does not need a label.
-/
partial def parseEntryBlock : MlirParserM Unit := do
  parseEntryBlockLabel
  while true do
    if (← parseOptionalOp) = none then
      break
  modifyIR' fun ir => .ok ((), ir.closeBlock)

/--
  Parse a block of the region being parsed, if present.
-/
partial def parseOptionalBlock : MlirParserM Bool := do
  if !(← parseOptionalBlockLabel) then
    return false
  while true do
    if (← parseOptionalOp) == none then
      break
  modifyIR' fun ir => .ok ((), ir.closeBlock)
  return true

end

/--
  Parse an operation.
-/
private def parseOp : MlirParserM IR.Op := do
  let some op ← parseOptionalOp | throwAtCurrentPos "operation expected"
  return op

/-- Check that all SSA values forward referenced while parsing were eventually defined. -/
def checkNoUnresolvedForwardValues : MlirParserM Unit := do
  for (valueName, loc) in (← getIR).unresolvedForwardValues do
    throwAt loc s!"use of undefined value %{String.fromUTF8! valueName}"

/--
  Parse the `!name = type` alias definitions preceding the top-level operation. As in MLIR, a
  definition may use earlier aliases, a name may not be redefined, and names containing a `.` are
  reserved for dialect types.
-/
def parseTypeAliasDefs : MlirParserM Unit := do
  repeat
    let startPos ← getPos
    let some name ← parseOptionalPrefixedKeyword .exclamationIdent | break
    if (← get).typeAliases.contains name then
      throwAt startPos s!"redefinition of type alias id '{String.fromUTF8! name}'"
    if name.toList.contains '.'.toUInt8 then
      throwAt startPos "type names with a '.' are reserved for dialect-defined names"
    parsePunctuation "=" "expected '=' in type alias definition"
    let type ← parseType
    modify fun state => { state with typeAliases := state.typeAliases.insert name type }

/--
  Parse the top-level alias definitions and operation, and report unresolved forward references.
  The top-level operation is left detached.
-/
partial def parseTopLevelOp : MlirParserM IR.Op := do
  parseTypeAliasDefs
  let op ← parseOp
  checkNoUnresolvedForwardValues
  return op

/--
  The source input of a parsed program, along with the location of each parsed operation.
-/
structure SourceInfo where
  /-- The name of the source. -/
  sourceName : String
  /-- The content of the source. -/
  content : ByteArray
  /-- The location in `content` for each parsed operation. -/
  opLocations : Std.HashMap IR.Op Location

/-- Parse program bytes into a well-formed buffered IR context and its (in-bounds) top-level
    operation, formatting parse errors caret-style against `sourceName`. -/
def parseSourceString (content : ByteArray) (sourceName : String := "<string>")
    (allowUnregisteredDialect : Bool := false) :
    Except String (IRState.Result × SourceInfo) := do
  match ParserState.fromInput content with
  | .ok parser =>
    let state := MlirParserState.initial allowUnregisteredDialect
    match parseTopLevelOp.run state parser with
    | .ok (op, state, _) =>
      match state.ir.finish with
      | .ok result =>
        if result.op ≠ op then
          throw "internal error: top-level operation mismatch"
        return (result, { sourceName, content, opLocations := state.opLocations })
      | .error err => throw (err.format sourceName content)
    | .error err =>
      throw (err.format sourceName content)
  | .error err =>
    throw (err.format sourceName content)

end Veir.Parser

end
