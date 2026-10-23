module

public import Veir.Frontend.Pancake.Emit

/-!
# Scalar Pancake frontend

`Veir.PancakeFrontend.toIR expression` consumes the pinned Flapjack `ExpHOL`
carrier and returns a parsed, verified standalone `func.func @main`. Its
`inputs` list gives the function argument order; each entry retains both the
local/global kind and the raw `MlString` name. No source text parser is added.

Supported expressions: constants, variables, five word operators, multiplication,
and eight comparisons. Subtraction/multiplication require two arguments;
add/and/or/xor allow empty and variadic lists. Unsupported constructors and
malformed arities return errors. Comparisons retain the input word width.

`translate` exposes the numbered SSA instructions and output reference;
`toMLIR` exposes their generic MLIR serialization. `translate_runtime_correct`
proves that sequential execution through the actual Pancake scalar interpreter
agrees with the checked scalar projection of Flapjack's evaluator, for all
positive widths and word-valued local/global environments, including absent
bindings. The source snapshot is checked by `Tools/sync-pancake-semantics`.

The extractor and textual serialization/parser are tested integration boundaries,
not part of that theorem. Stateful constructors, parsing Pancake source text,
and whole-program observational equivalence remain separate work.
-/
