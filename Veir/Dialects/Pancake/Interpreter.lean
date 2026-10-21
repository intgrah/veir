module

public import Veir.Dialects.Pancake.OpInfo
public import Veir.Interpreter.Memory

namespace Veir.Pancake

public section

/-- Execute the checked scalar subset. Unsupported operations and invalid inputs fail. -/
@[expose]
def interpretScalar (opType : Pancake) (props : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) : Option (Array RuntimeValue) := do
  let operation ← scalarOperation? opType props
  PancakeScalar.interpret operation resultTypes operands

/-- Scalar Pancake operations leave memory untouched and produce no control-flow action. -/
@[expose]
def interpretOp' (opType : Pancake) (props : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    (blockOperands : Array BlockPtr) (memory : MemoryState) :
    Interp (Array RuntimeValue × MemoryState × Option ControlFlowAction) := do
  if !blockOperands.isEmpty then none else do
    let values ← interpretScalar opType props resultTypes operands
    return (values, memory, none)

end

end Veir.Pancake
