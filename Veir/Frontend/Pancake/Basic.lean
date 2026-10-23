module

public import Veir.Dialects.Pancake.Correspondence
public import Veir.Dialects.Pancake.FlapjackExpr
import all Veir.Dialects.Pancake.Scalar

namespace Veir.PancakeFrontend
public section

open PancakeSource

/-- Local and global bindings with the same bytes are distinct SSA inputs. -/
structure Variable where
  kind : VarKind
  name : MlS
  deriving DecidableEq, Repr

/-- The checked scalar subset, after rejecting unsupported source constructors. -/
inductive Expr where
  | var (binding : Variable)
  | app (operation : PancakeScalar.Operation) (arguments : List Expr)

mutual
  @[expose] def Expr.eval {width : Nat} [NeZero width]
      (inputs : Variable → Option (BitVec width)) : Expr → Option (BitVec width)
    | .var binding => inputs binding
    | .app operation arguments => do
      let values ← Expr.evalList inputs arguments
      PancakeScalar.evaluate operation values
  @[expose] def Expr.evalList {width : Nat} [NeZero width]
      (inputs : Variable → Option (BitVec width)) : List Expr → Option (List (BitVec width))
    | [] => some []
    | expression :: rest => do
      let value ← expression.eval inputs
      let values ← Expr.evalList inputs rest
      return value :: values
end

mutual
  /-- Parse the exact Flapjack AST. Invalid arities and all non-scalar forms fail. -/
  @[expose] def fromSource {width : Nat} [NeZero width] : ExpHOL width → Option Expr
    | .const value => some (.app (.constant ⟨value.toNat, .signless width⟩) [])
    | .var kind name => some (.var ⟨kind, name⟩)
    | .op operator arguments => do
      if operator = .sub && arguments.length != 2 then none else
        return .app (.binop operator) (← fromSourceList arguments)
    | .panop .mul arguments => do
      if arguments.length != 2 then none else
        return .app .multiply (← fromSourceList arguments)
    | .cmp operator left right => do
      return .app (.compare operator) [← fromSource left, ← fromSource right]
    | _ => none
  @[expose] def fromSourceList {width : Nat} [NeZero width] :
      List (ExpHOL width) → Option (List Expr)
    | [] => some []
    | expression :: rest => do
      return (← fromSource expression) :: (← fromSourceList rest)
end

/-- Input references and temporary references occupy separate namespaces. -/
inductive Ref where
  | input (binding : Variable)
  | temp (index : Nat)
  deriving DecidableEq, Repr

@[expose] def Ref.read (inputs : Variable → Option α) (values : List α) : Ref → Option α
  | .input binding => inputs binding
  | .temp index => values[index]?

/-- Every instruction defines the next temporary, exactly once. -/
structure Instruction where
  operation : PancakeScalar.Operation
  operands : List Ref

structure Fragment where
  code : List Instruction
  result : Ref

structure Fragments where
  code : List Instruction
  results : List Ref

mutual
  /-- Postorder SSA emission; `base` is the number of existing temporaries. -/
  @[expose] def compile (base : Nat) : Expr → Fragment
    | .var binding => ⟨[], .input binding⟩
    | .app operation arguments =>
      let args := compileList base arguments
      ⟨args.code ++ [⟨operation, args.results⟩], .temp (base + args.code.length)⟩
  @[expose] def compileList (base : Nat) : List Expr → Fragments
    | [] => ⟨[], []⟩
    | expression :: rest =>
      let first := compile base expression
      let others := compileList (base + first.code.length) rest
      ⟨first.code ++ others.code, first.result :: others.results⟩
end

/-- Sequential SSA execution using the same scalar word operations as VeIR. -/
@[expose] def run {width : Nat} [NeZero width]
    (inputs : Variable → Option (BitVec width)) :
    List Instruction → List (BitVec width) → Option (List (BitVec width))
  | [], values => some values
  | instruction :: rest, values => do
    let operands ← instruction.operands.mapM (Ref.read inputs values)
    let result ← PancakeScalar.evaluate instruction.operation operands
    run inputs rest (values ++ [result])

@[expose] def evaluate {width : Nat} [NeZero width]
    (inputs : Variable → Option (BitVec width)) (fragment : Fragment)
    (initial : List (BitVec width) := []) : Option (BitVec width) := do
  let values ← run inputs fragment.code initial
  fragment.result.read inputs values

end
end Veir.PancakeFrontend
