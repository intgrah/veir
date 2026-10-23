module

public import Veir.Frontend.Pancake.Correctness
import all Veir.Frontend.Pancake.Basic
import all Veir.Dialects.Pancake.FlapjackExpr
import all Veir.Dialects.Pancake.Flapjack
import all Veir.Dialects.Pancake.Scalar

namespace Veir.PancakeFrontend
public section
open PancakeSource

@[expose] def sourceWord {width : Nat} [NeZero width] (value : BitVec width) : ValueHOL width :=
  .val (.word value)

/-- Word-valued local/global environments, including absent bindings. -/
@[expose] def sourceState {width : Nat} [NeZero width]
    (inputs : Variable → Option (BitVec width)) : ScalarState width where
  locals name := (inputs ⟨.local, name⟩).map sourceWord
  globals name := (inputs ⟨.global, name⟩).map sourceWord

@[simp] theorem all_sourceWord {width : Nat} [NeZero width] (values : List (BitVec width)) :
    (values.map sourceWord).all valueIsWord = true := by
  induction values <;> simp_all [sourceWord, valueIsWord]

@[simp] theorem map_sourceWord {width : Nat} [NeZero width] (values : List (BitVec width)) :
    (values.map sourceWord).map valueWord = values := by
  simp [List.map_map, Function.comp_def, sourceWord, valueWord]

mutual
  /-- The accepted AST agrees with the source-checked scalar evaluator clauses. -/
  theorem fromSource_correct {width : Nat} [NeZero width]
      (inputs : Variable → Option (BitVec width)) (expression : ExpHOL width)
      (translated : Expr) (h : fromSource expression = some translated) :
      evalScalarHOL (sourceState inputs) expression = (translated.eval inputs).map sourceWord := by
    cases expression with
    | const value =>
      simp only [fromSource, Option.some.injEq] at h
      subst translated
      simp [evalScalarHOL, Expr.eval, Expr.evalList, PancakeScalar.evaluate, sourceWord]
    | var kind name =>
      simp only [fromSource, Option.some.injEq] at h
      subst translated
      cases kind <;> rfl
    | op operator arguments =>
      simp only [fromSource] at h
      split at h
      · cases h
      · cases ha : fromSourceList arguments with
        | none => simp [ha] at h
        | some args =>
          simp [ha] at h
          subst translated
          have ih := fromSourceList_correct inputs arguments args ha
          simp only [evalScalarHOL, ih, Expr.eval]
          cases hv : Expr.evalList inputs args <;>
            simp [PancakeScalar.evaluate, sourceWord, valueIsWord, valueWord, Function.comp_def] <;> rfl
    | panop operator arguments =>
      cases operator
      simp only [fromSource] at h
      split at h
      · cases h
      · cases ha : fromSourceList arguments with
        | none => simp [ha] at h
        | some args =>
          simp [ha] at h
          subst translated
          have ih := fromSourceList_correct inputs arguments args ha
          simp only [evalScalarHOL, ih, Expr.eval]
          cases hv : Expr.evalList inputs args <;>
            simp [PancakeScalar.evaluate, sourceWord, valueIsWord, valueWord, Function.comp_def] <;> rfl
    | cmp operator left right =>
      cases hl : fromSource left with
      | none => simp [fromSource, hl] at h
      | some lhs =>
        cases hr : fromSource right with
        | none => simp [fromSource, hl, hr] at h
        | some rhs =>
          simp [fromSource, hl, hr] at h
          subst translated
          have il := fromSource_correct inputs left lhs hl
          have ir := fromSource_correct inputs right rhs hr
          simp only [evalScalarHOL, il, ir, Expr.eval, Expr.evalList]
          cases lhs.eval inputs <;> cases rhs.eval inputs <;>
            simp [sourceWord, PancakeScalar.evaluate, Compiler.Encoders.Asm.wordCmpResultHOL]
    | rstruct | rfield | nstruct | nfield | load | load32 | loadByte | shift |
      baseAddr | topAddr | bytesInWord => simp [fromSource] at h
  theorem fromSourceList_correct {width : Nat} [NeZero width]
      (inputs : Variable → Option (BitVec width)) (expressions : List (ExpHOL width))
      (translated : List Expr) (h : fromSourceList expressions = some translated) :
      evalListScalarHOL (sourceState inputs) expressions =
        (Expr.evalList inputs translated).map (List.map sourceWord) := by
    cases expressions with
    | nil => simp [fromSourceList] at h; subst translated; rfl
    | cons expression rest =>
      cases he : fromSource expression with
      | none => simp [fromSourceList, he] at h
      | some head =>
        cases ht : fromSourceList rest with
        | none => simp [fromSourceList, he, ht] at h
        | some tail =>
          simp [fromSourceList, he, ht] at h
          subst translated
          have ih := fromSource_correct inputs expression head he
          have it := fromSourceList_correct inputs rest tail ht
          simp only [evalListScalarHOL, ih, it, Expr.evalList]
          cases head.eval inputs <;> cases Expr.evalList inputs tail <;> rfl
end

/-- Compile a supported exact Flapjack expression into fresh, numbered SSA operations. -/
@[expose] def translate {width : Nat} [NeZero width] (expression : ExpHOL width) : Option Fragment :=
  (fromSource expression).map (compile 0)

/-- Correctness includes missing-variable and evaluation failures, not just successful runs. -/
theorem translate_correct {width : Nat} [NeZero width]
    (inputs : Variable → Option (BitVec width)) (expression : ExpHOL width)
    (fragment : Fragment) (h : translate expression = some fragment) :
    (evaluate inputs fragment).map sourceWord = evalScalarHOL (sourceState inputs) expression := by
  cases hs : fromSource expression with
  | none => simp [translate, hs] at h
  | some translated =>
    simp [translate, hs] at h
    subst fragment
    rw [fromSource_correct inputs expression translated hs]
    exact congrArg (Option.map sourceWord) (compile_correct inputs translated [])

end
end Veir.PancakeFrontend
