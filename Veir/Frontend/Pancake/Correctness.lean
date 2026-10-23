module

public import Veir.Frontend.Pancake.Basic
import all Veir.Frontend.Pancake.Basic

namespace Veir.PancakeFrontend
public section

@[expose] def Ref.Valid (bound : Nat) : Ref → Prop
  | .input _ => True
  | .temp index => index < bound

theorem Ref.Valid.mono {a b : Nat} {ref : Ref} (h : ref.Valid a) (hab : a ≤ b) :
    ref.Valid b := by
  cases ref <;> simp_all [Ref.Valid]
  omega

mutual
  theorem compile_valid (base : Nat) (expression : Expr) :
      (compile base expression).result.Valid (base + (compile base expression).code.length) := by
    cases expression with
    | var => simp [compile, Ref.Valid]
    | app operation arguments => simp [compile, Ref.Valid]
  theorem compileList_valid (base : Nat) (expressions : List Expr) :
      ∀ ref ∈ (compileList base expressions).results,
        ref.Valid (base + (compileList base expressions).code.length) := by
    cases expressions with
    | nil => simp [compileList]
    | cons expression rest =>
      simp only [compileList, List.mem_cons, List.length_append]
      intro ref h
      rcases h with rfl | h
      · exact (compile_valid base expression).mono (by omega)
      · have := compileList_valid (base + (compile base expression).code.length) rest ref h
        simpa [Nat.add_assoc] using this
end

theorem Ref.read_append (inputs : Variable → Option α) (initial suffix : List α)
    (ref : Ref) (h : ref.Valid initial.length) :
    ref.read inputs (initial ++ suffix) = ref.read inputs initial := by
  cases ref with
  | input => rfl
  | temp index =>
    simp only [Ref.Valid] at h
    simp [Ref.read, List.getElem?_append, h]

theorem run_append {width : Nat} [NeZero width]
    (inputs : Variable → Option (BitVec width)) (first rest : List Instruction)
    (initial : List (BitVec width)) :
    run inputs (first ++ rest) initial = (run inputs first initial).bind (run inputs rest) := by
  induction first generalizing initial with
  | nil => rfl
  | cons instruction first ih =>
    simp only [List.cons_append, run]
    cases instruction.operands.mapM (Ref.read inputs initial) <;> simp_all
    simp [Option.bind_assoc]

theorem run_extends {width : Nat} [NeZero width]
    (inputs : Variable → Option (BitVec width)) (code : List Instruction)
    (initial final : List (BitVec width)) (h : run inputs code initial = some final) :
    ∃ suffix, final = initial ++ suffix ∧ suffix.length = code.length := by
  induction code generalizing initial with
  | nil => simp [run] at h; subst final; exact ⟨[], by simp⟩
  | cons instruction rest ih =>
    simp only [run] at h
    cases hop : instruction.operands.mapM (Ref.read inputs initial) with
    | none => simp [hop] at h
    | some operands =>
      cases hv : PancakeScalar.evaluate instruction.operation operands with
      | none => simp [hop, hv] at h
      | some value =>
        simp [hop, hv] at h
        obtain ⟨suffix, heq, hlen⟩ := ih _ h
        exact ⟨value :: suffix, by simpa [List.append_assoc] using heq, by simp [hlen]⟩

theorem run_length {width : Nat} [NeZero width]
    (inputs : Variable → Option (BitVec width)) (code : List Instruction)
    (initial final : List (BitVec width)) (h : run inputs code initial = some final) :
    final.length = initial.length + code.length := by
  obtain ⟨suffix, rfl, hlen⟩ := run_extends inputs code initial final h
  simp [hlen]

mutual
  /-- Execution of the emitted SSA sequence agrees with the scalar expression. -/
  theorem compile_correct {width : Nat} [NeZero width]
      (inputs : Variable → Option (BitVec width)) (expression : Expr)
      (initial : List (BitVec width)) :
      evaluate inputs (compile initial.length expression) initial = expression.eval inputs := by
    cases expression with
    | var => rfl
    | app operation arguments =>
      have ih := compileList_correct inputs arguments initial
      cases hr : run inputs (compileList initial.length arguments).code initial with
      | none =>
        simp [hr] at ih
        simp [evaluate, compile, run_append, hr, Expr.eval, ← ih]
      | some values =>
        have hlen := run_length inputs _ initial values hr
        simp [hr] at ih
        simp only [evaluate, compile, run_append, hr, Option.bind_some, run, Expr.eval, ← ih]
        simp [Ref.read, ← hlen, Option.bind_assoc]
  theorem compileList_correct {width : Nat} [NeZero width]
      (inputs : Variable → Option (BitVec width)) (expressions : List Expr)
      (initial : List (BitVec width)) :
      ((run inputs (compileList initial.length expressions).code initial).bind fun values =>
        (compileList initial.length expressions).results.mapM (Ref.read inputs values)) =
        Expr.evalList inputs expressions := by
    cases expressions with
    | nil => rfl
    | cons expression rest =>
      have ihFirst := compile_correct inputs expression initial
      simp only [evaluate] at ihFirst
      cases hfirst : run inputs (compile initial.length expression).code initial with
      | none =>
        simp [hfirst] at ihFirst
        simp [compileList, run_append, hfirst, Expr.evalList, ← ihFirst]
      | some firstValues =>
        have hlen := run_length inputs _ initial firstValues hfirst
        have ihRest := compileList_correct inputs rest firstValues
        simp [hfirst] at ihFirst
        simp only [compileList, run_append, hfirst, Option.bind_some, ← hlen]
        cases hrest : run inputs (compileList firstValues.length rest).code firstValues with
        | none =>
          simp [hrest] at ihRest
          simp [Expr.evalList, ← ihRest]
        | some final =>
          obtain ⟨suffix, rfl, _⟩ := run_extends inputs _ firstValues final hrest
          have hv := compile_valid initial.length expression
          rw [← hlen] at hv
          simp only [hrest, Option.bind_some] at ihRest ⊢
          simp [List.mapM_cons, Ref.read_append _ _ _ _ hv, ihFirst, ihRest, Expr.evalList]
end

end
end Veir.PancakeFrontend
