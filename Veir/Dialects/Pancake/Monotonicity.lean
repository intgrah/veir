module

public import Veir.Interpreter.Lemmas
public import Veir.Dialects.Pancake.Interpreter
import all Veir.Dialects.Pancake.Interpreter
import all Veir.Interpreter.Basic
import all Veir.Interpreter.Refinement.Basic

namespace Veir.Pancake
public section

private theorem decodeWord_eq_some {width : Nat} {runtime : RuntimeValue} {word : BitVec width}
    (h : decodeWord width runtime = some word) : runtime = encodeWord word := by
  cases runtime with
  | int actual value =>
    cases value with
    | poison => simp [decodeWord] at h
    | val bits =>
      simp only [decodeWord] at h
      split at h
      · next heq => subst actual; simp only [Option.some.injEq] at h; subst word; rfl
      · cases h
  | _ => simp [decodeWord] at h

private theorem decodeWords_reconstruct {width : Nat} (values : List RuntimeValue)
    (words : List (BitVec width)) (h : values.mapM (decodeWord width) = some words) :
    values = words.map encodeWord := by
  induction values generalizing words with
  | nil => simp at h; subst words; rfl
  | cons value values ih =>
    cases hv : decodeWord width value with
    | none => simp [List.mapM_cons, hv] at h
    | some word =>
      cases ht : values.mapM (decodeWord width) with
      | none => simp [List.mapM_cons, hv, ht] at h
      | some rest =>
        simp [List.mapM_cons, hv, ht] at h
        subst words
        simp [decodeWord_eq_some hv, ih rest ht]

private theorem concrete_of_isRefinedBy {width : Nat} {word : BitVec width} {target : RuntimeValue}
    (h : (encodeWord word).isRefinedBy target) : target = encodeWord word := by
  obtain ⟨value, rfl, hv⟩ := RuntimeValue.int_of_isRefinedBy h
  cases value <;> simp_all [encodeWord, _root_.isRefinedBy_eq]

private theorem concrete_array_eq (words : List (BitVec width)) (target : Array RuntimeValue)
    (h : RuntimeValue.arrayIsRefinedBy (words.map encodeWord).toArray target) :
    target = (words.map encodeWord).toArray := by
  apply Array.ext
  · exact h.1.symm
  · intro index hi hj
    have href := h.2 index hj
    have hj' : index < words.length := by simpa using hj
    have source_eq : (words.map encodeWord).toArray[index]! = encodeWord words[index]! := by
      simp [getElem!_pos, hj']
    rw [source_eq] at href
    have heq := concrete_of_isRefinedBy href
    rw [← source_eq] at heq
    simpa [getElem!_pos, hi, hj, hj'] using heq

private theorem successful_operands (opType : Pancake) (props : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands result : Array RuntimeValue)
    (h : interpretScalar opType props resultTypes operands = some result) :
    ∃ (width : Nat) (words : List (BitVec width)), operands = (words.map encodeWord).toArray := by
  simp only [interpretScalar] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i attrs resultType hresult attr intType htype hsigned hwidth
  cases hd : operands.toList.mapM (decodeWord intType.bitwidth) with
  | none => simp [hd] at h
  | some words =>
    refine ⟨intType.bitwidth, words, ?_⟩
    have := decodeWords_reconstruct operands.toList words hd
    simpa using congrArg List.toArray this

/-- Concrete Pancake operands refine only to themselves; failure imposes no refinement constraint. -/
theorem interpretOp_monotone (opType : Pancake) (props : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands operands' : Array RuntimeValue)
    (blockOperands : Array BlockPtr) (memory : MemoryState)
    (href : RuntimeValue.arrayIsRefinedBy operands operands') :
    Interp.isRefinedBy OperationResult.isRefinedBy
      (interpretOp' opType props resultTypes operands blockOperands memory)
      (interpretOp' opType props resultTypes operands' blockOperands memory) := by
    simp only [interpretOp']
    split
    · simp [Interp.isRefinedBy]
    · cases hs : interpretScalar opType props resultTypes operands with
      | none => simp [Interp.isRefinedBy]
      | some values =>
        obtain ⟨width, words, rfl⟩ := successful_operands opType props resultTypes operands values hs
        obtain rfl := concrete_array_eq words operands' href
        simp only [hs]
        exact Interp.isRefinedBy_refl_operationResult _

/-- Register the dialect proof with the global interpreter's refinement interface. -/
instance instScalarMonotone (opType : Pancake) : InterpretOp'Monotone (.pancake opType) where
  monotone props resultTypes operands operands' blockOperands memory href := by
    simpa only [Veir.interpretOp'] using
      interpretOp_monotone opType props resultTypes operands operands' blockOperands memory href

end
end Veir.Pancake
