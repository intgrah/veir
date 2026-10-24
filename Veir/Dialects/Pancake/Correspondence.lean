module

public import Veir.Dialects.Pancake.Interpreter
public import Flapjack.Pancake.Semantics.PanSem.EvalExact
import all Veir.Dialects.Pancake.Interpreter
import all Veir.IR.Attribute

namespace Veir.Pancake
public section

/-!
Theorems against imported Flapjack definitions. The full-evaluator theorems
assume that the source child expressions evaluate to the operand words; they
do not assert a frontend translation or whole-program equivalence.
-/

theorem interpret_const {width : Nat} [NeZero width] (value : Int) :
    interpretScalar .const ⟨⟨value, .signless width⟩⟩
      #[TypeAttr.of IntegerType (.signless width)] #[] =
      some #[encodeWord (BitVec.ofInt width value)] := by
  simpa [evalWords] using interpret_encoded (width := width) .const ⟨⟨value, .signless width⟩⟩ []

theorem interpret_binop {width : Nat} [NeZero width]
    (operator : Flapjack.BinOp) (values : List (BitVec width)) :
    interpretScalar .op ⟨operator⟩ #[TypeAttr.of IntegerType (.signless width)]
      (values.map encodeWord).toArray =
      (Flapjack.wordOpHOL operator values).map (fun value => #[encodeWord value]) :=
  interpret_encoded .op ⟨operator⟩ values

theorem interpret_panop {width : Nat} [NeZero width]
    (operator : Flapjack.PanOp) (values : List (BitVec width)) :
    interpretScalar .panop ⟨operator⟩ #[TypeAttr.of IntegerType (.signless width)]
      (values.map encodeWord).toArray =
      (Flapjack.panOpHOL operator values).map (fun value => #[encodeWord value]) :=
  interpret_encoded .panop ⟨operator⟩ values

theorem interpret_cmp {width : Nat} [NeZero width]
    (operator : Flapjack.Cmp) (left right : BitVec width) :
    interpretScalar .cmp ⟨operator⟩ #[TypeAttr.of IntegerType (.signless width)]
      #[encodeWord left, encodeWord right] =
      some #[encodeWord (Flapjack.Compiler.Encoders.Asm.wordCmpResultHOL operator left right)] := by
  simpa [evalWords] using interpret_encoded .cmp ⟨operator⟩ [left, right]

@[expose] def sourceWord {width : Nat} [NeZero width] (value : BitVec width) : Flapjack.ValueHOL width :=
  .val (.word value)

/-- The exact source value representation has no poison; only words have scalar SSA results. -/
@[expose] def encodeSourceResult {width : Nat} [NeZero width] :
    Flapjack.ValueHOL width → Option (Array RuntimeValue)
  | .val (.word value) => some #[encodeWord value]
  | _ => none

@[simp] theorem sourceWords_all {width : Nat} [NeZero width] (values : List (BitVec width)) :
    (values.map sourceWord).all Flapjack.valueIsWord = true := by
  induction values <;> simp_all [sourceWord, Flapjack.valueIsWord]

@[simp] theorem sourceWords_map {width : Nat} [NeZero width] (values : List (BitVec width)) :
    (values.map sourceWord).map Flapjack.valueWord = values := by
  simp [List.map_map, Function.comp_def, sourceWord, Flapjack.valueWord]

theorem eval_const_correspondence {width : Nat} {σ : Type} [NeZero width]
    (state : Flapjack.PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (value : BitVec width) :
    interpretScalar .const ⟨⟨value.toNat, .signless width⟩⟩
      #[TypeAttr.of IntegerType (.signless width)] #[] =
      (Flapjack.evalHOLExact state (.const value)).bind encodeSourceResult := by
  simp [interpret_const, Flapjack.evalHOLExact, encodeSourceResult]

theorem eval_op_correspondence {width : Nat} {σ : Type} [NeZero width]
    (state : Flapjack.PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (operator : Flapjack.BinOp) (arguments : List (Flapjack.Pancake.PanLang.ExpHOL width))
    (values : List (BitVec width))
    (h : Flapjack.evalListHOLExact state arguments = some (values.map sourceWord)) :
    interpretScalar .op ⟨operator⟩ #[TypeAttr.of IntegerType (.signless width)]
      (values.map encodeWord).toArray =
      (Flapjack.evalHOLExact state (.op operator arguments)).bind encodeSourceResult := by
  rw [interpret_binop]
  simp only [Flapjack.evalHOLExact, h, sourceWords_all, sourceWords_map, ↓reduceIte]
  cases Flapjack.wordOpHOL operator values <;> rfl

theorem eval_panop_correspondence {width : Nat} {σ : Type} [NeZero width]
    (state : Flapjack.PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (operator : Flapjack.PanOp) (arguments : List (Flapjack.Pancake.PanLang.ExpHOL width))
    (values : List (BitVec width))
    (h : Flapjack.evalListHOLExact state arguments = some (values.map sourceWord)) :
    interpretScalar .panop ⟨operator⟩ #[TypeAttr.of IntegerType (.signless width)]
      (values.map encodeWord).toArray =
      (Flapjack.evalHOLExact state (.panop operator arguments)).bind encodeSourceResult := by
  rw [interpret_panop]
  simp only [Flapjack.evalHOLExact, h, sourceWords_all, sourceWords_map, ↓reduceIte]
  cases Flapjack.panOpHOL operator values <;> rfl

theorem eval_cmp_correspondence {width : Nat} {σ : Type} [NeZero width]
    (state : Flapjack.PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (operator : Flapjack.Cmp) (left right : Flapjack.Pancake.PanLang.ExpHOL width)
    (leftWord rightWord : BitVec width)
    (hl : Flapjack.evalHOLExact state left = some (sourceWord leftWord))
    (hr : Flapjack.evalHOLExact state right = some (sourceWord rightWord)) :
    interpretScalar .cmp ⟨operator⟩ #[TypeAttr.of IntegerType (.signless width)]
      #[encodeWord leftWord, encodeWord rightWord] =
      (Flapjack.evalHOLExact state (.cmp operator left right)).bind encodeSourceResult := by
  simp [interpret_cmp, Flapjack.evalHOLExact, hl, hr, sourceWord, encodeSourceResult,
    Flapjack.Compiler.Encoders.Asm.wordCmpResultHOL]

end
end Veir.Pancake
