module

import Veir.Dialects.Pancake.Correspondence
meta import Veir.Dialects.Pancake.Correspondence

open Veir

private def word (width : Nat) (value : Int) : RuntimeValue :=
  PancakeScalar.encodeWord (BitVec.ofInt width value)

private def resultType (width : Nat) : Array TypeAttr :=
  #[TypeAttr.of IntegerType (.signless width)]

private def run (opType : Pancake) (name : String) (width : Nat)
    (values : Array RuntimeValue) : Option (Array RuntimeValue) :=
  Pancake.interpretScalar opType (Pancake.operatorProperties name.toUTF8) (resultType width) values

/- One-bit signed comparisons and wide modular arithmetic exercise the value boundary. -/
#guard run .cmp "less" 1 #[word 1 1, word 1 0] == some #[word 1 1]
#guard run .cmp "lower" 1 #[word 1 1, word 1 0] == some #[word 1 0]
#guard run .op "add" 32 #[word 32 0xffffffff, word 32 1] == some #[word 32 0]
#guard run .panop "mul" 64 #[word 64 0x8000000000000000, word 64 2] == some #[word 64 0]
#guard run .op "and" 32 #[] == some #[word 32 (-1)]
#guard run .op "or" 64 #[] == some #[word 64 0]
#guard run .op "xor" 1 #[] == some #[word 1 0]
#guard run .op "and" 8 #[word 8 0xf3, word 8 0x5f, word 8 0x7a] == some #[word 8 0x52]
#guard Pancake.interpretScalar .const (Pancake.constantProperties ⟨-1, .signless 64⟩)
  (resultType 64) #[] == some #[word 64 (-1)]

/- Failed decoding is interpreter failure, never a coerced word or propagated poison. -/
#guard run .op "add" 8 #[word 16 1] == none
#guard run .op "add" 8 #[.int 8 .poison] == none
#guard run .op "add" 0 #[] == none
#guard run .op "sub" 8 #[word 8 1] == none
#guard run .panop "mul" 8 #[] == none
#guard run .cmp "equal" 8 #[word 8 1] == none
#guard run .op "unknown" 8 #[] == none
#guard run .load "add" 8 #[] == none
#guard Pancake.interpretScalar .const (Pancake.constantProperties ⟨1, .signless 32⟩)
  (resultType 64) #[] == none
#guard Pancake.interpretScalar .const (Pancake.constantProperties ⟨1, .signless 8⟩)
  (resultType 8) #[word 8 1] == none
#guard Pancake.interpretScalar .op DictionaryAttr.empty (resultType 8) #[] == none
#guard Pancake.interpretScalar .op
  { entries := #[("operator".toUTF8, .integerAttr ⟨1, .signless 8⟩)] }
  (resultType 8) #[] == none
#guard Pancake.interpretScalar .op (Pancake.operatorProperties "add".toUTF8) #[] #[] == none
#guard Pancake.interpretScalar .op (Pancake.operatorProperties "add".toUTF8)
  ((resultType 8) ++ resultType 8) #[] == none
#guard Pancake.interpretScalar .op (Pancake.operatorProperties "add".toUTF8)
  #[TypeAttr.of IntegerType (.signed 8)] #[] == none
#guard Pancake.interpretScalar .op (Pancake.operatorProperties "add".toUTF8)
  #[TypeAttr.of IntegerType (.unsigned 8)] #[] == none

/- Guard the proof boundary against accidental admitted or native-decided proofs. -/
/-- info: 'Veir.Pancake.interpret_binop_eq_flapjack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Pancake.interpret_binop_eq_flapjack

/-- info: 'Veir.Pancake.interpret_mul_eq_flapjack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Pancake.interpret_mul_eq_flapjack

/-- info: 'Veir.Pancake.interpret_cmp_eq_flapjack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Pancake.interpret_cmp_eq_flapjack

/-- info: 'Veir.Pancake.interpret_const_eq_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Pancake.interpret_const_eq_word
