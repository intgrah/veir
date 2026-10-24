module

import Veir.GlobalOpInfo
import Veir.Dialects.Pancake.Correspondence
import Veir.Dialects.Pancake.Monotonicity
meta import Veir.GlobalOpInfo
meta import Veir.Dialects.Pancake.Correspondence

open Veir

example : HasDialect OpCode Pancake := inferInstance
example (opType : Pancake) : InterpretOp'Monotone (.pancake opType) := inferInstance

#guard (#[Pancake.const, .op, .panop, .cmp]).all fun opType =>
  OpCode.fromName (Pancake.name opType) == some (.pancake opType)
#guard Pancake.fromName "pancake.shift".toUTF8 == none
#guard OpCode.getEffects (.pancake .op) ⟨.add⟩ == .none
#guard OpCode.isConstantLike (.pancake .const)
#guard !OpCode.isConstantLike (.pancake .op)
#guard !OpCode.propagatesPoison (.pancake .op)

private def roundtrip (opType : Pancake) (props : propertiesOf opType) : Bool := Id.run do
  let .ok restored := Pancake.fromAttrDict opType (Pancake.toAttrDict opType props) | return false
  let _ : DecidableEq (Pancake.propertiesOf opType) := by cases opType <;> simp only [Pancake.propertiesOf] <;> infer_instance
  return decide (restored = props)

#guard (#[Flapjack.BinOp.add, .sub, .and, .or, .xor]).all fun operator => roundtrip .op ⟨operator⟩
#guard roundtrip .panop ⟨.mul⟩
#guard (#[Flapjack.Cmp.equal, .lower, .less, .test, .notEqual, .notLower, .notLess, .notTest]).all
  fun operator => roundtrip .cmp ⟨operator⟩
#guard roundtrip .const ⟨⟨-1, .signless 64⟩⟩
#guard !(Pancake.fromAttrDict .op {}).isOk
#guard !(Pancake.fromAttrDict .op (Std.HashMap.ofList [("operator".toUTF8, .integerAttr ⟨0, .signless 8⟩)])).isOk
#guard !(Pancake.fromAttrDict .op (Std.HashMap.ofList [("operator".toUTF8, .stringAttr ⟨"mul".toUTF8⟩)])).isOk
#guard !(Pancake.fromAttrDict .panop (Std.HashMap.ofList [("operator".toUTF8, .stringAttr ⟨"add".toUTF8⟩)])).isOk
#guard !(Pancake.fromAttrDict .cmp (Std.HashMap.ofList [("operator".toUTF8, .stringAttr ⟨"unsigned_lt".toUTF8⟩)])).isOk
#guard !(Pancake.fromAttrDict .const (Std.HashMap.ofList [
  ("value".toUTF8, .integerAttr ⟨0, .signless 8⟩), ("extra".toUTF8, .unitAttr {})])).isOk

private def word (width : Nat) (value : Int) : RuntimeValue :=
  Pancake.encodeWord (BitVec.ofInt width value)
private def resultType (width : Nat) : Array TypeAttr := #[TypeAttr.of IntegerType (.signless width)]

#guard Pancake.interpretScalar .cmp ⟨.less⟩ (resultType 1) #[word 1 1, word 1 0] == some #[word 1 1]
#guard Pancake.interpretScalar .cmp ⟨.lower⟩ (resultType 1) #[word 1 1, word 1 0] == some #[word 1 0]
#guard Pancake.interpretScalar .op ⟨.add⟩ (resultType 32) #[word 32 0xffffffff, word 32 1] == some #[word 32 0]
#guard Pancake.interpretScalar .panop ⟨.mul⟩ (resultType 64)
  #[word 64 0x8000000000000000, word 64 2] == some #[word 64 0]
#guard Pancake.interpretScalar .op ⟨.and⟩ (resultType 32) #[] == some #[word 32 (-1)]
#guard Pancake.interpretScalar .op ⟨.or⟩ (resultType 64) #[] == some #[word 64 0]
#guard Pancake.interpretScalar .op ⟨.xor⟩ (resultType 1) #[] == some #[word 1 0]
#guard Pancake.interpretScalar .op ⟨.and⟩ (resultType 8)
  #[word 8 0xf3, word 8 0x5f, word 8 0x7a] == some #[word 8 0x52]
#guard Pancake.interpretScalar .const ⟨⟨-1, .signless 64⟩⟩ (resultType 64) #[] == some #[word 64 (-1)]

#guard Pancake.interpretScalar .op ⟨.add⟩ (resultType 8) #[word 16 1] == none
#guard Pancake.interpretScalar .op ⟨.add⟩ (resultType 8) #[.int 8 .poison] == none
#guard Pancake.interpretScalar .op ⟨.add⟩ (resultType 0) #[] == none
#guard Pancake.interpretScalar .op ⟨.sub⟩ (resultType 8) #[word 8 1] == none
#guard Pancake.interpretScalar .panop ⟨.mul⟩ (resultType 8) #[] == none
#guard Pancake.interpretScalar .cmp ⟨.equal⟩ (resultType 8) #[word 8 1] == none
#guard Pancake.interpretScalar .const ⟨⟨1, .signless 32⟩⟩ (resultType 64) #[] == none
#guard Pancake.interpretScalar .const ⟨⟨1, .signless 8⟩⟩ (resultType 8) #[word 8 1] == none
#guard Pancake.interpretScalar .op ⟨.add⟩ #[] #[] == none
#guard Pancake.interpretScalar .op ⟨.add⟩ ((resultType 8) ++ resultType 8) #[] == none
#guard Pancake.interpretScalar .op ⟨.add⟩ #[TypeAttr.of IntegerType (.signed 8)] #[] == none
#guard Pancake.interpretScalar .op ⟨.add⟩ #[TypeAttr.of IntegerType (.unsigned 8)] #[] == none
#guard match Pancake.interpretOp' .op ⟨.add⟩ (resultType 8) #[] #[⟨0⟩] MemoryState.empty with
  | .fail _ => true
  | _ => false

/-- info: 'Veir.Pancake.eval_const_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Pancake.eval_const_correspondence
/-- info: 'Veir.Pancake.eval_op_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Pancake.eval_op_correspondence
/-- info: 'Veir.Pancake.eval_panop_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Pancake.eval_panop_correspondence
/-- info: 'Veir.Pancake.eval_cmp_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Pancake.eval_cmp_correspondence

/-- info: 'Veir.Pancake.interpretOp_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Pancake.interpretOp_monotone
