import Veir.Meta.Tactic.PBVDecide
import Veir.Data.PBV

open Veir.Data.PBV
/-! ## Comparisons -/

/-- Bool equality is symmetric -/
example {w : Nat} (x y : BitVec w) (hw : w ≤ 4) :
    (x == y) = (y == x) := by
  pbv_decide 4

/-- Adding the same value preserves bool equality -/
example {w : Nat} (x y z : BitVec w) (hw : w ≤ 4) :
    (x + z == y + z) = (x == y) := by
  pbv_decide 4

/-- Two values are equal iff their xor is zero -/
example {w : Nat} (x y : BitVec w) (hw : w ≤ 4) :
    (x ^^^ y == 0#w) = (x == y) := by
  pbv_decide 4

/-- Unsigned less-than is irreflexive -/
example {w : Nat} (x : BitVec w) (hw : w ≤ 4) :
    x.ult x = false := by
  pbv_decide 4

/-- Unsigned less-than is the negation of flipped unsigned less-or-equal -/
example {w : Nat} (x y : BitVec w) (hw : w ≤ 4) :
    x.ult y = !(y.ule x) := by
  pbv_decide 4

/-- Zero extension preserves unsigned less-than -/
example {w v : Nat} (x y : BitVec w) (hwv : w ≤ v) (hv : v ≤ 4) :
    (x.zeroExtend v).ult (y.zeroExtend v) = x.ult y := by
  pbv_decide 4

/-- Unsigned less-or-equal is reflexive -/
example {w : Nat} (x : BitVec w) (hw : w ≤ 4) :
    x.ule x = true := by
  pbv_decide 4

/-- Every value is unsigned less-or-equal to `-1` -/
example {w : Nat} (x : BitVec w) (hw : w ≤ 4) :
    x.ule (-1#w) = true := by
  pbv_decide 4

/-- Zero extension preserves unsigned less-or-equal -/
example {w v : Nat} (x y : BitVec w) (hwv : w ≤ v) (hv : v ≤ 4) :
    (x.zeroExtend v).ule (y.zeroExtend v) = x.ule y := by
  pbv_decide 4

/-- Signed less-than is irreflexive -/
example {w : Nat} (x : BitVec w) (hw : w ≤ 4) :
    x.slt x = false := by
  pbv_decide 4

/-- Signed less-than is the negation of flipped signed less-or-equal -/
example {w : Nat} (x y : BitVec w) (hw : w ≤ 4) :
    x.slt y = !(y.sle x) := by
  pbv_decide 4

/-- Sign extension preserves signed less-than -/
example {w v : Nat} (x y : BitVec w) (hwv : w ≤ v) (hv : v ≤ 4) :
    (x.signExtend v).slt (y.signExtend v) = x.slt y := by
  pbv_decide 4

/-- Signed less-or-equal is reflexive -/
example {w : Nat} (x : BitVec w) (hw : w ≤ 4) :
    x.sle x = true := by
  pbv_decide 4

/-- Signed less-or-equal is antisymmetric -/
example {w : Nat} (x y : BitVec w) (hw : w ≤ 4) :
    (x.sle y && y.sle x) = (x == y) := by
  pbv_decide 4

/-- Sign extension preserves signed less-or-equal -/
example {w v : Nat} (x y : BitVec w) (hwv : w ≤ v) (hv : v ≤ 4) :
    (x.signExtend v).sle (y.signExtend v) = x.sle y := by
  pbv_decide 4
