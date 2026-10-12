module

public import CTree.Defs
public import CTree.Iter
public import CTree.Interp

public section

namespace CTree
open Coinductive Lean.Order

variable {EIn FIn CIn C'In DIn X Y X' Y' : Type u}
  {E : EIn → Type u} {F : FIn → Type u} {C : CIn → Type u} {C' : C'In → Type u} {D : DIn → Type u}
  {R R' : Type u} (RR : R → R' → Prop)

set_option warn.sorry false in
/--
Simulation between ctrees: the rhs should have at least all
the behaviors of the lhs.
The simulation is parameterized by a relation on return values.
-/
def sim (t : CTree E C R) (u : CTree E C' R') : Prop := let _ := RR; sorry

set_option warn.sorry false in
theorem sim_ret (r : R) (r' : R') :
  RR r r' →
  sim RR (CTree.ret (E := E) (C := C) r) (CTree.ret (C := C') r') := sorry

set_option warn.sorry false in
theorem sim_tau_l (i : C1In ⊕ CIn) (k : (C1 ⊕ₑ C) i → CTree E C R) (u : CTree E C' R') :
  (∀ x, sim RR (k x) u) →
  sim RR (CTree.tauG i k) u := sorry

set_option warn.sorry false in
theorem sim_tau_r (i' : C1In ⊕ C'In) (t : CTree E C R) (k' : (C1 ⊕ₑ C') i' → CTree E C' R') x :
  sim RR t (k' x) →
  sim RR t (CTree.tauG i' k') := sorry

set_option warn.sorry false in
theorem sim_tau (i : C1In ⊕ CIn) (i' : C1In ⊕ C'In) (k : (C1 ⊕ₑ C) i → CTree E C R) (k' : (C1 ⊕ₑ C') i' → CTree E C' R') :
  (∀ x, ∃ y, sim RR (k x) (k' y)) →
  sim RR (CTree.tauG i k) (CTree.tauG i' k') := sorry

set_option warn.sorry false in
theorem sim_tau_id (i : C1In ⊕ CIn) (k : (C1 ⊕ₑ C) i → CTree E C R) (k' : (C1 ⊕ₑ C) i → CTree E C R') :
  (∀ x, sim RR (k x) (k' x)) →
  sim RR (CTree.tauG i k) (CTree.tauG i k') := sorry

set_option warn.sorry false in
theorem sim_vis (i : EIn) (k : E i → CTree E C R) (k' : E i → CTree E C' R') :
  (∀ x, sim RR (k x) (k' x)) →
  sim RR (CTree.vis i k) (CTree.vis i k') := sorry

set_option warn.sorry false in
theorem sim_bind {RR RR'} (t : CTree E C X) (u : CTree E C' X') (k : X → CTree E C Y) (k' : X' → CTree E C' Y') :
  sim RR t u →
  (∀ x y, RR x y → sim RR' (k x) (k' y)) →
  sim RR' (bind t k) (bind u k') := sorry

set_option warn.sorry false in
theorem sim_iter {I I'} {RRi : I → I' → Prop} {RRo : X → Y → Prop} {RR} (body : I → CTree E C (I ⊕ X)) (body' : I' → CTree E C (I' ⊕ Y)) i i' :
  RRi i i' →
  (∀ x y, RRi x y → sim RR (body x) (body' y)) →
  sim (R' := Y) RRo (CTree.iter body i) (CTree.iter (X := Y) body' i') := sorry

set_option warn.sorry false in
theorem sim_interp {RR} (h : (i : EIn) → CTree F C (E i)) (t : CTree E C X) (u : CTree E C Y) :
    sim RR t u →
    sim RR (CTree.interp h t) (CTree.interp h u) := sorry

set_option warn.sorry false in
theorem sim_refine {RR} (h : (i : CIn) → CTree E D (C i)) (t : CTree E C X) (u : CTree E C Y) :
    sim RR t u →
    sim RR (CTree.refine h t) (CTree.refine h u) := sorry

end CTree

