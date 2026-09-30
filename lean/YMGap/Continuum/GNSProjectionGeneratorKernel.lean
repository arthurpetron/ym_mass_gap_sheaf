/-
# Exact zero set of a finite completed projection generator

For any finite list, including repetitions, the residual energy and the
residual-sum generator vanish exactly on the common fixed space. This is a
same-carrier algebraic kernel identity, not a spectral gap.
-/

import YMGap.Continuum.GNSProjectionSignedEnergy

namespace YMGap.Continuum.GNSProjectionGeneratorKernel

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSDenseCompletionLaws
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSProjectionSweep.Family
open YMGap.Continuum.GNSFiniteSumEnergy

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.add_zero' (A.approx n))))

private theorem rc_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_neg_self_eqv (A.approx n)))

private theorem cSub_self (D : GNSData) (x : GNSCompletionSpace D) :
    D.cSub x x = embedV D D.zero := by
  apply eq_of_pairings_equal
  intro z
  rw [D.cinnerCompl_cSub_left, rc_sub_self, D.cinnerCompl_embedZero_left]

private theorem sumOn_zero {A : Type} (xs : List A) :
    sumOn xs (fun _ => RCzero) = RCzero := by
  induction xs with
  | nil => rfl
  | cons a rest ih => simp only [sumOn, ih, rc_zero_add]

private theorem sumOn_zero_of_terms {A : Type} (xs : List A) (f : A → RC)
    (h : ∀ a, a ∈ xs → f a = RCzero) : sumOn xs f = RCzero := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
      rw [sumOn, h a List.mem_cons_self, rc_zero_add]
      exact ih (fun j hj => h j (List.mem_cons_of_mem a hj))

/-- A nonnegative summand is bounded by any finite sum containing it.
Membership, rather than nodup, is the only list hypothesis. -/
private theorem term_le_sum {A : Type} (xs : List A) (f : A → RC)
    (hf : ∀ a, a ∈ xs → RCnonneg (f a)) (i : A) (hi : i ∈ xs) :
    RCle (f i) (sumOn xs f) := by
  induction xs with
  | nil => exact False.elim (List.not_mem_nil hi)
  | cons a rest ih =>
      rcases List.mem_cons.mp hi with hia | hir
      · subst i
        have hrest := sumOn_nonnegative rest f
          (fun j hj => hf j (List.mem_cons_of_mem a hj))
        have h := RCadd_le_add (RCle_refl (f a)) hrest
        rw [rc_add_zero] at h
        exact h
      · have hfirst := hf a List.mem_cons_self
        have htail := ih (fun j hj => hf j (List.mem_cons_of_mem a hj)) hir
        have h := RCadd_le_add hfirst htail
        rw [rc_zero_add] at h
        exact h

variable {D : GNSData} {Index : Type} (P : Family D Index)

/-- Zero residual energy is equivalent to every listed projection fixing x.
Repeated tests merely repeat nonnegative summands. -/
theorem finalEnergy_zero_iff_jointFixed (tests : List Index)
    (x : GNSCompletionSpace D) :
    P.finalEnergy tests x = RCzero ↔ P.JointFixed tests x := by
  constructor
  · intro hz i hi
    apply Eq.symm
    apply eq_of_distance_le_zero x (P.op i x)
    change RCle (normSq (P.residual i x)) RCzero
    have hterm := term_le_sum tests
      (fun j => normSq (P.residual j x))
      (fun j hj => D.cinner_self_nonneg (P.residual j x)) i hi
    change RCle (normSq (P.residual i x)) (P.finalEnergy tests x) at hterm
    rwa [hz] at hterm
  · intro hx
    change sumOn tests (fun i => normSq (P.residual i x)) = RCzero
    apply sumOn_zero_of_terms tests
    intro i hi
    rw [show P.residual i x = embedV D D.zero by
      unfold Family.residual
      rw [hx i hi, cSub_self]]
    exact D.cinnerCompl_embedZero_left _

/-- The generator is zero precisely on the same joint fixed space. -/
theorem residualSum_zero_iff_jointFixed (tests : List Index)
    (x : GNSCompletionSpace D) :
    P.residualSum tests x = embedV D D.zero ↔ P.JointFixed tests x := by
  constructor
  · intro hz
    apply (finalEnergy_zero_iff_jointFixed P tests x).mp
    rw [← P.residualSum_self_pairing tests x, hz]
    exact D.cinnerCompl_embedZero_left _
  · intro hx
    apply eq_of_pairings_equal
    intro y
    rw [P.residualSum_pairing]
    have hterm (i : Index) (hi : i ∈ tests) :
        D.cinnerCompl (P.residual i x) y = RCzero := by
      unfold Family.residual
      rw [hx i hi, cSub_self]
      exact D.cinnerCompl_embedZero_left _
    have hsum : sumOn tests (fun i => D.cinnerCompl (P.residual i x) y) = RCzero :=
      sumOn_zero_of_terms tests _ hterm
    rw [hsum]
    exact (D.cinnerCompl_embedZero_left y).symm

theorem residualSum_zero_iff_finalEnergy_zero (tests : List Index)
    (x : GNSCompletionSpace D) :
    P.residualSum tests x = embedV D D.zero ↔ P.finalEnergy tests x = RCzero :=
  (residualSum_zero_iff_jointFixed P tests x).trans
    (finalEnergy_zero_iff_jointFixed P tests x).symm

#print axioms finalEnergy_zero_iff_jointFixed
#print axioms residualSum_zero_iff_jointFixed
#print axioms residualSum_zero_iff_finalEnergy_zero

end YMGap.Continuum.GNSProjectionGeneratorKernel
