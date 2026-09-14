/-
# Bounded linear inverse for the ORIGINAL two-step defect

The constructed inverse satisfies ||R x||^2 <= 4||center x||^2 <= 4||x||^2.
The proof doubles the inequality obtained from R x = center x + T_2 R x
and cancels the residual norm. No spectral theorem, square root, or division
by a potentially zero vector norm occurs. Uniqueness proves linearity and
the same bound controls distances. Scalars retain their CReal/QCauchy data.

This concerns the existing fixed-spacing, fixed-nome SU(2) plaquette OS
completion. It neither proves full quotient-level completeness nor extends
the observable carrier, takes a continuum limit, or identifies a Hamiltonian.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicResolvent

namespace YMGap.Continuum.BF4ExactSlabThermodynamicResolventBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar
open YMGap.Continuum.BF4ExactSlabThermodynamicRealScalarAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial
open YMGap.Continuum.BF4ExactSlabThermodynamicResolvent
open YMGap.Continuum.MeanExpConvexProgress (le_of_add_le_add_right)

local notation "B" => completedInner

private theorem rc_add_cancel (a b c : RC)
    (h : RCle (RCadd a c) (RCadd b c)) : RCle a b := by
  revert h
  refine Quotient.inductionOn₃ a b c ?_
  intro A B0 C h epsilon he
  obtain ⟨N, hN⟩ := h epsilon he
  refine ⟨N, fun n hn => ?_⟩
  apply le_of_add_le_add_right (c := C.approx n)
  exact Q'.le_trans' _ _ _ (hN n hn) (Q'.le_of_eqv
    (RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.var 2))
      (.add (.add (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => B0.approx n | 1 => C.approx n | _ => epsilon)))

private theorem rc_double_regroup (a b : RC) :
    RCadd (RCadd a b) (RCadd a b) = RCadd (RCadd a a) (RCadd b b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B0
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))
      (.add (.add (.var 0) (.var 0)) (.add (.var 1) (.var 1))) (by decide)
      (fun | 0 => A.approx n | _ => B0.approx n)))

/-- Linear cancellation, valid also at zero norm and without deciding its sign. -/
theorem norm_budget_cancel (a c : RC)
    (h : RCle a (RCadd (RCadd c c)
      (RCadd (RCscale (HalfPow.half^2) a) (RCscale (HalfPow.half^2) a)))) :
    RCle a (RCscale 4 c) := by
  have hh := RCadd_le_add h h
  rw [rc_double_regroup, four_copies, four_copies, RCscale_RCscale,
    scale_congr (a := 4*(HalfPow.half^2)) (b := 1) (by decide) a, RCscale_one] at hh
  exact rc_add_cancel a (RCscale 4 c) a hh

theorem resolvent_norm_centered_bound (x : Completion) :
    RCle (B (resolvent x) (resolvent x)) (RCscale 4 (B (center x) (center x))) := by
  have ht := centered_norm_decay (resolvent x) 2
  rw [resolvent_centered] at ht
  have h := RCle_trans (norm_add_bound (center x) (twoStepTransfer (resolvent x)))
    (RCadd_le_add (RCle_refl _) (RCadd_le_add ht ht))
  rw [← resolvent_equation] at h
  exact norm_budget_cancel _ _ h

/-- A uniform operator bound on the current carrier, not uniform in coupling or spacing. -/
theorem resolvent_norm_bound (x : Completion) :
    RCle (B (resolvent x) (resolvent x)) (RCscale 4 (B x x)) :=
  RCle_trans (resolvent_norm_centered_bound x)
    (RCscale_mono (by decide : (0 : Q') ≤ 4) (center_norm_le x))

theorem centered_eq_of_defect_eq (x y : Completion)
    (hx : center x = x) (hy : center y = y) (h : defect x = defect y) : x = y := by
  have he := congrArg resolvent h
  rw [resolvent_left_inverse, resolvent_left_inverse, hx, hy] at he
  exact he

private theorem rc_sub_swap (a b c d : RC) :
    RCsub (RCsub a b) (RCsub c d) = RCsub (RCsub a c) (RCsub b d) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B0
  refine Quotient.inductionOn₂ c d ?_
  intro C D
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 2) (.neg (.var 3)))))
      (.add (.add (.var 0) (.neg (.var 2))) (.neg (.add (.var 1) (.neg (.var 3)))))
      (by decide) (fun | 0 => A.approx n | 1 => B0.approx n | 2 => C.approx n | _ => D.approx n)))

theorem defect_sub (x y : Completion) : defect (completedSub x y) = completedSub (defect x) (defect y) := by
  unfold defect twoStepTransfer
  rw [completedTime_sub]
  apply completed_eq_of_pairings
  intro z
  simp only [completedInner_sub_left]
  exact rc_sub_swap _ _ _ _

theorem resolvent_sub (x y : Completion) :
    resolvent (completedSub x y) = completedSub (resolvent x) (resolvent y) := by
  apply centered_eq_of_defect_eq _ _ (resolvent_centered _)
  · rw [center_sub, resolvent_centered, resolvent_centered]
  · rw [resolvent_right_inverse, defect_sub, resolvent_right_inverse,
      resolvent_right_inverse, center_sub]

theorem resolvent_add (x y : Completion) :
    resolvent (completedAdd x y) = completedAdd (resolvent x) (resolvent y) := by
  have h := congrArg (fun a => completedAdd a (resolvent y)) (resolvent_sub (completedAdd x y) y)
  change completedAdd (resolvent (completedSub (completedAdd x y) y)) (resolvent y) =
    completedAdd (completedSub (resolvent (completedAdd x y)) (resolvent y)) (resolvent y) at h
  rw [sub_add_right_cancel, completedSub_add_cancel] at h
  exact h.symm

theorem defect_realSmul (s : CReal) (cs : QCauchy s.approx) (x : Completion) :
    defect (completedRealSmul s cs x) = completedRealSmul s cs (defect x) := by
  unfold defect twoStepTransfer
  rw [completedTime_realSmul, completedRealSmul_sub]

/-- Linearity keeps the supplied constructive-real modulus as data. -/
theorem resolvent_realSmul (s : CReal) (cs : QCauchy s.approx) (x : Completion) :
    resolvent (completedRealSmul s cs x) = completedRealSmul s cs (resolvent x) := by
  apply centered_eq_of_defect_eq _ _ (resolvent_centered _)
  · rw [center_realSmul, resolvent_centered]
  · rw [resolvent_right_inverse, defect_realSmul, resolvent_right_inverse, center_realSmul]

theorem resolvent_distance_bound (x y : Completion) :
    RCle (completedDist (resolvent x) (resolvent y)) (RCscale 4 (completedDist x y)) := by
  unfold completedDist
  rw [← resolvent_sub]
  exact resolvent_norm_bound (completedSub x y)

theorem defect_zero : defect completedZero = completedZero := by
  unfold defect twoStepTransfer
  rw [completedTime_zeroState, completedSub_self]

theorem resolvent_zero : resolvent completedZero = completedZero := by
  have h := resolvent_left_inverse completedZero
  rw [defect_zero, center_zero] at h
  exact h

/-- The inverse cannot erase a nonzero centered excitation. -/
theorem resolvent_ne_zero (x : UnitComplement) (hx : x.val ≠ completedZero) :
    resolvent x.val ≠ completedZero := by
  intro h
  have hd := congrArg defect h
  rw [resolvent_right_inverse, (center_fixed_iff x.val).mpr x.property, defect_zero] at hd
  exact hx hd

end YMGap.Continuum.BF4ExactSlabThermodynamicResolventBound

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventBound.norm_budget_cancel
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventBound.resolvent_norm_centered_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventBound.resolvent_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventBound.centered_eq_of_defect_eq
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventBound.defect_sub
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventBound.resolvent_sub
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventBound.resolvent_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventBound.defect_realSmul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventBound.resolvent_realSmul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventBound.resolvent_distance_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventBound.defect_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventBound.resolvent_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventBound.resolvent_ne_zero
