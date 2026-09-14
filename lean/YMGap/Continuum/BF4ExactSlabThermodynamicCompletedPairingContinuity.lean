/-
# Explicit two-slot continuity of the ORIGINAL completed OS pairing

The original completed Cauchy--Schwarz inequality and bilinearity give
pairing error epsilon from squared-distance error epsilon^2/(8*(B+1)).
B bounds only the unchanged second and changed first vectors. The scalar
tolerance is reused from finite-form arithmetic; no finite-form pairing or
new physical hypothesis replaces the original completed pairing.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
import YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion
import YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity

namespace YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPairingContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity
  (smallTolerance smallTolerance_pos smallTolerance_budget signed_small_of_square pairingTolerance)
open YMGap.Continuum.ScaledGNSCompletionEstimates (mul_mono_left mul_mono_right)

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

theorem small_of_square (a : RC) (r : Q') (hr : (0 : Q') < r)
    (h : RCle (RCmul a a) (rat (HalfPow.half * (r*r)))) :
    RCle a (rat r) ∧ RCle (RCneg a) (rat r) := by
  revert h
  refine Quotient.inductionOn a ?_
  exact fun A h => signed_small_of_square A r hr h

theorem sub_bound_to_order (a b : RC) (e : Q')
    (h : RCle (RCsub a b) (rat e)) : RCle a (RCadd b (rat e)) := by
  revert h
  refine Quotient.inductionOn₂ a b ?_
  intro A B h epsilon hepsilon
  obtain ⟨N,hN⟩ := h epsilon hepsilon
  refine ⟨N,fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _ (CReal.le_add_of_sub_le (hN n hn))
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)))

theorem rc_telescope (a b c : RC) : RCadd (RCsub a b) (RCsub b c)=RCsub a c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
      (Q'.add_eqv_congr_right _ _ _ (Q'.sub_add_cancel_eqv _ _))))

theorem reverse_sub (a b : RC) : RCsub b a=RCneg (RCsub a b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_symm (Q'.neg_sub_eqv _ _)))

theorem neg_add (a b : RC) : RCneg (RCadd a b)=RCadd (RCneg a) (RCneg b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.neg_add_eqv _ _))

theorem pairing_small (x y : Completion) (B : Q') (hB : (0 : Q')≤B)
    (r : Q') (hr : (0 : Q')<r)
    (hx : RCle (completedInner x x) (rat (smallTolerance B hB r)))
    (hy : RCle (completedInner y y) (rat B)) :
    RCle (completedInner x y) (rat r) ∧ RCle (RCneg (completedInner x y)) (rat r) := by
  apply small_of_square _ r hr
  have hd : RCnonneg (rat (smallTolerance B hB r)) :=
    leEv_ofQ'_of_approx_ge (fun _ => Q'.le_of_lt (smallTolerance_pos B hB hr))
  have hp := RCle_trans (completedInner_cauchySchwarz x y) (RCle_trans
    (mul_mono_right (completedInner_nonnegative y) hx) (mul_mono_left hd hy))
  exact RCle_trans hp (leEv_le_ofQ'_of_approx_le (fun _ => smallTolerance_budget B hB hr))

theorem pairing_difference_split (x x' y y' : Completion) :
    RCsub (completedInner x y) (completedInner x' y')=
      RCadd (completedInner (completedSub x x') y) (completedInner (completedSub y y') x') := by
  rw [completedInner_sub_left,completedInner_symm (completedSub y y') x',completedInner_sub_right]
  exact (rc_telescope _ _ _).symm

/-- Both order errors, with an explicit squared-distance tolerance on the SAME carrier. -/
theorem pairing_close (x x' y y' : Completion) (B : Q') (hB : (0 : Q')≤B)
    (epsilon : Q') (hepsilon : (0 : Q')<epsilon)
    (hx : RCle (completedDist x x') (rat (pairingTolerance B hB epsilon)))
    (hy : RCle (completedDist y y') (rat (pairingTolerance B hB epsilon)))
    (hynorm : RCle (completedInner y y) (rat B))
    (hxnorm : RCle (completedInner x' x') (rat B)) :
    RCle (completedInner x y) (RCadd (completedInner x' y') (rat epsilon)) ∧
    RCle (completedInner x' y') (RCadd (completedInner x y) (rat epsilon)) := by
  have hr := ExpNeg.half_mul_pos epsilon hepsilon
  have h1 := pairing_small (completedSub x x') y B hB _ hr hx hynorm
  have h2 := pairing_small (completedSub y y') x' B hB _ hr hy hxnorm
  have hsum : RCle (RCadd (rat (HalfPow.half*epsilon)) (rat (HalfPow.half*epsilon))) (rat epsilon) :=
    leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_eqv (ExpNeg.two_halves epsilon))
  constructor
  · apply sub_bound_to_order
    rw [pairing_difference_split]
    exact RCle_trans (RCadd_le_add h1.1 h2.1) hsum
  · apply sub_bound_to_order
    rw [reverse_sub, pairing_difference_split,neg_add]
    exact RCle_trans (RCadd_le_add h1.2 h2.2) hsum

end YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPairingContinuity

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPairingContinuity.small_of_square
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPairingContinuity.sub_bound_to_order
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPairingContinuity.rc_telescope
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPairingContinuity.reverse_sub
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPairingContinuity.neg_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPairingContinuity.pairing_small
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPairingContinuity.pairing_difference_split
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPairingContinuity.pairing_close
