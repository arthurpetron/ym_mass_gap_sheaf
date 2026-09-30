/-
# Completed pairing continuity on the original all-nome Wilson carrier

The actual completed Cauchy--Schwarz inequality and rational bilinearity
give a two-slot pairing modulus from squared-distance control. No change of
carrier, nome, or width is involved.
-/

import YMGap.Continuum.BF4WilsonAllNomeDistance
import YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity

namespace YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity
  (smallTolerance smallTolerance_pos smallTolerance_budget signed_small_of_square pairingTolerance)
open YMGap.Continuum.ScaledGNSCompletionEstimates (mul_mono_left mul_mono_right)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "S" => completedSub hw0 hw1
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
  intro A B' h epsilon hepsilon
  obtain ⟨N,hN⟩ := h epsilon hepsilon
  refine ⟨N,fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _ (CReal.le_add_of_sub_le (hN n hn))
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)))

theorem rc_telescope (a b c : RC) : RCadd (RCsub a b) (RCsub b c)=RCsub a c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B' C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
      (Q'.add_eqv_congr_right _ _ _ (Q'.sub_add_cancel_eqv _ _))))

theorem reverse_sub (a b : RC) : RCsub b a=RCneg (RCsub a b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_symm (Q'.neg_sub_eqv _ _)))

theorem neg_add (a b : RC) : RCneg (RCadd a b)=RCadd (RCneg a) (RCneg b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.neg_add_eqv _ _))

private theorem rc_negative_one (a : RC) : RCscale (-1) a = RCneg a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 (A.approx n))
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (A.approx n)))))

theorem completedInner_sub_left (x y z : V) :
    B (S x y) z = RCsub (B x z) (B y z) := by
  unfold completedSub completedNeg RCsub
  rw [completedInner_add_left, completedInner_smul_left, rc_negative_one]

theorem completedInner_sub_right (x y z : V) :
    B x (S y z) = RCsub (B x y) (B x z) := by
  rw [completedInner_symm hw0 hw1 x, completedInner_sub_left,
    completedInner_symm hw0 hw1 y x, completedInner_symm hw0 hw1 z x]

theorem pairing_small (x y : V) (cap : Q') (hcap : (0 : Q')≤cap)
    (r : Q') (hr : (0 : Q')<r)
    (hx : RCle (B x x) (rat (smallTolerance cap hcap r)))
    (hy : RCle (B y y) (rat cap)) :
    RCle (B x y) (rat r) ∧ RCle (RCneg (B x y)) (rat r) := by
  apply small_of_square _ r hr
  have hd : RCnonneg (rat (smallTolerance cap hcap r)) :=
    leEv_ofQ'_of_approx_ge (fun _ => Q'.le_of_lt (smallTolerance_pos cap hcap hr))
  have hp := RCle_trans (completedInner_cauchySchwarz hw0 hw1 x y) (RCle_trans
    (mul_mono_right (completedInner_nonnegative hw0 hw1 y) hx) (mul_mono_left hd hy))
  exact RCle_trans hp (leEv_le_ofQ'_of_approx_le (fun _ => smallTolerance_budget cap hcap hr))

theorem pairing_difference_split (x x' y y' : V) :
    RCsub (B x y) (B x' y') =
      RCadd (B (S x x') y) (B (S y y') x') := by
  rw [completedInner_sub_left, completedInner_symm hw0 hw1 (S y y') x',
    completedInner_sub_right]
  exact (rc_telescope _ _ _).symm

/-- Both order errors with a computed tolerance on the SAME completion. -/
theorem pairing_close (x x' y y' : V) (cap : Q') (hcap : (0 : Q')≤cap)
    (epsilon : Q') (hepsilon : (0 : Q')<epsilon)
    (hx : RCle (completedDist hw0 hw1 x x') (rat (pairingTolerance cap hcap epsilon)))
    (hy : RCle (completedDist hw0 hw1 y y') (rat (pairingTolerance cap hcap epsilon)))
    (hynorm : RCle (B y y) (rat cap))
    (hxnorm : RCle (B x' x') (rat cap)) :
    RCle (B x y) (RCadd (B x' y') (rat epsilon)) ∧
    RCle (B x' y') (RCadd (B x y) (rat epsilon)) := by
  have hr := ExpNeg.half_mul_pos epsilon hepsilon
  have h1 := pairing_small hw0 hw1 (S x x') y cap hcap _ hr hx hynorm
  have h2 := pairing_small hw0 hw1 (S y y') x' cap hcap _ hr hy hxnorm
  have hsum : RCle (RCadd (rat (HalfPow.half*epsilon)) (rat (HalfPow.half*epsilon))) (rat epsilon) :=
    leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_eqv (ExpNeg.two_halves epsilon))
  constructor
  · apply sub_bound_to_order
    rw [pairing_difference_split hw0 hw1]
    exact RCle_trans (RCadd_le_add h1.1 h2.1) hsum
  · apply sub_bound_to_order
    rw [reverse_sub, pairing_difference_split hw0 hw1, neg_add]
    exact RCle_trans (RCadd_le_add h1.2 h2.2) hsum

end YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity

#print axioms YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity.small_of_square
#print axioms YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity.sub_bound_to_order
#print axioms YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity.rc_telescope
#print axioms YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity.reverse_sub
#print axioms YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity.neg_add
#print axioms YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity.completedInner_sub_left
#print axioms YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity.completedInner_sub_right
#print axioms YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity.pairing_small
#print axioms YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity.pairing_difference_split
#print axioms YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity.pairing_close
