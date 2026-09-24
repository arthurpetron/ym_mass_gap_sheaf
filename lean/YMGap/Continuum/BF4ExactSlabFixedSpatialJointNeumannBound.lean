/-
# Intrinsic bound for the SAME discrete inverse

The actual strict form bound gives a source-independent squared-norm bound
`||inverse x||^2 <= (1-q)^(-2) ||center x||^2` at fixed nome and width.
The proof completes the nonnegative square `||z-g*(I-T^2)z||^2`, with
`g=1/(1-q)`. It never divides by a vector norm or decides whether it is zero.
Together with inverse linearity this bounds distances in the actual carrier.
This is not a spatial/spacing-uniform bound or a Hamiltonian resolvent.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannAlgebra

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointVacuumProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedGap
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap
  (twoStepRate twoStepRate_lt_one)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation (residual)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannInverse
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannAlgebra
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedCompleteness (completedDistSq)
open YMGap.Continuum.BF4SpatialUnionBilinear (rc_add_zero)
open YMGap.Continuum.MeanExpConvexProgress (le_of_add_le_add_right)

private theorem rc_scale_congr {a b : Q'} (h : a.eqv b) (x : RC) :
    RCscale a x = RCscale b x := by
  refine Quotient.inductionOn x ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_eqv_congr_right _ _ _ h))

private theorem rc_zero_add (x : RC) : RCadd RCzero x = x := by
  refine Quotient.inductionOn x ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_trans _ _ _ (Q'.add_comm_eqv 0 (X.approx n))
      (QPoly.q_add_zero_eqv (X.approx n))))

private theorem rc_add_cancel (a b c : RC)
    (h : RCle (RCadd a c) (RCadd b c)) : RCle a b := by
  revert h
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C h epsilon he
  obtain ⟨N, hN⟩ := h epsilon he
  refine ⟨N, fun n hn => ?_⟩
  apply le_of_add_le_add_right (c := C.approx n)
  exact Q'.le_trans' _ _ _ (hN n hn) (Q'.le_of_eqv
    (RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.var 2))
      (.add (.add (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => B.approx n | 1 => C.approx n | _ => epsilon)))

private theorem deficit_lower (r : Q') (norm form : RC)
    (h : RCle form (RCscale r norm)) :
    RCle (RCscale (1-r) norm) (RCsub norm form) := by
  revert h
  refine Quotient.inductionOn₂ norm form ?_
  intro N F h epsilon he
  obtain ⟨index, hN⟩ := h epsilon he
  refine ⟨index, fun n hn => ?_⟩
  have hf : F.approx n ≤ r * N.approx n + epsilon := hN n hn
  have hsum := Q'.add_le_add_left (N.approx n) _ _ (Q'.neg_le_neg_add hf)
  change (1-r)*N.approx n ≤ (N.approx n + -F.approx n) + epsilon
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (RingNormaliser.poly_identity_of_normal_eq
      (.mul (.add (.const 1) (.neg (.var 0))) (.var 1))
      (.add (.var 1) (.neg (.mul (.var 0) (.var 1)))) (by decide)
      (fun | 0 => r | _ => N.approx n)))
    (Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv (Q'.add_assoc_eqv _ _ _)))

/-- The completed-square identity, with the two mixed terms retained. -/
private theorem square_identity (g : Q') (norm cross image : RC) :
    RCadd
      (RCsub (RCsub norm (RCscale g cross))
        (RCsub (RCscale g cross) (RCscale g (RCscale g image))))
      (RCadd (RCscale g cross) (RCscale g cross)) =
      RCadd (RCscale (g*g) image) norm := by
  refine Quotient.inductionOn₃ norm cross image ?_
  intro N P M
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add
        (.add (.add (.var 0) (.neg (.mul (.var 3) (.var 1))))
          (.neg (.add (.mul (.var 3) (.var 1))
            (.neg (.mul (.var 3) (.mul (.var 3) (.var 2)))))))
        (.add (.mul (.var 3) (.var 1)) (.mul (.var 3) (.var 1))))
      (.add (.mul (.mul (.var 3) (.var 3)) (.var 2)) (.var 0))
      (by decide)
      (fun | 0 => N.approx n | 1 => P.approx n | 2 => M.approx n | _ => g)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "V" => JointCompletion hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width
local notation "U" => jointCompletedUnit hw0 hw1 width
local notation "T" => jointCompletedTime hw0 hw1 width
local notation "R" => residual hw0 hw1 width
local notation "q" => twoStepRate hw0 hw1 width

/-- Explicit operator constant; only nome and width enter, never the source. -/
def inverseNormConstant : Q' :=
  Q'.divPos 1 (1-q) (HKPos.one_sub_pos (twoStepRate_lt_one hw0 hw1 width))

theorem inverseNormConstant_positive : (0 : Q') < inverseNormConstant hw0 hw1 width :=
  Q'.divPos_pos _ _ _ (by decide)

/-- Coercivity of the actual discrete residual on the actual unit complement. -/
theorem residual_form_bound (x : V) (hx : B x U = RCzero) :
    RCle (RCscale (1-q) (B x x)) (B x (R x)) := by
  rw [residual, completedInner_sub_right]
  have h := completed_twoStep_form_gap hw0 hw1 width x hx
  have hscale (a : RC) :
      RCmul (Quotient.mk crealSetoid (ofQ' q)) a = RCscale q a := by
    refine Quotient.inductionOn a ?_
    exact fun _ => rfl
  rw [hscale] at h
  exact deficit_lower q _ _ h

/-- Completing a square gives the sharp reciprocal-margin squared bound.
No division by the vector norm, Cauchy--Schwarz cancellation or sign split. -/
theorem residual_norm_bound (x : V) (hx : B x U = RCzero) :
    RCle (B x x)
      (RCscale (inverseNormConstant hw0 hw1 width * inverseNormConstant hw0 hw1 width)
        (B (R x) (R x))) := by
  let g := inverseNormConstant hw0 hw1 width
  have hg : (0 : Q') ≤ g := Q'.le_of_lt (inverseNormConstant_positive hw0 hw1 width)
  have hcancel : (g*(1-q)).eqv 1 := Q'.divPos_mul_eqv _ _ _
  have hco := RCscale_mono hg (residual_form_bound hw0 hw1 width x hx)
  rw [RCscale_RCscale, rc_scale_congr hcancel, RCscale_one] at hco
  have hs := completedInner_nonnegative hw0 hw1 width
    (completedSub hw0 hw1 width x (completedSmul hw0 hw1 width g (R x)))
  rw [completedInner_sub_left, completedInner_sub_right, completedInner_sub_right,
    completedInner_smul_left, completedInner_smul_right, completedInner_smul_right,
    completedInner_smul_left, completedInner_symm hw0 hw1 width (R x) x] at hs
  have hp := RCadd_le_add hs (RCle_refl
    (RCadd (RCscale g (B x (R x))) (RCscale g (B x (R x)))))
  rw [rc_zero_add, square_identity] at hp
  exact rc_add_cancel _ _ _ (RCle_trans (RCadd_le_add hco hco) hp)

theorem inverse_norm_centered_bound (x : V) :
    RCle (B (inverse hw0 hw1 width x) (inverse hw0 hw1 width x))
      (RCscale (inverseNormConstant hw0 hw1 width * inverseNormConstant hw0 hw1 width)
        (B (center hw0 hw1 width x) (center hw0 hw1 width x))) := by
  have h := residual_norm_bound hw0 hw1 width (inverse hw0 hw1 width x)
    (inverse_orthogonal hw0 hw1 width x)
  rwa [inverse_residual] at h

/-- Source-independent actual-norm control, still dependent on nome and width. -/
theorem inverse_norm_bound (x : V) :
    RCle (B (inverse hw0 hw1 width x) (inverse hw0 hw1 width x))
      (RCscale (inverseNormConstant hw0 hw1 width * inverseNormConstant hw0 hw1 width)
        (B x x)) :=
  RCle_trans (inverse_norm_centered_bound hw0 hw1 width x)
    (RCscale_mono (Q'.mul_nonneg _ _
      (Q'.le_of_lt (inverseNormConstant_positive hw0 hw1 width))
      (Q'.le_of_lt (inverseNormConstant_positive hw0 hw1 width)))
      (center_norm_le hw0 hw1 width x))

/-- The intrinsic norm estimate controls differences of actual quotient states. -/
theorem inverse_distance_bound (x y : V) :
    RCle (completedDistSq hw0 hw1 width
        (inverse hw0 hw1 width x) (inverse hw0 hw1 width y))
      (RCscale (inverseNormConstant hw0 hw1 width * inverseNormConstant hw0 hw1 width)
        (completedDistSq hw0 hw1 width x y)) := by
  unfold completedDistSq
  rw [← inverse_sub]
  exact inverse_norm_bound hw0 hw1 width (completedSub hw0 hw1 width x y)

/-- An approximate centered preimage has an actual error bounded by its
residual error. The exact solution and source remain on the SAME carrier. -/
theorem preimage_error_bound (x y : V) (hy : B y U = RCzero) :
    RCle (completedDistSq hw0 hw1 width y (inverse hw0 hw1 width x))
      (RCscale (inverseNormConstant hw0 hw1 width * inverseNormConstant hw0 hw1 width)
        (completedDistSq hw0 hw1 width (R y) (center hw0 hw1 width x))) := by
  have hc : B (completedSub hw0 hw1 width y (inverse hw0 hw1 width x)) U = RCzero := by
    rw [completedInner_sub_left, hy, inverse_orthogonal]
    rfl
  have h := residual_norm_bound hw0 hw1 width
    (completedSub hw0 hw1 width y (inverse hw0 hw1 width x)) hc
  rw [residual_sub, inverse_residual] at h
  exact h

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannBound

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannBound.inverseNormConstant
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannBound.inverseNormConstant_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannBound.residual_form_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannBound.residual_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannBound.inverse_norm_centered_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannBound.inverse_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannBound.inverse_distance_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannBound.preimage_error_bound
