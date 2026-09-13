/-
# Quantitative relaxation to the ORIGINAL completed unit projection

Reflection symmetry identifies the one-step squared norm with the two-step
form. The proved completed form gap therefore gives a factor 1/2 per step
on squared norms in the unit complement. Iteration and the exact time/unit
projection identities give

  ||T_n x - P x||^2 <= (1/2)^n ||center x||^2 <= (1/2)^n ||x||^2.

For every supplied Cauchy representative, its existing inner-product modulus
computes a rational ceiling and an explicit time threshold for any positive
tolerance. No quotient representative is selected. The original SU(2) law,
nome 1/1024 and lattice spacing remain fixed; no nonzero excitation or
continuum generator is asserted.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGap
import YMGap.Continuum.BoundedTransferCalculus

namespace YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar
open YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGap
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy (scalarCeiling scalarCeiling_nonnegative scalar_approx_le_ceiling)
open YMGap.Continuum.RegularLinearGeometricModulus

local notation "D" => seminorm
local notation "B" => completedInner

theorem completedTime_projection (lag : Nat) (x : Completion) :
    completedTime lag (unitProjection x) = unitProjection x := by
  refine Quotient.inductionOn x ?_
  intro X
  rw [unitProjection_mk, completedTime_realSmul, completedTime_unit]

theorem projection_completedTime (lag : Nat) (x : Completion) :
    unitProjection (completedTime lag x) = unitProjection x := by
  apply completed_eq_of_pairings
  intro y
  rw [unitProjection_pairing, completedTime_mean, unitProjection_pairing]

theorem centered_norm_one_step (x : Completion) :
    RCle (B (completedTime 1 (center x)) (completedTime 1 (center x)))
      (RCscale HalfPow.half (B (center x) (center x))) := by
  rw [completedTime_moments]
  exact centered_twoStep_form_gap x

theorem centered_norm_decay (x : Completion) : ∀ n : Nat,
    RCle (B (completedTime n (center x)) (completedTime n (center x)))
      (RCscale (HalfPow.half^n) (B (center x) (center x)))
  | 0 => by rw [completedTime_zero, show HalfPow.half^0 = (1 : Q') from rfl, RCscale_one]; exact RCle_refl _
  | n+1 => by
      have hstep := centered_norm_one_step (completedTime n x)
      rw [← completedTime_center, completedTime_comp] at hstep
      have h := RCle_trans hstep (RCscale_mono HalfPow.half_nonneg (centered_norm_decay x n))
      rw [RCscale_RCscale] at h
      exact h

theorem completedTime_sub (lag : Nat) (x y : Completion) :
    completedTime lag (completedSub x y) = completedSub (completedTime lag x) (completedTime lag y) := by
  change completedTime lag (completedAdd x (completedSmul (-1) y)) =
    completedAdd (completedTime lag x) (completedSmul (-1) (completedTime lag y))
  rw [completedTime_add, completedTime_smul]

theorem relaxation_difference (lag : Nat) (x : Completion) :
    completedSub (completedTime lag x) (unitProjection x) = completedTime lag (center x) := by
  unfold center
  rw [completedTime_sub, completedTime_projection]

/-- Relative squared-distance decay, uniform over every completed vector. -/
theorem relaxation_centered_bound (lag : Nat) (x : Completion) :
    RCle (completedDist (completedTime lag x) (unitProjection x))
      (RCscale (HalfPow.half^lag) (B (center x) (center x))) := by
  unfold completedDist
  rw [relaxation_difference]
  exact centered_norm_decay x lag

theorem relaxation_norm_bound (lag : Nat) (x : Completion) :
    RCle (completedDist (completedTime lag x) (unitProjection x)) (RCscale (HalfPow.half^lag) (B x x)) :=
  RCle_trans (relaxation_centered_bound lag x)
    (RCscale_mono (Q'.pow_nonneg _ HalfPow.half_nonneg _) (center_norm_le x))

/-- The supplied representative and its computed pairing modulus produce this ceiling. -/
def normCap (X : (D).Cauchy) : Q' := scalarCeiling (representativeInner X X) (representativeInnerCauchy X X)

theorem normCap_nonnegative (X : (D).Cauchy) : (0 : Q') ≤ normCap X := scalarCeiling_nonnegative _ _

private theorem scalar_le_ceiling (s : CReal) (cs : QCauchy s.approx) : leEv s (ofQ' (scalarCeiling s cs)) := by
  intro epsilon he
  refine ⟨cs.M 1, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ (Q'.le_abs_self _) (scalar_approx_le_ceiling s cs n hn))
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))

theorem norm_le_cap (X : (D).Cauchy) :
    RCle (B (Quotient.mk (D).completionSetoid X) (Quotient.mk (D).completionSetoid X))
      (Quotient.mk crealSetoid (ofQ' (normCap X))) := scalar_le_ceiling _ _

def relaxationModulus (X : (D).Cauchy) (epsilon : Q') : Nat := geoOuterModulus (normCap X) epsilon

private theorem scaled_half_small (C : Q') (hC : (0 : Q') ≤ C) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : geoOuterModulus C epsilon ≤ n) : C*HalfPow.half^n ≤ epsilon := by
  have htwo : C ≤ Q'.ofNat 2*C := Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hC)
    (Q'.le_of_eqv (RingNormaliser.poly_identity_of_normal_eq (.add (.var 0) (.var 0))
      (.mul (.const 2) (.var 0)) (by decide) (fun _ => C)))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ htwo (Q'.pow_nonneg _ HalfPow.half_nonneg _))
    (geoTail_le_of_modulus C hC epsilon he n hn)

theorem relaxation_small (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : relaxationModulus X epsilon ≤ n) :
    RCle (completedDist (completedTime n (Quotient.mk (D).completionSetoid X))
      (unitProjection (Quotient.mk (D).completionSetoid X))) (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  have h := RCle_trans (relaxation_norm_bound n (Quotient.mk (D).completionSetoid X))
    (RCscale_mono (Q'.pow_nonneg _ HalfPow.half_nonneg _) (norm_le_cap X))
  refine RCle_trans h ?_
  change leEv (CReal.mul (ofQ' (HalfPow.half^n)) (ofQ' (normCap X))) (ofQ' epsilon)
  exact leEv_ofQ'_of_approx_ge (fun _ => Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
    (scaled_half_small (normCap X) (normCap_nonnegative X) epsilon he n hn))

/-- Witness-bearing convergence of the original orbit to the original projection. -/
def relaxationCertificate (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    {N : Nat // ∀ n, N ≤ n → RCle
      (completedDist (completedTime n (Quotient.mk (D).completionSetoid X))
        (unitProjection (Quotient.mk (D).completionSetoid X))) (Quotient.mk crealSetoid (ofQ' epsilon))} :=
  ⟨relaxationModulus X epsilon, relaxation_small X epsilon he⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation.completedTime_projection
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation.projection_completedTime
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation.centered_norm_one_step
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation.centered_norm_decay
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation.completedTime_sub
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation.relaxation_difference
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation.relaxation_centered_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation.relaxation_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation.normCap
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation.normCap_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation.norm_le_cap
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation.relaxationModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation.relaxation_small
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation.relaxationCertificate
