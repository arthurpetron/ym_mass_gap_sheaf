/-
# Quantitative relaxation for the actual spatial union transfer

Iterating the existing one-step squared-norm estimate gives q^n decay,
where q is the SAME coupling-dependent two-step form rate. Centering and
unit projection identify this with distance to the actual stationary part.
The supplied representative's scalar Cauchy data compute a ceiling and a
tolerance modulus. Neither quotient representatives nor a uniform nome
bound are selected. This is discrete fixed-spacing relaxation, not a
continuum Hamiltonian theorem.
-/

import YMGap.Continuum.BF4SpatialUnionCompletedDistance
import YMGap.Continuum.BF4SpatialUnionStationary
import YMGap.Continuum.BoundedTransferCalculus
import YMGap.Continuum.PositiveContractionResidual

namespace YMGap.Continuum.BF4SpatialUnionRelaxation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4SpatialUnionSeminorm
open YMGap.Continuum.BF4SpatialUnionPairingData
open YMGap.Continuum.BF4SpatialUnionGeometry
open YMGap.Continuum.BF4SpatialUnionBilinear
open YMGap.Continuum.BF4SpatialUnionUnitProjection
open YMGap.Continuum.BF4SpatialUnionUnitComplement
open YMGap.Continuum.BF4SpatialUnionCentered
open YMGap.Continuum.BF4SpatialUnionCompletedDistance
open YMGap.Continuum.CRealSeminormPairingCompletion
  (representativeInner representativeInnerCauchy)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy
  (scalarCeiling scalarCeiling_nonnegative scalar_approx_le_ceiling)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap
  (twoStepRate twoStepRate_positive twoStepRate_lt_one)
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "PD" => pairingData hw0 hw1 hsmall hd hs
local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs
local notation "C" => center hw0 hw1 hsmall hd hs
local notation "P" => unitProjection hw0 hw1 hsmall hd hs
local notation "q" => twoStepRate w hd

theorem centered_norm_one_step (x : V) :
    RCle (B (T 1 (C x)) (T 1 (C x))) (RCscale q (B (C x) (C x))) :=
  unitComplement_oneStep_norm_gap hw0 hw1 hsmall hd hs (centeredState hw0 hw1 hsmall hd hs x)

/-- The rate remains coupling-dependent and quantifies over every completed vector. -/
theorem centered_norm_decay (x : V) : ∀ n : Nat,
    RCle (B (T n (C x)) (T n (C x))) (RCscale (q^n) (B (C x) (C x)))
  | 0 => by
      rw [completedTime_zero, show q^0 = (1 : Q') from rfl, RCscale_one]
      exact RCle_refl _
  | n+1 => by
      have hstep := centered_norm_one_step hw0 hw1 hsmall hd hs (T n x)
      rw [← completedTime_center, ← completedTime_add, Nat.add_comm 1 n] at hstep
      have h := RCle_trans hstep
        (RCscale_mono (Q'.le_of_lt (twoStepRate_positive hw0 hd)) (centered_norm_decay x n))
      rw [RCscale_RCscale] at h
      exact h

theorem relaxation_difference (n : Nat) (x : V) :
    completedSub hw0 hw1 hsmall hd hs (T n x) (P x) = T n (C x) := by
  unfold center
  rw [completedTime_sub, time_unitProjection]

theorem relaxation_centered_bound (n : Nat) (x : V) :
    RCle (completedDist hw0 hw1 hsmall hd hs (T n x) (P x))
      (RCscale (q^n) (B (C x) (C x))) := by
  unfold completedDist
  rw [relaxation_difference]
  exact centered_norm_decay hw0 hw1 hsmall hd hs x n

theorem relaxation_norm_bound (n : Nat) (x : V) :
    RCle (completedDist hw0 hw1 hsmall hd hs (T n x) (P x)) (RCscale (q^n) (B x x)) :=
  RCle_trans (relaxation_centered_bound hw0 hw1 hsmall hd hs n x)
    (RCscale_mono (Q'.pow_nonneg _ (Q'.le_of_lt (twoStepRate_positive hw0 hd)) _)
      (center_norm_le hw0 hw1 hsmall hd hs x))

def normCap (X : (D).Cauchy) : Q' :=
  scalarCeiling (representativeInner PD X X) (representativeInnerCauchy PD X X)

theorem normCap_nonnegative (X : (D).Cauchy) : (0 : Q') ≤ normCap hw0 hw1 hsmall hd hs X :=
  scalarCeiling_nonnegative _ _

private theorem scalar_le_ceiling (s : CReal) (cs : QCauchy s.approx) :
    leEv s (ofQ' (scalarCeiling s cs)) := by
  intro epsilon he
  refine ⟨cs.M 1, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ (Q'.le_abs_self _) (scalar_approx_le_ceiling s cs n hn))
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))

theorem norm_le_cap (X : (D).Cauchy) :
    RCle (B (Quotient.mk (D).completionSetoid X) (Quotient.mk (D).completionSetoid X))
      (Quotient.mk crealSetoid (ofQ' (normCap hw0 hw1 hsmall hd hs X))) := scalar_le_ceiling _ _

def relaxationModulus (X : (D).Cauchy) (epsilon : Q') : Nat :=
  geometricCutoff q (normCap hw0 hw1 hsmall hd hs X) epsilon

theorem relaxation_small (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : relaxationModulus hw0 hw1 hsmall hd hs X epsilon ≤ n) :
    RCle (completedDist hw0 hw1 hsmall hd hs
      (T n (Quotient.mk (D).completionSetoid X)) (P (Quotient.mk (D).completionSetoid X)))
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  have h := RCle_trans
    (relaxation_norm_bound hw0 hw1 hsmall hd hs n (Quotient.mk (D).completionSetoid X))
    (RCscale_mono (Q'.pow_nonneg _ (Q'.le_of_lt (twoStepRate_positive hw0 hd)) _)
      (norm_le_cap hw0 hw1 hsmall hd hs X))
  refine RCle_trans h ?_
  exact leEv_le_ofQ'_of_approx_le (fun _ => geometric_bound
    (Q'.le_of_lt (twoStepRate_positive hw0 hd)) (twoStepRate_lt_one hw0 hd hs)
    (normCap_nonnegative hw0 hw1 hsmall hd hs X) he n hn)

/-- The actual threshold is data, not an existentially selected natural number. -/
def relaxationCertificate (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    {N : Nat // ∀ n, N ≤ n → RCle
      (completedDist hw0 hw1 hsmall hd hs (T n (Quotient.mk (D).completionSetoid X))
        (P (Quotient.mk (D).completionSetoid X))) (Quotient.mk crealSetoid (ofQ' epsilon))} :=
  ⟨relaxationModulus hw0 hw1 hsmall hd hs X epsilon, relaxation_small hw0 hw1 hsmall hd hs X epsilon he⟩

end YMGap.Continuum.BF4SpatialUnionRelaxation

#print axioms YMGap.Continuum.BF4SpatialUnionRelaxation.centered_norm_one_step
#print axioms YMGap.Continuum.BF4SpatialUnionRelaxation.centered_norm_decay
#print axioms YMGap.Continuum.BF4SpatialUnionRelaxation.relaxation_difference
#print axioms YMGap.Continuum.BF4SpatialUnionRelaxation.relaxation_centered_bound
#print axioms YMGap.Continuum.BF4SpatialUnionRelaxation.relaxation_norm_bound
#print axioms YMGap.Continuum.BF4SpatialUnionRelaxation.normCap
#print axioms YMGap.Continuum.BF4SpatialUnionRelaxation.normCap_nonnegative
#print axioms YMGap.Continuum.BF4SpatialUnionRelaxation.norm_le_cap
#print axioms YMGap.Continuum.BF4SpatialUnionRelaxation.relaxationModulus
#print axioms YMGap.Continuum.BF4SpatialUnionRelaxation.relaxation_small
#print axioms YMGap.Continuum.BF4SpatialUnionRelaxation.relaxationCertificate
