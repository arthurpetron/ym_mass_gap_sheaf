/-
# Quantitative decay of ORIGINAL residuals on the actual T2 range

The existing energy inequality for T2 also says
  ||T2 z||^2 + ||(I-T2)z||^2 <= ||z||^2.
Thus D=I-T2 is a contraction. Its successive T2-responses decrease,
and finite telescoping proves n*||D^n T2 x||^2 <= ||x||^2.
At n=2^k the range-approximation residual is at most 2^(-k)||x||^2.
A supplied original preimage representative computes a degree threshold.

This proves actual range residual decay, not a density premise or decay
on every original vector. No inverse or alternative carrier is constructed.
Fixed SU(2) nome and spacing; full-space zero-time continuity and the
physical Hamiltonian/continuum/Clay conclusions remain open.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicRangeApproximation
import YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy

namespace YMGap.Continuum.BF4ExactSlabThermodynamicRangeDefectEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.SU3CharFactor (ofNat_nonneg)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicResolvent (defect)
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventBound (defect_sub)
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments
open YMGap.Continuum.BF4ExactSlabThermodynamicRangeApproximation
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy
  (time_dissipation half_power_normalizes rangeModulus scaled_norm_small)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes (time generator_zero)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords (scale_nat_succ add_assoc add_comm)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments (scale_zero)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional (rc_add_zero rc_zero_add)
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial (scale_congr)

local notation "B" => completedInner
local notation "point" X => Quotient.mk seminorm.completionSetoid X
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

theorem defect_energy (x : Completion) :
    RCle (RCadd (B (twoStepTransfer x) (twoStepTransfer x)) (B (defect x) (defect x))) (B x x) := by
  have h := time_dissipation 0 1 x
  change RCle (RCadd (completedDist (time 0 1 x) x) (B (time 0 1 x) (time 0 1 x))) (B x x) at h
  have ht : time 0 1 x = twoStepTransfer x := generator_zero x
  rw [ht, completedDist_symm] at h
  change RCle (RCadd (B (defect x) (defect x)) (B (twoStepTransfer x) (twoStepTransfer x))) (B x x) at h
  rw [add_comm] at h
  exact h

theorem defect_contraction (x : Completion) : RCle (B (defect x) (defect x)) (B x x) := by
  have h := RCadd_le_add (completedInner_nonnegative (twoStepTransfer x))
    (RCle_refl (B (defect x) (defect x)))
  rw [rc_zero_add] at h
  exact RCle_trans h (defect_energy x)

theorem defect_distance_contraction (x y : Completion) :
    RCle (completedDist (defect x) (defect y)) (completedDist x y) := by
  unfold completedDist
  rw [← defect_sub]
  exact defect_contraction (completedSub x y)

theorem defectPower_distance_contraction (n : Nat) (x y : Completion) :
    RCle (completedDist (defectPower n x) (defectPower n y)) (completedDist x y) := by
  induction n with
  | zero => exact RCle_refl _
  | succ n ih => exact RCle_trans (defect_distance_contraction (defectPower n x) (defectPower n y)) ih

def rangeResidual (n : Nat) (x : Completion) : RC :=
  B (twoStepTransfer (defectPower n x)) (twoStepTransfer (defectPower n x))

theorem rangeResidual_succ (n : Nat) (x : Completion) :
    RCle (rangeResidual (n+1) x) (rangeResidual n x) := by
  unfold rangeResidual
  change RCle (B (completedTime 2 (defect (defectPower n x)))
    (completedTime 2 (defect (defectPower n x)))) _
  rw [time_defect]
  exact defect_contraction (twoStepTransfer (defectPower n x))

theorem residual_weighted_energy (n : Nat) (x : Completion) :
    RCle (RCadd (RCscale (Q'.ofNat n) (rangeResidual n x))
      (B (defectPower n x) (defectPower n x))) (B x x) := by
  induction n with
  | zero =>
      rw [scale_congr (by decide : Q'.eqv (Q'.ofNat 0) 0), scale_zero, rc_zero_add]
      exact RCle_refl _
  | succ n ih =>
      have h := RCle_trans (RCadd_le_add
        (RCle_refl (RCscale (Q'.ofNat n) (rangeResidual n x)))
        (defect_energy (defectPower n x))) ih
      change RCle (RCadd (RCscale (Q'.ofNat n) (rangeResidual n x))
        (RCadd (rangeResidual n x) (B (defectPower (n+1) x) (defectPower (n+1) x)))) (B x x) at h
      rw [← add_assoc, ← scale_nat_succ] at h
      exact RCle_trans (RCadd_le_add
        (RCscale_mono (ofNat_nonneg (n+1)) (rangeResidual_succ n x)) (RCle_refl _)) h

theorem residual_weighted_bound (n : Nat) (x : Completion) :
    RCle (RCscale (Q'.ofNat n) (rangeResidual n x)) (B x x) := by
  have h := RCadd_le_add (RCle_refl (RCscale (Q'.ofNat n) (rangeResidual n x)))
    (completedInner_nonnegative (defectPower n x))
  rw [rc_add_zero] at h
  exact RCle_trans h (residual_weighted_energy n x)

theorem rangeResidual_moment (n : Nat) (x : Completion) :
    rangeResidual n x = mixedMoment (twoStepTransfer x) 0 (n+n) := by
  unfold rangeResidual twoStepTransfer
  rw [time_defectPower, residual_norm_moment]

theorem range_residual_dyadic_bound (k : Nat) (x : Completion) :
    RCle (mixedMoment (twoStepTransfer x) 0 (2^k+2^k)) (RCscale (HalfPow.half^k) (B x x)) := by
  have h := RCscale_mono (Q'.pow_nonneg HalfPow.half HalfPow.half_nonneg k) (residual_weighted_bound (2^k) x)
  have hn : Q'.eqv (HalfPow.half^k * Q'.ofNat (2^k)) 1 := half_power_normalizes k
  rw [RCscale_RCscale, scale_congr hn, RCscale_one, rangeResidual_moment] at h
  exact h

def residualDegree (X : seminorm.Cauchy) (epsilon : Q') : Nat := 2^(rangeModulus X epsilon)

theorem range_residual_small (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    RCle (mixedMoment (twoStepTransfer (point X)) 0
      (residualDegree X epsilon + residualDegree X epsilon)) (rat epsilon) :=
  RCle_trans (range_residual_dyadic_bound (rangeModulus X epsilon) (point X))
    (scaled_norm_small X epsilon he (rangeModulus X epsilon) (Nat.le_refl _))

end YMGap.Continuum.BF4ExactSlabThermodynamicRangeDefectEnergy

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRangeDefectEnergy.defect_energy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRangeDefectEnergy.defect_contraction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRangeDefectEnergy.defect_distance_contraction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRangeDefectEnergy.defectPower_distance_contraction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRangeDefectEnergy.rangeResidual
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRangeDefectEnergy.rangeResidual_succ
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRangeDefectEnergy.residual_weighted_energy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRangeDefectEnergy.residual_weighted_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRangeDefectEnergy.rangeResidual_moment
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRangeDefectEnergy.range_residual_dyadic_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRangeDefectEnergy.residualDegree
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicRangeDefectEnergy.range_residual_small
