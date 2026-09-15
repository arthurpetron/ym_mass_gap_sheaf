/-
# Approximate T2 preimages and time zero on the ORIGINAL geometric T1 range

For T=the existing two-step transfer and D=I-T, nonnegative mixed moments
and m(0,n)=m(1,n)+m(0,n+1) give n*m(1,n)<=||x||^2 by finite telescoping.
But m(1,2n)=||D^n (completedTime 1 x)||^2: the existing GEOMETRIC one-step
operator supplies the half-time pairing, without identifying it with the
positive square root of T. Hence the existing finite partialPreimage has a
computed small residual on that actual geometric range. Its original Cauchy
representative is constructed, not selected or assumed to be an exact inverse.

The existing T2-range time-zero modulus and distance contraction then give
time-zero continuity of the actual positive-real-time action on the geometric
T1 range. This is not density of that range, full-space time zero, positivity
of geometric T1, or T1=A(1/2). No physical hypothesis or carrier is added.
Fixed SU(2) nome and spacing; physical Hamiltonian/continuum/Clay remain open.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicRangeDefectEnergy
import YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRangeZeroContinuity

namespace YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRangeContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.SU3CharFactor (ofNat_nonneg)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments
open YMGap.Continuum.BF4ExactSlabThermodynamicRangeApproximation
open YMGap.Continuum.BF4ExactSlabThermodynamicRangeDefectEnergy (residualDegree)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy
  (half_power_normalizes rangeModulus scaled_norm_small)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords (scale_nat_succ add_assoc)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments (scale_zero)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional (rc_add_zero rc_zero_add)
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial (scale_congr)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation (completedDist_three_segment)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup (realTimeAction_distance_contraction)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealLocalContinuity (localRadius localRadius_positive)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRangeZeroContinuity
  (oneTimeData twoStep_range_zero_bound)

local notation "B" => completedInner
local notation "point" X => Quotient.mk seminorm.completionSetoid X
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

theorem moment_defect_succ_le (x : Completion) (k n : Nat) :
    RCle (mixedMoment x k (n+1)) (mixedMoment x k n) := by
  have h := RCadd_le_add (mixedMoment_nonnegative x (k+1) n)
    (RCle_refl (mixedMoment x k (n+1)))
  rw [rc_zero_add, ← mixedMoment_split] at h
  exact h

theorem moment_defect_antitone (x : Completion) (k : Nat) {m n : Nat} (h : m ≤ n) :
    RCle (mixedMoment x k n) (mixedMoment x k m) := by
  induction n with
  | zero => have hm : m=0 := Nat.eq_zero_of_le_zero h; subst m; exact RCle_refl _
  | succ n ih =>
      by_cases he : m=n+1
      · subst m; exact RCle_refl _
      · exact RCle_trans (moment_defect_succ_le x k n) (ih (by omega))

/-- Finite telescoping retains the terminal moment; no spectral measure is used. -/
theorem moment_weighted_energy (n : Nat) (x : Completion) :
    RCle (RCadd (RCscale (Q'.ofNat n) (mixedMoment x 1 n)) (mixedMoment x 0 n)) (B x x) := by
  induction n with
  | zero =>
      rw [scale_congr (by decide : Q'.eqv (Q'.ofNat 0) 0), scale_zero, rc_zero_add, mixedMoment_zero]
      exact RCle_refl _
  | succ n ih =>
      rw [mixedMoment_split x 0 n, ← add_assoc, ← scale_nat_succ] at ih
      exact RCle_trans (RCadd_le_add
        (RCscale_mono (ofNat_nonneg (n+1)) (moment_defect_succ_le x 1 n)) (RCle_refl _)) ih

theorem moment_weighted_bound (n : Nat) (x : Completion) :
    RCle (RCscale (Q'.ofNat n) (mixedMoment x 1 n)) (B x x) := by
  have h := RCadd_le_add (RCle_refl (RCscale (Q'.ofNat n) (mixedMoment x 1 n)))
    (mixedMoment_nonnegative x 0 n)
  rw [rc_add_zero] at h
  exact RCle_trans h (moment_weighted_energy n x)

theorem oneStep_residual_moment (n : Nat) (x : Completion) :
    mixedMoment (completedTime 1 x) 0 (n+n) = mixedMoment x 1 (n+n) := by
  rw [mixedMoment_halfTime x 1 (n+n)]
  unfold mixedMoment
  rw [completedTime_zero]

theorem oneStep_residual_weighted (n : Nat) (x : Completion) :
    RCle (RCscale (Q'.ofNat n) (mixedMoment (completedTime 1 x) 0 (n+n))) (B x x) := by
  rw [oneStep_residual_moment]
  exact RCle_trans (RCscale_mono (ofNat_nonneg n)
    (moment_defect_antitone x 1 (Nat.le_add_right _ _))) (moment_weighted_bound n x)

/-- The norm cap uses x, without assuming a T2 preimage of geometric T1 x. -/
theorem oneStep_residual_dyadic_bound (k : Nat) (x : Completion) :
    RCle (mixedMoment (completedTime 1 x) 0 (2^k+2^k)) (RCscale (HalfPow.half^k) (B x x)) := by
  have h := RCscale_mono (Q'.pow_nonneg HalfPow.half HalfPow.half_nonneg k)
    (oneStep_residual_weighted (2^k) x)
  have hn : Q'.eqv (HalfPow.half^k * Q'.ofNat (2^k)) 1 := half_power_normalizes k
  rw [RCscale_RCscale, scale_congr hn, RCscale_one] at h
  exact h

theorem oneStep_residual_small (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    RCle (mixedMoment (completedTime 1 (point X)) 0
      (residualDegree X epsilon + residualDegree X epsilon)) (rat epsilon) :=
  RCle_trans (oneStep_residual_dyadic_bound (rangeModulus X epsilon) (point X))
    (scaled_norm_small X epsilon he _ (Nat.le_refl _))

/-- The EXISTING candidate, now at a degree proved sufficient on the geometric range. -/
def oneStepPreimage (X : seminorm.Cauchy) (epsilon : Q') : seminorm.Cauchy :=
  partialPreimageCauchy (residualDegree X epsilon) (timeCauchy 1 X)

theorem oneStepPreimage_pin (X : seminorm.Cauchy) (epsilon : Q') :
    (point (oneStepPreimage X epsilon)) =
      partialPreimage (residualDegree X epsilon) (completedTime 1 (point X)) :=
  partialPreimageCauchy_pin _ _

theorem oneStepPreimage_bound (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    RCle (completedDist (completedTime 1 (point X))
      (twoStepTransfer (point (oneStepPreimage X epsilon)))) (rat epsilon) := by
  rw [oneStepPreimage_pin, partialPreimage_distance]
  exact oneStep_residual_small X epsilon he

def oneStepApproximationCertificate (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' Y : seminorm.Cauchy,
      RCle (completedDist (completedTime 1 (point X)) (twoStepTransfer (point Y))) (rat epsilon) :=
  ⟨oneStepPreimage X epsilon, oneStepPreimage_bound X epsilon he⟩

/-- Computed after constructing the approximate preimage; no uniform inverse bound. -/
def oneStepZeroRadius (X : seminorm.Cauchy) (epsilon : Q') : Q' :=
  localRadius oneTimeData (oneStepPreimage X (quarter (quarter epsilon))) (quarter (quarter epsilon))

theorem oneStepZeroRadius_positive (X : seminorm.Cauchy) (epsilon : Q') :
    (0 : Q') < oneStepZeroRadius X epsilon := localRadius_positive _ _ _

theorem oneStep_zero_bound (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (t : PositiveTimeValue) (ht : RCle (realValue t) (rat (oneStepZeroRadius X epsilon))) :
    RCle (completedDist (realTimeAction t (completedTime 1 (point X))) (completedTime 1 (point X)))
      (rat epsilon) := by
  let eta := quarter (quarter epsilon)
  have heta : (0 : Q') < eta := quarter_pos (quarter_pos he)
  let Y := oneStepPreimage X eta
  let x := completedTime 1 (point X)
  let z := twoStepTransfer (point Y)
  have herr : RCle (completedDist x z) (rat eta) := oneStepPreimage_bound X eta heta
  have htime : RCle (completedDist (realTimeAction t z) z) (rat eta) :=
    twoStep_range_zero_bound Y eta heta t ht
  exact completedDist_three_segment (realTimeAction t x) (realTimeAction t z) z x epsilon he
    (RCle_trans (realTimeAction_distance_contraction t x z) herr) htime
    (by rw [completedDist_symm]; exact herr)

/-- Time zero on actual geometric T1 states, not an identification T1=A(1/2). -/
def oneStepZeroContinuityCertificate (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' delta : Q', ((0 : Q') < delta) ×'
      (∀ t : PositiveTimeValue, RCle (realValue t) (rat delta) →
        RCle (completedDist (realTimeAction t (completedTime 1 (point X)))
          (completedTime 1 (point X))) (rat epsilon)) :=
  ⟨oneStepZeroRadius X epsilon, oneStepZeroRadius_positive X epsilon,
    fun t ht => oneStep_zero_bound X epsilon he t ht⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRangeContinuity

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRangeContinuity.moment_defect_succ_le
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRangeContinuity.moment_defect_antitone
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRangeContinuity.moment_weighted_energy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRangeContinuity.moment_weighted_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRangeContinuity.oneStep_residual_moment
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRangeContinuity.oneStep_residual_weighted
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRangeContinuity.oneStep_residual_dyadic_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRangeContinuity.oneStep_residual_small
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRangeContinuity.oneStepPreimage
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRangeContinuity.oneStepPreimage_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRangeContinuity.oneStepPreimage_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRangeContinuity.oneStepApproximationCertificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRangeContinuity.oneStepZeroRadius
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRangeContinuity.oneStepZeroRadius_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRangeContinuity.oneStep_zero_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRangeContinuity.oneStepZeroContinuityCertificate
