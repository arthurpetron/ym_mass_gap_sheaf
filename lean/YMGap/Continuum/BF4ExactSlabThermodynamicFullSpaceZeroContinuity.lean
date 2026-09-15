/-
# Computed residuals, original range density, and full-space time zero

An arbitrary supplied ORIGINAL Cauchy representative provides a dense
sample at epsilon/4. Defect contraction and the proved dense residual
degree then bound its OWN defect residual at every later degree. The OLD
finite partial sum therefore supplies an actual approximate T2 preimage.

The computed residual bound constructs the existing finite accepted
time-zero certificate. Its radius controls the existing positive-real-time
action on EVERY original represented state, not only a transfer range.
All witnesses and moduli are data; no quotient representative is selected,
no range-closure space replaces the original completion, and no inverse
bound is assumed. The original T2 kernel is consequently trivial.

SU(2), nome 1/1024, fixed spacing. This is not a bounded inverse or a
uniform physical spectral floor. Physical Hamiltonian identification,
spacing/coupling control, continuum QFT and the all-group Clay target
remain open. No canonical frontier field is changed here.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicDenseResidualDecay
import YMGap.Continuum.BF4ExactSlabThermodynamicZeroTimeCertificate

namespace YMGap.Continuum.BF4ExactSlabThermodynamicFullSpaceZeroContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation (Presentation)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear (completedInner_zero_left)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation (completedTime_sub)
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments
open YMGap.Continuum.BF4ExactSlabThermodynamicRangeApproximation
open YMGap.Continuum.BF4ExactSlabThermodynamicRangeDefectEnergy (defectPower_distance_contraction)
open YMGap.Continuum.BF4ExactSlabThermodynamicDenseResidualDecay
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows (completed_eq_of_small)
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit (dist_zero)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealLocalContinuity (localRadius localRadius_positive)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRangeZeroContinuity (oneTimeData)
open YMGap.Continuum.BF4ExactSlabThermodynamicZeroTimeCertificate (Certificate certificateOfMomentBound)

local notation "point" X => Quotient.mk seminorm.completionSetoid X
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

def denseSample (X : seminorm.Cauchy) (epsilon : Q') : Presentation :=
  X.seq (X.modulus (quarter epsilon))

/-- The supplied original modulus and the actual dense sample compute the degree. -/
def residualModulus (X : seminorm.Cauchy) (epsilon : Q') : Nat :=
  denseDegree (denseSample X epsilon) (quarter epsilon)

theorem residual_small (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : residualModulus X epsilon ≤ n) :
    RCle (mixedMoment (point X) 0 (n+n)) (rat epsilon) := by
  have hsample : RCle (completedDist (point X) (embedPresentation (denseSample X epsilon)))
      (rat (quarter epsilon)) := by
    rw [completedDist_symm]
    exact constantApproximation_bound X (quarter epsilon) (quarter_pos he) _ (Nat.le_refl _)
  have h := completedDist_two_segment (defectPower n (point X))
    (defectPower n (embedPresentation (denseSample X epsilon))) completedZero epsilon
    (RCle_trans (defectPower_distance_contraction n _ _) hsample)
    (by rw [dist_zero, residual_norm_moment]
        exact dense_residual_small (denseSample X epsilon) (quarter epsilon) (quarter_pos he) n hn)
  rw [dist_zero, residual_norm_moment] at h
  exact h

/-- A finite original Cauchy sum for X itself, not just for its dense sample. -/
def approximatePreimage (X : seminorm.Cauchy) (epsilon : Q') : seminorm.Cauchy :=
  partialPreimageCauchy (residualModulus X epsilon) X

theorem approximatePreimage_bound (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    RCle (completedDist (point X) (twoStepTransfer (point (approximatePreimage X epsilon)))) (rat epsilon) := by
  rw [approximatePreimage, partialPreimageCauchy_pin, partialPreimage_distance]
  exact residual_small X epsilon he _ (Nat.le_refl _)

/-- Constructive range density on the unchanged completion, with actual output data. -/
def rangeApproximationData (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' Y : seminorm.Cauchy, RCle (completedDist (point X) (twoStepTransfer (point Y))) (rat epsilon) :=
  ⟨approximatePreimage X epsilon, approximatePreimage_bound X epsilon he⟩

/-- Every original represented state and positive tolerance gets an accepted finite test. -/
def zeroCertificate (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) : Certificate X epsilon :=
  certificateOfMomentBound X epsilon he
    (residualModulus X (HalfPow.half * quarter (quarter epsilon)))
    (residual_small X (HalfPow.half * quarter (quarter epsilon))
      (ExpNeg.half_mul_pos _ (quarter_pos (quarter_pos he))) _ (Nat.le_refl _))

/-- Positive-real T2-time radius, computed from original state data and squared error. -/
def zeroRadius (X : seminorm.Cauchy) (epsilon : Q') : Q' :=
  localRadius oneTimeData
    (partialPreimageCauchy (residualModulus X (HalfPow.half * quarter (quarter epsilon))) X)
    (quarter (quarter epsilon))

theorem zeroRadius_positive (X : seminorm.Cauchy) (epsilon : Q') :
    (0 : Q') < zeroRadius X epsilon := localRadius_positive _ _ _

/-- The original positive-real-time action tends to identity on the ENTIRE original space. -/
theorem full_space_zero_bound (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (t : PositiveTimeValue) (ht : RCle (realValue t) (rat (zeroRadius X epsilon))) :
    RCle (completedDist (realTimeAction t (point X)) (point X)) (rat epsilon) :=
  (zeroCertificate X epsilon he).zero_bound t ht

def zeroContinuityData (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' delta : Q', ((0 : Q') < delta) ×'
      (∀ t : PositiveTimeValue, RCle (realValue t) (rat delta) →
        RCle (completedDist (realTimeAction t (point X)) (point X)) (rat epsilon)) :=
  ⟨zeroRadius X epsilon, zeroRadius_positive X epsilon, fun t ht => full_space_zero_bound X epsilon he t ht⟩

/-- Trivial kernel on all original quotient states; no quotient choice is used. -/
theorem transfer_kernel_trivial (x : Completion) (hx : twoStepTransfer x = completedZero) : x = completedZero := by
  revert hx
  refine Quotient.inductionOn x ?_
  intro X hx
  apply completed_eq_of_small
  intro epsilon he
  rw [dist_zero]
  have h := residual_small X epsilon he _ (Nat.le_refl _)
  rw [kernel_residual_moment _ _ hx] at h
  exact h

theorem transfer_injective (x y : Completion) (h : twoStepTransfer x = twoStepTransfer y) : x = y := by
  have hz : twoStepTransfer (completedSub x y) = completedZero := by
    change completedTime 2 (completedSub x y) = completedZero
    rw [completedTime_sub]
    change completedSub (twoStepTransfer x) (twoStepTransfer y) = completedZero
    rw [h, completedSub_self]
  apply (completedDist_zero_iff x y).mp
  unfold completedDist
  rw [transfer_kernel_trivial _ hz, completedInner_zero_left]

end YMGap.Continuum.BF4ExactSlabThermodynamicFullSpaceZeroContinuity

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicFullSpaceZeroContinuity.denseSample
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicFullSpaceZeroContinuity.residualModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicFullSpaceZeroContinuity.residual_small
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicFullSpaceZeroContinuity.approximatePreimage
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicFullSpaceZeroContinuity.approximatePreimage_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicFullSpaceZeroContinuity.rangeApproximationData
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicFullSpaceZeroContinuity.zeroCertificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicFullSpaceZeroContinuity.zeroRadius
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicFullSpaceZeroContinuity.zeroRadius_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicFullSpaceZeroContinuity.full_space_zero_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicFullSpaceZeroContinuity.zeroContinuityData
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicFullSpaceZeroContinuity.transfer_kernel_trivial
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicFullSpaceZeroContinuity.transfer_injective
