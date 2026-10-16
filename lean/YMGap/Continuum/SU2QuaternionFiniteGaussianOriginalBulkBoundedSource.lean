/-
# The rational bulk source as a bounded ORIGINAL Wilson expression

The existing rational bulk face list and coefficient profile are compiled into
one literal radius-zero Wilson expression on the canonical containing slice of
width `s^2`.  Its source polynomial, and its second through fourth powers, are
coefficientwise the corresponding powers of the existing spatial span.

The finite odd-window means therefore define a separate bounded ORIGINAL
center whose entries converge to the matching interacting joint limits.  This
does not identify those entries with the FREE Gaussian Cayley center, provide
an asymptotic comparison between the two laws, or assert a continuum or Clay
mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkSourceBridge
import YMGap.Continuum.BF4WilsonPlaquetteFamilyIncrement
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOwnCenterLimit
import YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleFunctionalLaws

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkBoundedSource

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift_zero)
open YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin
open YMGap.Continuum.BF4WilsonPlaquetteFamilyIncrement (source_family_shift)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule (spatialSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleFunctionalLaws (middleRatio_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOwnCenterLimit
  (expressionOwnMean expressionOwnMean_converges expressionOwn_centeredPair_converges)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy (originalJointLimit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMovingCenterLagDifference (centeredPair)
open YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement (state)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments (centeredTimeMoment)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkSourceBridge
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)

local infix:50 " ≈ " => Q'.eqv

/-- The literal weighted bulk Wilson family at time offset zero. -/
def originalBulkExpression (s : Nat) (hs : 0 < s) : WindowExpression (s * s) :=
  familyExpression (s * s) (bulkSourceFaces s) (bulkSourceCoefficient s hs)
    (bulkSourceFaces_spatial s)

theorem originalBulkExpression_within (s : Nat) (hs : 0 < s) :
    Within 0 (originalBulkExpression s hs) :=
  family_within (s * s) (bulkSourceFaces s) (bulkSourceCoefficient s hs)
    (bulkSourceFaces_spatial s)

/-- The bounded expression is exactly the existing ORIGINAL spatial span. -/
theorem originalBulkExpression_source_pin (s : Nat) (hs : 0 < s) :
    RatPolyCoeffEqv (sourcePolynomial (originalBulkExpression s hs))
      (spatialSpan (s * s) (bulkSourceCoefficient s hs) (bulkSourceFaces s)) := by
  simpa only [originalBulkExpression, shift_zero, Nat.zero_mul, liftBoundary] using
    source_family_shift (s * s) (bulkSourceFaces s) (bulkSourceCoefficient s hs)
      (bulkSourceFaces_spatial s) 0

def originalBulkSquareExpression (s : Nat) (hs : 0 < s) : WindowExpression (s * s) :=
  .mul (originalBulkExpression s hs) (originalBulkExpression s hs)

def originalBulkCubeExpression (s : Nat) (hs : 0 < s) : WindowExpression (s * s) :=
  .mul (originalBulkSquareExpression s hs) (originalBulkExpression s hs)

def originalBulkFourthExpression (s : Nat) (hs : 0 < s) : WindowExpression (s * s) :=
  .mul (originalBulkSquareExpression s hs) (originalBulkSquareExpression s hs)

theorem originalBulkSquareExpression_within (s : Nat) (hs : 0 < s) :
    Within 0 (originalBulkSquareExpression s hs) :=
  ⟨originalBulkExpression_within s hs, originalBulkExpression_within s hs⟩

theorem originalBulkCubeExpression_within (s : Nat) (hs : 0 < s) :
    Within 0 (originalBulkCubeExpression s hs) :=
  ⟨originalBulkSquareExpression_within s hs, originalBulkExpression_within s hs⟩

theorem originalBulkFourthExpression_within (s : Nat) (hs : 0 < s) :
    Within 0 (originalBulkFourthExpression s hs) :=
  ⟨originalBulkSquareExpression_within s hs, originalBulkSquareExpression_within s hs⟩

theorem originalBulkSquareExpression_source_pin (s : Nat) (hs : 0 < s) :
    RatPolyCoeffEqv (sourcePolynomial (originalBulkSquareExpression s hs))
      (polyMul
        (spatialSpan (s * s) (bulkSourceCoefficient s hs) (bulkSourceFaces s))
        (spatialSpan (s * s) (bulkSourceCoefficient s hs) (bulkSourceFaces s))) :=
  (originalBulkExpression_source_pin s hs).mul
    (originalBulkExpression_source_pin s hs)

theorem originalBulkCubeExpression_source_pin (s : Nat) (hs : 0 < s) :
    RatPolyCoeffEqv (sourcePolynomial (originalBulkCubeExpression s hs))
      (polyMul
        (polyMul
          (spatialSpan (s * s) (bulkSourceCoefficient s hs) (bulkSourceFaces s))
          (spatialSpan (s * s) (bulkSourceCoefficient s hs) (bulkSourceFaces s)))
        (spatialSpan (s * s) (bulkSourceCoefficient s hs) (bulkSourceFaces s))) :=
  (originalBulkSquareExpression_source_pin s hs).mul
    (originalBulkExpression_source_pin s hs)

theorem originalBulkFourthExpression_source_pin (s : Nat) (hs : 0 < s) :
    RatPolyCoeffEqv (sourcePolynomial (originalBulkFourthExpression s hs))
      (polyMul
        (polyMul
          (spatialSpan (s * s) (bulkSourceCoefficient s hs) (bulkSourceFaces s))
          (spatialSpan (s * s) (bulkSourceCoefficient s hs) (bulkSourceFaces s)))
        (polyMul
          (spatialSpan (s * s) (bulkSourceCoefficient s hs) (bulkSourceFaces s))
          (spatialSpan (s * s) (bulkSourceCoefficient s hs) (bulkSourceFaces s)))) :=
  (originalBulkSquareExpression_source_pin s hs).mul
    (originalBulkSquareExpression_source_pin s hs)

/-- The actual finite odd-window mean of the bounded ORIGINAL bulk source. -/
def originalBulkOwnMean {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n : Nat) : Q' :=
  expressionOwnMean hw0 hw1 (originalBulkExpression s hs) stage n

theorem originalBulkOwnMean_spatialSpan_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n : Nat) :
    middleRatio hw0 hw1 (headCutoff w + stage) (s * s) (Nat.le_add_right _ _)
        (n + 1) n
        (spatialSpan (s * s) (bulkSourceCoefficient s hs) (bulkSourceFaces s)) ≈
      originalBulkOwnMean hw0 hw1 s hs stage n := by
  unfold originalBulkOwnMean expressionOwnMean
  exact middleRatio_congr hw0 hw1 _ _ _ _ _
    (originalBulkExpression_source_pin s hs).symm

/-- A same-law moment center for the bounded Wilson source powers.  The field
names deliberately differ from `CayleyTraceOldCenter.c2/c3/c4`: these are
moments of one exact bounded source, not homogeneous Cayley coefficients. -/
structure OriginalBulkBoundedMomentCenter where
  m2 : Q'
  m3 : Q'
  m4 : Q'

def originalBulkBoundedMomentCenter {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n : Nat) : OriginalBulkBoundedMomentCenter where
  m2 := expressionOwnMean hw0 hw1 (originalBulkSquareExpression s hs) stage n
  m3 := expressionOwnMean hw0 hw1 (originalBulkCubeExpression s hs) stage n
  m4 := expressionOwnMean hw0 hw1 (originalBulkFourthExpression s hs) stage n

theorem originalBulkBoundedMomentCenter_m2_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n : Nat) :
    middleRatio hw0 hw1 (headCutoff w + stage) (s * s) (Nat.le_add_right _ _)
        (n + 1) n
        (polyMul
          (spatialSpan (s * s) (bulkSourceCoefficient s hs) (bulkSourceFaces s))
          (spatialSpan (s * s) (bulkSourceCoefficient s hs) (bulkSourceFaces s))) ≈
      (originalBulkBoundedMomentCenter hw0 hw1 s hs stage n).m2 := by
  unfold originalBulkBoundedMomentCenter expressionOwnMean
  exact middleRatio_congr hw0 hw1 _ _ _ _ _
    (originalBulkSquareExpression_source_pin s hs).symm

theorem originalBulkBoundedMomentCenter_m3_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n : Nat) :
    middleRatio hw0 hw1 (headCutoff w + stage) (s * s) (Nat.le_add_right _ _)
        (n + 1) n
        (polyMul
          (polyMul
            (spatialSpan (s * s) (bulkSourceCoefficient s hs) (bulkSourceFaces s))
            (spatialSpan (s * s) (bulkSourceCoefficient s hs) (bulkSourceFaces s)))
          (spatialSpan (s * s) (bulkSourceCoefficient s hs) (bulkSourceFaces s))) ≈
      (originalBulkBoundedMomentCenter hw0 hw1 s hs stage n).m3 := by
  unfold originalBulkBoundedMomentCenter expressionOwnMean
  exact middleRatio_congr hw0 hw1 _ _ _ _ _
    (originalBulkCubeExpression_source_pin s hs).symm

theorem originalBulkBoundedMomentCenter_m4_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n : Nat) :
    middleRatio hw0 hw1 (headCutoff w + stage) (s * s) (Nat.le_add_right _ _)
        (n + 1) n
        (polyMul
          (polyMul
            (spatialSpan (s * s) (bulkSourceCoefficient s hs) (bulkSourceFaces s))
            (spatialSpan (s * s) (bulkSourceCoefficient s hs) (bulkSourceFaces s)))
          (polyMul
            (spatialSpan (s * s) (bulkSourceCoefficient s hs) (bulkSourceFaces s))
            (spatialSpan (s * s) (bulkSourceCoefficient s hs) (bulkSourceFaces s)))) ≈
      (originalBulkBoundedMomentCenter hw0 hw1 s hs stage n).m4 := by
  unfold originalBulkBoundedMomentCenter expressionOwnMean
  exact middleRatio_congr hw0 hw1 _ _ _ _ _
    (originalBulkFourthExpression_source_pin s hs).symm

theorem originalBulkOwnMean_converges {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (s : Nat) (hs : 0 < s) :
    ConvergesTo (fun k => ofQ' (originalBulkOwnMean hw0 hw1 s hs k k))
      (originalJointLimit hw0 hw1 0 (originalBulkExpression s hs)
        (originalBulkExpression_within s hs)) := by
  simpa only [originalBulkOwnMean] using
    expressionOwnMean_converges hw0 hw1 (originalBulkExpression s hs)
      (originalBulkExpression_within s hs)

theorem originalBulkBoundedMomentCenter_m2_converges {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (s : Nat) (hs : 0 < s) :
    ConvergesTo
      (fun k => ofQ' ((originalBulkBoundedMomentCenter hw0 hw1 s hs k k).m2))
      (originalJointLimit hw0 hw1 0 (originalBulkSquareExpression s hs)
        (originalBulkSquareExpression_within s hs)) := by
  simpa only [originalBulkBoundedMomentCenter] using
    expressionOwnMean_converges hw0 hw1 (originalBulkSquareExpression s hs)
      (originalBulkSquareExpression_within s hs)

theorem originalBulkBoundedMomentCenter_m3_converges {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (s : Nat) (hs : 0 < s) :
    ConvergesTo
      (fun k => ofQ' ((originalBulkBoundedMomentCenter hw0 hw1 s hs k k).m3))
      (originalJointLimit hw0 hw1 0 (originalBulkCubeExpression s hs)
        (originalBulkCubeExpression_within s hs)) := by
  simpa only [originalBulkBoundedMomentCenter] using
    expressionOwnMean_converges hw0 hw1 (originalBulkCubeExpression s hs)
      (originalBulkCubeExpression_within s hs)

theorem originalBulkBoundedMomentCenter_m4_converges {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (s : Nat) (hs : 0 < s) :
    ConvergesTo
      (fun k => ofQ' ((originalBulkBoundedMomentCenter hw0 hw1 s hs k k).m4))
      (originalJointLimit hw0 hw1 0 (originalBulkFourthExpression s hs)
        (originalBulkFourthExpression_within s hs)) := by
  simpa only [originalBulkBoundedMomentCenter] using
    expressionOwnMean_converges hw0 hw1 (originalBulkFourthExpression s hs)
      (originalBulkFourthExpression_within s hs)

/-- The finite moving OWN center produces the existing SAME-ORIGINAL
centered two-time moment of the exact bounded bulk source. -/
theorem originalBulkOwn_centeredPair_converges {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (L : Nat) :
    ConvergesTo (fun k => ofQ'
      (centeredPair hw0 hw1 (headCutoff w + k) (s * s) (Nat.le_add_right _ _)
        k L (sourcePolynomial (originalBulkExpression s hs))
        (originalBulkOwnMean hw0 hw1 s hs k k)))
      (centeredTimeMoment hw0 hw1 L
        (state (originalBulkExpression s hs) (originalBulkExpression_within s hs))
        (state (originalBulkExpression s hs) (originalBulkExpression_within s hs))) := by
  simpa only [originalBulkOwnMean] using
    expressionOwn_centeredPair_converges hw0 hw1 (originalBulkExpression s hs)
      (originalBulkExpression_within s hs) L

#print axioms originalBulkExpression_source_pin
#print axioms originalBulkSquareExpression_source_pin
#print axioms originalBulkCubeExpression_source_pin
#print axioms originalBulkFourthExpression_source_pin
#print axioms originalBulkOwnMean_spatialSpan_pin
#print axioms originalBulkBoundedMomentCenter_m2_pin
#print axioms originalBulkBoundedMomentCenter_m3_pin
#print axioms originalBulkBoundedMomentCenter_m4_pin
#print axioms originalBulkOwnMean_converges
#print axioms originalBulkBoundedMomentCenter_m2_converges
#print axioms originalBulkBoundedMomentCenter_m3_converges
#print axioms originalBulkBoundedMomentCenter_m4_converges
#print axioms originalBulkOwn_centeredPair_converges

end YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkBoundedSource
