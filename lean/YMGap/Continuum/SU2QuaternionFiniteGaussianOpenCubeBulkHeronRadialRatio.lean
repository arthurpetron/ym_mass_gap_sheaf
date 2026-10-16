/-
# Normalized finite radial ratio for the open-cube bulk source

The explicit positive Heron stage supplies a strictly positive rational
quadratic radial pair covariance.  This leaf uses that witness as the
denominator of the corresponding finite sixth-order radial covariance and
constructs the exact positive-denominator rational quotient.

This is only the formula-level finite product-Gaussian ratio.  No quantitative
bound on its numerator, original-law comparison, continuum limit, Hamiltonian
gap, or Clay theorem is proved here.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronRadialRatio

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

/-- Sixth-order radial covariance numerator for the weighted bulk source at
the explicit positivity-preserving Heron stage. -/
def bulkSourcePositiveHeronRadialNumerator
    (s : Nat) (hs : 0 < s) : Q' :=
  let coordinateCount :=
    historyCoordinateCount 1
      (combGaugeEdgeCount (bulkSourceWidth s))
  let stage := bulkSourcePositiveHeronStage s
  let source := bulkSourceHeronRadialSquare 1 s hs stage 0
  let direction := bulkSourceHeronRadialSquare 1 s hs stage 1
  finiteGaussianCovariance
    (coordinateCount + (coordinateCount + coordinateCount))
    (polyMul source source) direction

/-- Positive quadratic radial pair covariance used as the normalization
denominator. -/
def bulkSourcePositiveHeronRadialDenominator
    (s : Nat) (hs : 0 < s) : Q' :=
  bulkSourceHeronRadialPairCovariance
    1 s hs (bulkSourcePositiveHeronStage s) 0 1

theorem bulkSourcePositiveHeronRadialDenominator_pos
    (s : Nat) (hs : 0 < s) :
    (0 : Q') < bulkSourcePositiveHeronRadialDenominator s hs :=
  bulkSourcePositiveHeronRadialPairCovariance_pos s hs

/-- Exact normalized finite rational radial ratio. -/
def bulkSourcePositiveHeronRadialRatio
    (s : Nat) (hs : 0 < s) : Q' :=
  Q'.divPos
    (bulkSourcePositiveHeronRadialNumerator s hs)
    (bulkSourcePositiveHeronRadialDenominator s hs)
    (bulkSourcePositiveHeronRadialDenominator_pos s hs)

/-- Positive-denominator cancellation recovers the literal sixth-order
numerator exactly. -/
theorem bulkSourcePositiveHeronRadialRatio_mul_denominator
    (s : Nat) (hs : 0 < s) :
    bulkSourcePositiveHeronRadialRatio s hs *
        bulkSourcePositiveHeronRadialDenominator s hs ≈
      bulkSourcePositiveHeronRadialNumerator s hs := by
  unfold bulkSourcePositiveHeronRadialRatio
  exact Q'.divPos_mul_eqv _ _ _

/-- A cleared lower estimate transports directly to the normalized ratio. -/
theorem le_bulkSourcePositiveHeronRadialRatio_of_mul_le
    (s : Nat) (hs : 0 < s) {lower : Q'}
    (hbound : lower * bulkSourcePositiveHeronRadialDenominator s hs ≤
      bulkSourcePositiveHeronRadialNumerator s hs) :
    lower ≤ bulkSourcePositiveHeronRadialRatio s hs := by
  unfold bulkSourcePositiveHeronRadialRatio
  exact Q'.le_divPos_of_mul_le _ _ _ hbound

/-- A cleared upper estimate transports directly to the normalized ratio. -/
theorem bulkSourcePositiveHeronRadialRatio_le_of_le_mul
    (s : Nat) (hs : 0 < s) {upper : Q'}
    (hbound : bulkSourcePositiveHeronRadialNumerator s hs ≤
      upper * bulkSourcePositiveHeronRadialDenominator s hs) :
    bulkSourcePositiveHeronRadialRatio s hs ≤ upper := by
  unfold bulkSourcePositiveHeronRadialRatio
  exact Q'.divPos_le_of_le_mul _ _ _ hbound

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronRadialRatio

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronRadialRatio.bulkSourcePositiveHeronRadialDenominator_pos
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronRadialRatio.bulkSourcePositiveHeronRadialRatio_mul_denominator
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronRadialRatio.le_bulkSourcePositiveHeronRadialRatio_of_mul_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronRadialRatio.bulkSourcePositiveHeronRadialRatio_le_of_le_mul
