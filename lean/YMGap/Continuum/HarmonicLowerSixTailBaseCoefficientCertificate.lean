/-
# Coefficient-level certificate for the high-branch Base Bernstein table

The 42 by 23 table is checked by two cached one-dimensional Pascal passes.
No substituted Bernstein polynomial is normalized in this module.
-/

import YMGap.Continuum.HarmonicLowerSixTailBaseCertificateRows
import YMGap.Continuum.HarmonicLowerSixTailBaseCertificateSeparableRows
import YMGap.Continuum.HarmonicLowerSixTailBaseCertificateClearedRows

namespace YMGap.Continuum.HarmonicLowerSixTailBaseCoefficientCertificate

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

open YMGap.RG
open YMGap.Continuum.HarmonicLowerSixTailBaseCertificateRows
open YMGap.Continuum.HarmonicLowerSixTailBaseCertificateSeparableRows
open YMGap.Continuum.HarmonicLowerSixTailBaseCertificateClearedRows
open YMGap.Continuum.TensorBernsteinSeparableReconstruction

def tailBaseScaledPowerCoeff (a b : Nat) : Int :=
  gridCoeff tailBaseScaledPowerRows a b

def tailBaseXPascalCoeff (i b : Nat) : Int :=
  gridCoeff tailBaseXPascalRows i b

def tailBaseBernsteinCoeff (i j : Nat) : Int :=
  gridCoeff tailBaseBernsteinRows i j

def tailBaseWeightedCoeff (i j : Nat) : Int :=
  tailBaseBernsteinCoeff i j *
    Int.ofNat (binom 41 i * binom 22 j)

def tailBaseClearedCoeff (i j : Nat) : Int :=
  gridCoeff tailBaseClearedRows i j

def tailBaseClearedDiagCoeff (a j : Nat) : Int :=
  if a + j ≤ 50 then tailBaseClearedCoeff (50 - a - j) j else 0

def tailBaseScaledRawDiagCoeff (a j : Nat) : Int :=
  tailBaseChartQuotient * tailBaseClearedDiagCoeff a j

def tailBaseChartScaledPowerCoeff (a b : Nat) : Int :=
  tailBaseScaledPowerCoeff a b * Int.ofNat (8191 ^ a)

theorem tailBaseScaledPowerRows_length :
    tailBaseScaledPowerRows.length = 42 := by
  decide

theorem tailBaseXPascalRows_length : tailBaseXPascalRows.length = 42 := by
  decide

theorem tailBaseClearedRows_length : tailBaseClearedRows.length = 48 := by
  decide

/-- Closed first-pass identity in the x coordinate. -/
theorem tailBase_xPascal_relation :
    GridRelation 42 23 tailBaseXPascalCoeff
      (tensorPascalMid 41 tailBaseScaledPowerCoeff) = true := by
  rfl

/-- Closed second-pass identity in the y coordinate. -/
theorem tailBase_yPascal_relation :
    GridRelation 42 23 tailBaseWeightedCoeff
      (fun i j => pascalTransformRow 22 (tailBaseXPascalCoeff i) j) = true := by
  rfl

/-- Closed sign check for the binomial-weighted Bernstein table. -/
theorem tailBase_weighted_nonnegative :
    GridNonnegative 42 23 tailBaseWeightedCoeff = true := by
  rfl

/-- Closed raw-chart identity.  For each inverse-scale exponent `a`, the
upper-binomial transform reconstructs `n/D = 1 + (n-D)/D`. -/
theorem tailBase_rawChart_relation :
    GridRelation 42 23 tailBaseChartScaledPowerCoeff
      (fun a b => upperBinomialTransform 22
        (tailBaseScaledRawDiagCoeff a) b) = true := by
  rfl

theorem tailBase_weighted_eq_tensorPascal
    {i j : Nat} (hi : i < 42) (hj : j < 23) :
    tailBaseWeightedCoeff i j =
      tensorPascalTransform 41 22 tailBaseScaledPowerCoeff i j := by
  have hy := gridRelation_true_at tailBase_yPascal_relation hi hj
  refine hy.trans ?_
  unfold tensorPascalTransform
  apply pascalTransformRow_congr
  intro b hb
  exact gridRelation_true_at tailBase_xPascal_relation hi hb

theorem tailBase_weighted_nonnegative_at
    {i j : Nat} (hi : i < 42) (hj : j < 23) :
    (0 : Int) ≤ tailBaseWeightedCoeff i j :=
  gridNonnegative_true_at tailBase_weighted_nonnegative hi hj

theorem tailBase_rawChart_relation_at
    {a b : Nat} (ha : a < 42) (hb : b < 23) :
    tailBaseChartScaledPowerCoeff a b =
      upperBinomialTransform 22 (tailBaseScaledRawDiagCoeff a) b :=
  gridRelation_true_at tailBase_rawChart_relation ha hb

#print axioms tailBase_xPascal_relation
#print axioms tailBase_yPascal_relation
#print axioms tailBase_weighted_nonnegative
#print axioms tailBase_rawChart_relation
#print axioms tailBase_weighted_eq_tensorPascal
#print axioms tailBase_weighted_nonnegative_at
#print axioms tailBase_rawChart_relation_at

end YMGap.Continuum.HarmonicLowerSixTailBaseCoefficientCertificate
