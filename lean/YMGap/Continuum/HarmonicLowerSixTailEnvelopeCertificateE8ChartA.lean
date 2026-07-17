/-
# Exact coefficient certificate for the lower-six E8 envelope, chart A

The generated integer tables encode the degree `(83,44)` tensor Bernstein
certificate after `x=64/n` and `D=n^2*(1+r)`.  All large equalities below
are staged one-dimensional coefficient checks; no substituted multivariate
polynomial is sent to the eager ring normalizer.
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartARows
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateRawRows
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCoefficientKernel

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartA

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

open YMGap.Continuum.TensorBernsteinSeparableReconstruction
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCoefficientKernel
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateRows

private abbrev power : Nat → Nat → Int :=
  gridCoeff tailEnvelopeE8ChartAScaledPowerRows

private abbrev xPascal : Nat → Nat → Int :=
  gridCoeff tailEnvelopeE8ChartAXPascalRows

private abbrev bernstein : Nat → Nat → Int :=
  gridCoeff tailEnvelopeE8ChartABernsteinRows

private abbrev preChart : Nat → Nat → Int :=
  gridCoeff tailEnvelopeE8ChartAPreChartRows

theorem tailEnvelopeE8ChartA_xPascal_relation :
    GridRelation 84 45 xPascal
      (xPascalExpected 83 tailEnvelopeE8ChartAScaledPowerRows) = true := by
  rfl

theorem tailEnvelopeE8ChartA_yPascal_relation :
    GridRelation 84 45
      (weightedGrid 83 44 tailEnvelopeE8ChartABernsteinRows)
      (yPascalExpected 44 tailEnvelopeE8ChartAXPascalRows) = true := by
  rfl

theorem tailEnvelopeE8ChartA_bernstein_nonnegative :
    GridNonnegative 84 45 bernstein = true := by
  rfl

theorem tailEnvelopeE8ChartA_shift_relation :
    GridRelation 84 45 power
      (fun a b => upperBinomialTransform 44 (preChart a) b) = true := by
  rfl

theorem tailEnvelopeE8ChartA_raw_relation :
    GridRelation 84 45
      (fun u i => preChart u i * Int.ofNat (64 ^ u))
      (quadraticRawExpected 89 tailEnvelopeE8ChartAChartQuotient
        tailEnvelopeE8ClearedRows) = true := by
  rfl

theorem tailEnvelopeE8ChartA_scale_relation :
    tailEnvelopeE8ChartATableScale =
      tailEnvelopeE8ChartAClearScale *
        tailEnvelopeE8ChartAChartQuotient := by
  decide

theorem tailEnvelopeE8ChartA_transform_at
    {i j : Nat} (hi : i < 84) (hj : j < 45) :
    weightedGrid 83 44 tailEnvelopeE8ChartABernsteinRows i j =
      tensorPascalTransform 83 44 power i j := by
  have hy := gridRelation_true_at
    tailEnvelopeE8ChartA_yPascal_relation hi hj
  have hx : ∀ b, b < 45 →
      xPascal i b = tensorPascalMid 83 power i b := by
    intro b hb
    exact gridRelation_true_at tailEnvelopeE8ChartA_xPascal_relation hi hb
  calc
    weightedGrid 83 44 tailEnvelopeE8ChartABernsteinRows i j =
        yPascalExpected 44 tailEnvelopeE8ChartAXPascalRows i j := hy
    _ = tensorPascalTransform 83 44 power i j := by
      unfold yPascalExpected tensorPascalTransform tensorPascalMid
      exact pascalTransformRow_congr 44
        (fun b => xPascal i b)
        (fun b => pascalTransformRow 83 (fun a => power a b) i)
        j hx

theorem tailEnvelopeE8ChartA_bernstein_nonnegative_at
    {i j : Nat} (hi : i < 84) (hj : j < 45) :
    (0 : Int) ≤ bernstein i j :=
  gridNonnegative_true_at tailEnvelopeE8ChartA_bernstein_nonnegative hi hj

#print axioms tailEnvelopeE8ChartA_xPascal_relation
#print axioms tailEnvelopeE8ChartA_yPascal_relation
#print axioms tailEnvelopeE8ChartA_bernstein_nonnegative
#print axioms tailEnvelopeE8ChartA_shift_relation
#print axioms tailEnvelopeE8ChartA_raw_relation
#print axioms tailEnvelopeE8ChartA_scale_relation
#print axioms tailEnvelopeE8ChartA_transform_at
#print axioms tailEnvelopeE8ChartA_bernstein_nonnegative_at

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartA
