/-
# Exact raw scaling for the lower-six E8/E9 envelope certificates

The chart-A tables multiply every cleared raw coefficient by one exact
integer quotient.  This module transports that coefficientwise fact through
the quadratic evaluator without expanding either dense grid.
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartAPhysical
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartAPhysical

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeRawScaling

open YMGap.Constructive
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateRows
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartAPhysical
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE9ChartAPhysical
open YMGap.Continuum.TensorBernsteinQuadraticProjectiveReconstruction
open YMGap.Continuum.TensorBernsteinSeparableReconstruction

local infix:50 " ≈ " => Q'.eqv

/-- E8's generated cleared numerator, before the chart-dependent quotient. -/
def tailEnvelopeE8ClearedEval (D n : Q') : Q' :=
  quadraticPowerEval 83 44 89
    (gridCoeff tailEnvelopeE8ClearedRows) D n

/-- E9's generated cleared numerator, before the chart-dependent quotient. -/
def tailEnvelopeE9ClearedEval (D n : Q') : Q' :=
  quadraticPowerEval 87 44 89
    (gridCoeff tailEnvelopeE9ClearedRows) D n

theorem tailEnvelopeE8ChartARawEval_eqv_cleared
    (D n : Q') :
    tailEnvelopeE8ChartARawEval D n ≈
      tailEnvelopeE8ClearedEval D n *
        Q'.ofInt (Int.ofNat tailEnvelopeE8ChartAChartQuotient) := by
  unfold tailEnvelopeE8ChartARawEval tailEnvelopeE8ChartAScaledRaw
    tailEnvelopeE8ClearedEval
  exact quadraticPowerEval_scale_left 83 44 89
    (gridCoeff tailEnvelopeE8ClearedRows)
    (Int.ofNat tailEnvelopeE8ChartAChartQuotient) D n

theorem tailEnvelopeE9ChartARawEval_eqv_cleared
    (D n : Q') :
    tailEnvelopeE9ChartARawEval D n ≈
      tailEnvelopeE9ClearedEval D n *
        Q'.ofInt (Int.ofNat tailEnvelopeE9ChartAChartQuotient) := by
  unfold tailEnvelopeE9ChartARawEval tailEnvelopeE9ChartAScaledRaw
    tailEnvelopeE9ClearedEval
  exact quadraticPowerEval_scale_left 87 44 89
    (gridCoeff tailEnvelopeE9ClearedRows)
    (Int.ofNat tailEnvelopeE9ChartAChartQuotient) D n

#print axioms tailEnvelopeE8ClearedEval
#print axioms tailEnvelopeE9ClearedEval
#print axioms tailEnvelopeE8ChartARawEval_eqv_cleared
#print axioms tailEnvelopeE9ChartARawEval_eqv_cleared

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeRawScaling
