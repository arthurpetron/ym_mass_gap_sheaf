/- Exact first Pascal pass for the lower-six E8 chart-A table. -/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartARows
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCoefficientKernel

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartA

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

open YMGap.Continuum.TensorBernsteinSeparableReconstruction
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCoefficientKernel
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateRows

theorem tailEnvelopeE8ChartA_xPascal_relation :
    GridRelation 84 45
      (gridCoeff tailEnvelopeE8ChartAXPascalRows)
      (xPascalExpected 83 tailEnvelopeE8ChartAScaledPowerRows) = true := by
  rfl

#print axioms tailEnvelopeE8ChartA_xPascal_relation

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartA
