/- Kernel-checked forest-gauge value for orbit representative 0x2dfaa6. -/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit2DFAA6

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge

local infix:50 " ≈ " => Q'.eqv

/-- Fourteen faces, sixteen vertices, twenty-eight edges, and thirteen
post-forest chords; this is the second fourteen-face symmetry orbit. -/
theorem forestGaugeHaar_exact :
    surfaceForestGaugeHaar 3013286 ≈
      surfaceTopologicalHaarAmplitude 3013286 := by
  decide

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit2DFAA6

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit2DFAA6.forestGaugeHaar_exact
