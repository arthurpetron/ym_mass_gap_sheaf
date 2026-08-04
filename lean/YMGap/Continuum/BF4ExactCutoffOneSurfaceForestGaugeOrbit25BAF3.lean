/- Kernel-checked forest-gauge value for orbit representative 0x25baf3. -/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit25BAF3

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge

local infix:50 " ≈ " => Q'.eqv

/-- Fourteen faces, sixteen vertices, twenty-eight edges, and thirteen
post-forest chords. -/
theorem forestGaugeHaar_exact :
    surfaceForestGaugeHaar 2472691 ≈
      surfaceTopologicalHaarAmplitude 2472691 := by
  decide

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit25BAF3

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit25BAF3.forestGaugeHaar_exact
