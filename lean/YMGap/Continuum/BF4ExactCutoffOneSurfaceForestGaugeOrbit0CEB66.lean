/- Kernel-checked forest-gauge value for orbit representative 0x0ceb66. -/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit0CEB66

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge

local infix:50 " ≈ " => Q'.eqv

/-- Twelve faces, fourteen vertices, twenty-four edges, and eleven
post-forest chords. -/
theorem forestGaugeHaar_exact :
    surfaceForestGaugeHaar 846694 ≈
      surfaceTopologicalHaarAmplitude 846694 := by
  decide

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit0CEB66

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit0CEB66.forestGaugeHaar_exact
