/- Kernel-checked forest-gauge value for orbit representative 0x008938. -/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit008938

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge

local infix:50 " ≈ " => Q'.eqv

/-- Six faces, eight vertices, twelve edges, and five post-forest chords. -/
theorem forestGaugeHaar_exact :
    surfaceForestGaugeHaar 35128 ≈
      surfaceTopologicalHaarAmplitude 35128 := by
  decide

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit008938

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit008938.forestGaugeHaar_exact
