/- Kernel-checked forest-gauge value for orbit representative 0x2533cb. -/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit2533CB

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge

local infix:50 " ≈ " => Q'.eqv

/-- Two six-face components: twelve faces, sixteen vertices, twenty-four
edges, two primal components, and ten post-forest chords. -/
theorem forestGaugeHaar_exact :
    surfaceForestGaugeHaar 2438091 ≈
      surfaceTopologicalHaarAmplitude 2438091 := by
  decide

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit2533CB

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit2533CB.forestGaugeHaar_exact
