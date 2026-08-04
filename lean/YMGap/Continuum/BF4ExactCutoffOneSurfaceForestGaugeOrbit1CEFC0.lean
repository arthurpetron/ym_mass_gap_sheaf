/- Kernel-checked forest-gauge value for orbit representative 0x1cefc0. -/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit1CEFC0

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge

local infix:50 " ≈ " => Q'.eqv

/-- Twelve faces, fourteen vertices, twenty-four edges, and eleven
post-forest chords; this is the second twelve-face symmetry orbit. -/
theorem forestGaugeHaar_exact :
    surfaceForestGaugeHaar 1896384 ≈
      surfaceTopologicalHaarAmplitude 1896384 := by
  decide

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit1CEFC0

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit1CEFC0.forestGaugeHaar_exact
