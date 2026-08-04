/- Kernel-checked forest-gauge value for orbit representative 0x04ab33. -/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit04AB33

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge

local infix:50 " ≈ " => Q'.eqv

/-- Ten faces, twelve vertices, twenty edges, and nine post-forest chords. -/
theorem forestGaugeHaar_exact :
    surfaceForestGaugeHaar 305971 ≈
      surfaceTopologicalHaarAmplitude 305971 := by
  decide

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit04AB33

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit04AB33.forestGaugeHaar_exact
