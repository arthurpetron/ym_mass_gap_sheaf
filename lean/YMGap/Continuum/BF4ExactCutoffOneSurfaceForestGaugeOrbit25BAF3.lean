/- Proof-shared forest-gauge value for orbit representative 0x25baf3.

The exhaustive mask campaign already kernel-checks this representative.  This
compatibility module reuses that proof instead of normalizing the same closed
computation a second time.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeMask25BAF3

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit25BAF3

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge

local infix:50 " ≈ " => Q'.eqv

/-- Fourteen faces, sixteen vertices, twenty-eight edges, and thirteen
post-forest chords. -/
theorem forestGaugeHaar_exact :
    surfaceForestGaugeHaar 2472691 ≈
      surfaceTopologicalHaarAmplitude 2472691 :=
  YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeMask25BAF3.forestGaugeHaar_exact

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit25BAF3

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit25BAF3.forestGaugeHaar_exact
