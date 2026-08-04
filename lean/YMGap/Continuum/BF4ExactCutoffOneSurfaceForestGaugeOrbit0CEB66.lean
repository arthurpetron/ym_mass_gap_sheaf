/- Proof-shared forest-gauge value for orbit representative 0x0ceb66.

The exhaustive mask campaign already kernel-checks this representative.  This
compatibility module reuses that proof instead of normalizing the same closed
computation a second time.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeMask0CEB66

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit0CEB66

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge

local infix:50 " ≈ " => Q'.eqv

/-- Twelve faces, fourteen vertices, twenty-four edges, and eleven
post-forest chords. -/
theorem forestGaugeHaar_exact :
    surfaceForestGaugeHaar 846694 ≈
      surfaceTopologicalHaarAmplitude 846694 :=
  YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeMask0CEB66.forestGaugeHaar_exact

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit0CEB66

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit0CEB66.forestGaugeHaar_exact
