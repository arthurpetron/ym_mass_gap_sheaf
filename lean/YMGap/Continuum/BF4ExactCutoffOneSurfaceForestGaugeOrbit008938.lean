/- Proof-shared forest-gauge value for orbit representative 0x008938.

The exhaustive mask campaign already kernel-checks this representative.  This
compatibility module reuses that proof instead of normalizing the same closed
computation a second time.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeMask008938

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit008938

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge

local infix:50 " ≈ " => Q'.eqv

/-- Six faces, eight vertices, twelve edges, and five post-forest chords. -/
theorem forestGaugeHaar_exact :
    surfaceForestGaugeHaar 35128 ≈
      surfaceTopologicalHaarAmplitude 35128 :=
  YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeMask008938.forestGaugeHaar_exact

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit008938

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit008938.forestGaugeHaar_exact
