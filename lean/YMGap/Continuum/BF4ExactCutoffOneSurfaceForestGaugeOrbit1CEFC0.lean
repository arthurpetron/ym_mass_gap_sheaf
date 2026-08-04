/- Proof-shared forest-gauge value for orbit representative 0x1cefc0.

The exhaustive mask campaign already kernel-checks this representative.  This
compatibility module reuses that proof instead of normalizing the same closed
computation a second time.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeMask1CEFC0

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit1CEFC0

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge

local infix:50 " ≈ " => Q'.eqv

/-- Twelve faces, fourteen vertices, twenty-four edges, and eleven
post-forest chords; this is the second twelve-face symmetry orbit. -/
theorem forestGaugeHaar_exact :
    surfaceForestGaugeHaar 1896384 ≈
      surfaceTopologicalHaarAmplitude 1896384 :=
  YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeMask1CEFC0.forestGaugeHaar_exact

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit1CEFC0

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit1CEFC0.forestGaugeHaar_exact
