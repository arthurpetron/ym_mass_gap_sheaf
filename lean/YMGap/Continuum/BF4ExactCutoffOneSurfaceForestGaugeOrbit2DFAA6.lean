/- Proof-shared forest-gauge value for orbit representative 0x2dfaa6.

The exhaustive mask campaign already kernel-checks this representative.  This
compatibility module reuses that proof instead of normalizing the same closed
computation a second time.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeMask2DFAA6

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit2DFAA6

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge

local infix:50 " ≈ " => Q'.eqv

/-- Fourteen faces, sixteen vertices, twenty-eight edges, and thirteen
post-forest chords; this is the second fourteen-face symmetry orbit. -/
theorem forestGaugeHaar_exact :
    surfaceForestGaugeHaar 3013286 ≈
      surfaceTopologicalHaarAmplitude 3013286 :=
  YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeMask2DFAA6.forestGaugeHaar_exact

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit2DFAA6

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit2DFAA6.forestGaugeHaar_exact
