/- Proof-shared forest-gauge value for orbit representative 0x2533cb.

The exhaustive mask campaign already kernel-checks this representative.  This
compatibility module reuses that proof instead of normalizing the same closed
computation a second time.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeMask2533CB

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit2533CB

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge

local infix:50 " ≈ " => Q'.eqv

/-- Two six-face components: twelve faces, sixteen vertices, twenty-four
edges, two primal components, and ten post-forest chords. -/
theorem forestGaugeHaar_exact :
    surfaceForestGaugeHaar 2438091 ≈
      surfaceTopologicalHaarAmplitude 2438091 :=
  YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeMask2533CB.forestGaugeHaar_exact

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit2533CB

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit2533CB.forestGaugeHaar_exact
