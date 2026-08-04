/- Proof-shared forest-gauge value for orbit representative 0x04ab33.

The exhaustive mask campaign already kernel-checks this representative.  This
compatibility module reuses that proof instead of normalizing the same closed
computation a second time.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeMask04AB33

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit04AB33

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge

local infix:50 " ≈ " => Q'.eqv

/-- Ten faces, twelve vertices, twenty edges, and nine post-forest chords. -/
theorem forestGaugeHaar_exact :
    surfaceForestGaugeHaar 305971 ≈
      surfaceTopologicalHaarAmplitude 305971 :=
  YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeMask04AB33.forestGaugeHaar_exact

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit04AB33

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit04AB33.forestGaugeHaar_exact
