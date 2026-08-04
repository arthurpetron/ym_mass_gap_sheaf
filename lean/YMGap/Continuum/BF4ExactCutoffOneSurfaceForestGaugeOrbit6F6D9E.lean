/- Proof-shared forest-gauge value for orbit representative 0x6f6d9e.

The exhaustive mask campaign already kernel-checks this representative.  This
compatibility module reuses that proof instead of normalizing the same closed
computation a second time; in particular it does not duplicate the
2,694-line staged trace.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeMask6F6D9E

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit6F6D9E

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge

local infix:50 " ≈ " => Q'.eqv

/-- Sixteen faces, sixteen vertices, thirty-two edges, and seventeen
post-forest chords. -/
theorem forestGaugeHaar_exact :
    surfaceForestGaugeHaar 7302558 ≈
      surfaceTopologicalHaarAmplitude 7302558 :=
  YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeMask6F6D9E.forestGaugeHaar_exact

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit6F6D9E

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeOrbit6F6D9E.forestGaugeHaar_exact
