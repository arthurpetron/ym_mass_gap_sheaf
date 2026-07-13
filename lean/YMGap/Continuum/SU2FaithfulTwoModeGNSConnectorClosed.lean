/-
# Unconditional faithful two-mode GNS connector

The frozen connector identified `SemiConvergesToHalfPi` as its sole analytic
normalization premise.  The midpoint value closure now supplies that premise,
so the normalized Riemann Gram agrees unconditionally with the explicit
positive-definite rational two-mode GNS form.
-/

import YMGap.Continuum.SU2FiniteHaarRiemannTwoModeClosed
import YMGap.Continuum.SU2FaithfulTwoModeGNSConnector

namespace YMGap.Continuum.SU2FaithfulTwoModeGNSConnectorClosed

open YMGap.Constructive
open YMGap.Continuum.SU2FiniteHaarRiemannTwoMode
open YMGap.Continuum.SU2FaithfulTwoModeGNSConnector

/-- The normalized midpoint-Riemann Gram is exactly the constructive-real lift
of the nondegenerate rational two-mode GNS Gram, with no residual premise. -/
theorem faithful_normalized_moment_matches_gns (i j : Fin 2) :
    CReal.Equiv (normalizedMoment i j)
      (CReal.ofQ' (faithfulModeGNS.B (modeVector i) (modeVector j))) :=
  YMGap.Continuum.SU2FaithfulTwoModeGNSConnector.faithful_normalized_moment_matches_gns
    SU2FiniteHaarRiemannTwoModeClosed.semiConvergesToHalfPi i j

end YMGap.Continuum.SU2FaithfulTwoModeGNSConnectorClosed

#print axioms YMGap.Continuum.SU2FaithfulTwoModeGNSConnectorClosed.faithful_normalized_moment_matches_gns
