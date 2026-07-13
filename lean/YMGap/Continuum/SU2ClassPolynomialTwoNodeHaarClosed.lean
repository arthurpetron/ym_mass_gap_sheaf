/-
# Unconditional two-node polynomial/Riemann state agreement

The constructive semicircle value theorem removes the sole premise from the
retained two-mode state comparison in `SU2ClassPolynomialTwoNodeHaar`.  This
does not promote the two-node quadrature to full Haar integration: the frozen
counterexample at `chebPoly 4` remains in force.
-/

import YMGap.Continuum.SU2FaithfulTwoModeGNSConnectorClosed
import YMGap.Continuum.SU2ClassPolynomialTwoNodeHaar

namespace YMGap.Continuum.SU2ClassPolynomialTwoNodeHaarClosed

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2ClassPolynomialTwoNodeHaar
open YMGap.Continuum.SU2FiniteHaarRiemannTwoMode

/-- On the retained two-character sector, the normalized midpoint-Riemann
state and the exact positive two-node polynomial functional agree with no
residual premise. -/
theorem normalizedMoment_matches_twoNodeHaar (i j : Fin 2) :
    CReal.Equiv (normalizedMoment i j)
      (CReal.ofQ' (twoNodeHaar (pmul (polyMode i) (polyMode j)))) :=
  YMGap.Continuum.SU2ClassPolynomialTwoNodeHaar.normalizedMoment_matches_twoNodeHaar
    SU2FiniteHaarRiemannTwoModeClosed.semiConvergesToHalfPi i j

end YMGap.Continuum.SU2ClassPolynomialTwoNodeHaarClosed

#print axioms YMGap.Continuum.SU2ClassPolynomialTwoNodeHaarClosed.normalizedMoment_matches_twoNodeHaar
