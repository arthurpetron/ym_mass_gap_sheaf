/-
# Unconditional finite-Haar two-mode normalization

The constructive semicircle midpoint value is now closed.  This successor
module discharges every `SemiConvergesToHalfPi` premise exposed by
`SU2FiniteHaarRiemannTwoMode` without changing that frozen interface.
-/

import YMGap.Continuum.SemicircleMidpointValueClosed
import YMGap.Continuum.SU2FiniteHaarRiemannTwoMode

namespace YMGap.Continuum.SU2FiniteHaarRiemannTwoModeClosed

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CosIntegralReduction
open YMGap.Continuum.SemicircleValue
open YMGap.Continuum.SU2FiniteHaarRiemannTwoMode

/-- The named semicircle convergence residual is now inhabited by the
machine-checked midpoint value theorem. -/
theorem semiConvergesToHalfPi : SemiConvergesToHalfPi :=
  SemicircleMidpointValueClosed.seqSemi_converges_halfPi

/-- Every diagonal entry of the normalized faithful two-mode Riemann Gram is
unconditionally one. -/
theorem normalized_diagonal (i : Fin 2) :
    CReal.Equiv (normalizedMoment i i) (CReal.ofQ' (1 : Q')) :=
  normalized_diagonal_of_semiConverges semiConvergesToHalfPi i

/-- The genuine base midpoint-Riemann provenance is available for every
legacy value table; its former residual was exactly the now-proved
semicircle convergence theorem. -/
theorem baseRiemannProvenance (F : CosIntegralFamily) :
    BaseRiemannProvenance F :=
  (baseRiemannProvenance_iff_semiConverges F).2 semiConvergesToHalfPi

end YMGap.Continuum.SU2FiniteHaarRiemannTwoModeClosed

#print axioms YMGap.Continuum.SU2FiniteHaarRiemannTwoModeClosed.semiConvergesToHalfPi
#print axioms YMGap.Continuum.SU2FiniteHaarRiemannTwoModeClosed.normalized_diagonal
#print axioms YMGap.Continuum.SU2FiniteHaarRiemannTwoModeClosed.baseRiemannProvenance
