/-
# Unconditional value of the constructive semicircle midpoint integral

The even midpoint subsequence is squeezed by the uniform endpoint sequences
from the frozen predecessors.  It is also a subsequence of the unconditional
full midpoint limit.  Constructive uniqueness of limits therefore identifies
that limit with the Machin value `halfPi`.
-/

import YMGap.Continuum.SemicircleEvenMidpointPairing

namespace YMGap.Continuum.SemicircleMidpointValueClosed

open YMGap.Constructive
open YMGap.Continuum.SemicircleIntegral
open YMGap.Continuum.SemicircleBoundClosed
open YMGap.Continuum.SemicirclePolygonMidpointBridge
open YMGap.Continuum.SemicircleUniformEndpointConvergence
open YMGap.Continuum.SemicircleEvenMidpointPairing

/-- The exact even midpoint subsequence converges to the Machin value. -/
theorem evenMidSeq_converges_halfPi :
    CReal.ConvergesTo evenMidSeq Pi.halfPi := by
  apply convergesTo_of_limitBracket
    unitRightSeq_converges_halfPi unitLeftSeq_converges_halfPi
  exact evenMidSeq_limitBracket

/-- The same even subsequence inherits the already-proved full midpoint
sequence limit. -/
theorem evenMidSeq_converges_semiInt :
    CReal.ConvergesTo evenMidSeq semiInt := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := semiInt_converges epsilon hepsilon
  refine ⟨N, fun M hM => ?_⟩
  unfold evenMidSeq
  exact hN (2*M+1) (by omega)

/-- The constructive midpoint integral is exactly `pi/2`. -/
theorem semiInt_eq_halfPi : CReal.Equiv semiInt Pi.halfPi :=
  CReal.Equiv_of_limit_of_equal
    (fun M => CReal.Equiv.refl (evenMidSeq M))
    evenMidSeq_converges_semiInt
    evenMidSeq_converges_halfPi

/-- The original full midpoint sequence, not merely a subsequence, converges
to `pi/2`. -/
theorem seqSemi_converges_halfPi :
    CReal.ConvergesTo seqSemi Pi.halfPi :=
  YMGap.Continuum.SemicircleAtanAddition.convergesTo_of_equiv
    semiInt_converges semiInt_eq_halfPi

end YMGap.Continuum.SemicircleMidpointValueClosed

#print axioms YMGap.Continuum.SemicircleMidpointValueClosed.evenMidSeq_converges_halfPi
#print axioms YMGap.Continuum.SemicircleMidpointValueClosed.evenMidSeq_converges_semiInt
#print axioms YMGap.Continuum.SemicircleMidpointValueClosed.semiInt_eq_halfPi
#print axioms YMGap.Continuum.SemicircleMidpointValueClosed.seqSemi_converges_halfPi
