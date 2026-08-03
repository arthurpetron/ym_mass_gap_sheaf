/- Exact selected-head self-gradient certificate for orientation 0110. -/

import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicBase

namespace YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0110Self

set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicBase

theorem self0110 :
    RatPolyCoeffEqv
      (headGradientDot
        (exposedFourWord false true true false).scalar
        (exposedFourWord false true true false).scalar)
      retainedThreeRadiusProduct := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide

end YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0110Self

#print axioms YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0110Self.self0110
