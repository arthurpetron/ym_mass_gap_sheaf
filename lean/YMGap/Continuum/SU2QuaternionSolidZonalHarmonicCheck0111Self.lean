/- Exact selected-head self-gradient certificate for orientation 0111. -/

import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicBase

namespace YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0111Self

set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicBase

theorem self0111 :
    RatPolyCoeffEqv
      (headGradientDot
        (exposedFourWord false true true true).scalar
        (exposedFourWord false true true true).scalar)
      retainedThreeRadiusProduct := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide

end YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0111Self

#print axioms YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0111Self.self0111
