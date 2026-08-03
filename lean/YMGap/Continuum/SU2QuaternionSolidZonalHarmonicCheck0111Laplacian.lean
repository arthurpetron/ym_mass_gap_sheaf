/- Exact selected-head scalar Laplacian certificate for orientation 0111. -/

import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicBase

namespace YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0111Laplacian

set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar

theorem laplacian0111 :
    RatPolyCoeffEqv
      (headLaplacian
        (exposedFourWord false true true true).scalar)
      polyZero := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide

end YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0111Laplacian

#print axioms YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0111Laplacian.laplacian0111
