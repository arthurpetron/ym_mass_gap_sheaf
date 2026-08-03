/- Exact selected-head scalar Laplacian certificate for orientation 0001. -/

import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicBase

namespace YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0001Laplacian

set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar

theorem laplacian0001 :
    RatPolyCoeffEqv
      (headLaplacian
        (exposedFourWord false false false true).scalar)
      polyZero := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide

end YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0001Laplacian

#print axioms YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0001Laplacian.laplacian0001
