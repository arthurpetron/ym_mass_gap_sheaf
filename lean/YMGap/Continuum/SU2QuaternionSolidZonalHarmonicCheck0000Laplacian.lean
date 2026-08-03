/- Exact selected-head scalar Laplacian certificate for the all-forward word. -/

import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicBase

namespace YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0000Laplacian

set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar

theorem laplacian0000 :
    RatPolyCoeffEqv
      (headLaplacian
        (exposedFourWord false false false false).scalar)
      polyZero := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide

end YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0000Laplacian

#print axioms YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0000Laplacian.laplacian0000
