/- Combined selected-head differential certificate for orientation 0011. -/

import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0011Laplacian
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0011Self

namespace YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0011

open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicBase
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0011Laplacian
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0011Self

theorem certificate0011 :
    ExposedDifferentialCertificate false false true true := by
  constructor
  · exact laplacian0011
  · exact self0011

end YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0011

#print axioms YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0011.certificate0011
