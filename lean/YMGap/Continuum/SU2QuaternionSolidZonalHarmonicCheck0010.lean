/- Combined selected-head differential certificate for orientation 0010. -/

import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0010Laplacian
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0010Self

namespace YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0010

open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicBase
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0010Laplacian
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0010Self

theorem certificate0010 :
    ExposedDifferentialCertificate false false true false := by
  constructor
  · exact laplacian0010
  · exact self0010

end YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0010

#print axioms YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0010.certificate0010
