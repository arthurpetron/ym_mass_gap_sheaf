/- Combined selected-head differential certificate for orientation 0101. -/

import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0101Laplacian
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0101Self

namespace YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0101

open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicBase
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0101Laplacian
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0101Self

theorem certificate0101 :
    ExposedDifferentialCertificate false true false true := by
  constructor
  · exact laplacian0101
  · exact self0101

end YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0101

#print axioms YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0101.certificate0101
