/- Combined selected-head differential certificate for orientation 1010. -/

import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1010Laplacian
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1010Self

namespace YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1010

open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicBase
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1010Laplacian
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1010Self

theorem certificate1010 :
    ExposedDifferentialCertificate true false true false := by
  constructor
  · exact laplacian1010
  · exact self1010

end YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1010

#print axioms YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1010.certificate1010
