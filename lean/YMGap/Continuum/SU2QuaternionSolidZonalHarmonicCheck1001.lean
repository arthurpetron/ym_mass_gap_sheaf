/- Combined selected-head differential certificate for orientation 1001. -/

import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1001Laplacian
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1001Self

namespace YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1001

open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicBase
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1001Laplacian
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1001Self

theorem certificate1001 :
    ExposedDifferentialCertificate true false false true := by
  constructor
  · exact laplacian1001
  · exact self1001

end YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1001

#print axioms YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1001.certificate1001
