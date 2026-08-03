/- Combined selected-head differential certificate for orientation 1000. -/

import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1000Laplacian
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1000Self

namespace YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1000

open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicBase
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1000Laplacian
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1000Self

theorem certificate1000 :
    ExposedDifferentialCertificate true false false false := by
  constructor
  · exact laplacian1000
  · exact self1000

end YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1000

#print axioms YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1000.certificate1000
