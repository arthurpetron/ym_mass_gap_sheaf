/- Combined selected-head differential certificate for orientation 1101. -/

import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1101Laplacian
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1101Self

namespace YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1101

open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicBase
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1101Laplacian
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1101Self

theorem certificate1101 :
    ExposedDifferentialCertificate true true false true := by
  constructor
  · exact laplacian1101
  · exact self1101

end YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1101

#print axioms YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1101.certificate1101
