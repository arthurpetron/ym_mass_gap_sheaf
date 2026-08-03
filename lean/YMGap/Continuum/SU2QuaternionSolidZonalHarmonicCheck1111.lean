/- Combined selected-head differential certificate for orientation 1111. -/

import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1111Laplacian
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1111Self

namespace YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1111

open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicBase
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1111Laplacian
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1111Self

theorem certificate1111 :
    ExposedDifferentialCertificate true true true true := by
  constructor
  · exact laplacian1111
  · exact self1111

end YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1111

#print axioms YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1111.certificate1111
