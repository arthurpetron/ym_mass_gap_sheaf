/- Combined selected-head differential certificate for orientation 1110. -/

import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1110Laplacian
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1110Self

namespace YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1110

open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicBase
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1110Laplacian
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1110Self

theorem certificate1110 :
    ExposedDifferentialCertificate true true true false := by
  constructor
  · exact laplacian1110
  · exact self1110

end YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1110

#print axioms YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1110.certificate1110
