/- Combined selected-head differential certificate for orientation 1100. -/

import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1100Laplacian
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1100Self

namespace YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1100

open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicBase
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1100Laplacian
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1100Self

theorem certificate1100 :
    ExposedDifferentialCertificate true true false false := by
  constructor
  · exact laplacian1100
  · exact self1100

end YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1100

#print axioms YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1100.certificate1100
