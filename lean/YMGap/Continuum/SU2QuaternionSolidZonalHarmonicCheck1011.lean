/- Combined selected-head differential certificate for orientation 1011. -/

import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1011Laplacian
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1011Self

namespace YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1011

open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicBase
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1011Laplacian
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1011Self

theorem certificate1011 :
    ExposedDifferentialCertificate true false true true := by
  constructor
  · exact laplacian1011
  · exact self1011

end YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1011

#print axioms YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck1011.certificate1011
