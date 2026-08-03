/- Combined selected-head differential certificate for orientation 0111. -/

import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0111Laplacian
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0111Self

namespace YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0111

open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicBase
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0111Laplacian
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0111Self

theorem certificate0111 :
    ExposedDifferentialCertificate false true true true := by
  constructor
  · exact laplacian0111
  · exact self0111

end YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0111

#print axioms YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0111.certificate0111
