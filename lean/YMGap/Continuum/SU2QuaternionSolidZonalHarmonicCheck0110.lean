/- Combined selected-head differential certificate for orientation 0110. -/

import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0110Laplacian
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0110Self

namespace YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0110

open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicBase
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0110Laplacian
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0110Self

theorem certificate0110 :
    ExposedDifferentialCertificate false true true false := by
  constructor
  · exact laplacian0110
  · exact self0110

end YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0110

#print axioms YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0110.certificate0110
