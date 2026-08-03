/- Combined selected-head differential certificate for orientation 0001. -/

import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0001Laplacian
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0001Self

namespace YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0001

open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicBase
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0001Laplacian
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0001Self

theorem certificate0001 :
    ExposedDifferentialCertificate false false false true := by
  constructor
  · exact laplacian0001
  · exact self0001

end YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0001

#print axioms YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0001.certificate0001
