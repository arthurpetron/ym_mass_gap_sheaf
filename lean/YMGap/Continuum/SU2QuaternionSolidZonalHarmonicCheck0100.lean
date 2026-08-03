/- Combined selected-head differential certificate for orientation 0100. -/

import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0100Laplacian
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0100Self

namespace YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0100

open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicBase
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0100Laplacian
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0100Self

theorem certificate0100 :
    ExposedDifferentialCertificate false true false false := by
  constructor
  · exact laplacian0100
  · exact self0100

end YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0100

#print axioms YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0100.certificate0100
