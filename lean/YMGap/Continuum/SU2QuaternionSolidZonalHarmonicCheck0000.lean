/- Exact selected-head differential certificate for the all-forward word. -/

import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0000Laplacian
import YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0000Self

namespace YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0000

set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicBase
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0000Laplacian
open YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0000Self

theorem certificate0000 :
    ExposedDifferentialCertificate false false false false := by
  constructor
  · exact laplacian0000
  · exact self0000

end YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0000

#print axioms YMGap.Continuum.SU2QuaternionSolidZonalHarmonicCheck0000.certificate0000
