/-
# E9 scaled raw identity: mode row 0
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row0

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE9ScaledRaw_row0 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE9ScaledRawRows 0) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE9StructuredRawRows 0)) = true := by
  rfl

#print axioms tailEnvelopeE9ScaledRaw_row0

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row0
