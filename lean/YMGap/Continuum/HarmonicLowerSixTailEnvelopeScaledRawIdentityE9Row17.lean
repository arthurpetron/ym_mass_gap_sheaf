/-
# E9 scaled raw identity: mode row 17
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row17

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE9ScaledRaw_row17 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE9ScaledRawRows 17) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE9StructuredRawRows 17)) = true := by
  rfl

#print axioms tailEnvelopeE9ScaledRaw_row17

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row17
