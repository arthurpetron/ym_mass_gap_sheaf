/-
# E9 scaled raw identity: mode row 7
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row7

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE9ScaledRaw_row7 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE9ScaledRawRows 7) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE9StructuredRawRows 7)) = true := by
  rfl

#print axioms tailEnvelopeE9ScaledRaw_row7

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row7
