/-
# E9 scaled raw identity: mode row 19
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row19

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE9ScaledRaw_row19 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE9ScaledRawRows 19) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE9StructuredRawRows 19)) = true := by
  rfl

#print axioms tailEnvelopeE9ScaledRaw_row19

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row19
