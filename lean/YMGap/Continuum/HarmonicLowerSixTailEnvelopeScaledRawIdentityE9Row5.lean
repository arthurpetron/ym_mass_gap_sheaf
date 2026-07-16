/-
# E9 scaled raw identity: mode row 5
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row5

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE9ScaledRaw_row5 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE9ScaledRawRows 5) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE9StructuredRawRows 5)) = true := by
  rfl

#print axioms tailEnvelopeE9ScaledRaw_row5

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row5
