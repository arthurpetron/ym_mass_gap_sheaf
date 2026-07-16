/-
# E9 scaled raw identity: mode row 14
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row14

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE9ScaledRaw_row14 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE9ScaledRawRows 14) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE9StructuredRawRows 14)) = true := by
  rfl

#print axioms tailEnvelopeE9ScaledRaw_row14

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row14
