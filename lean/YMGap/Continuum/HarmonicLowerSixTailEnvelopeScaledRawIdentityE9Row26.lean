/-
# E9 scaled raw identity: mode row 26
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row26

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE9ScaledRaw_row26 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE9ScaledRawRows 26) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE9StructuredRawRows 26)) = true := by
  rfl

#print axioms tailEnvelopeE9ScaledRaw_row26

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row26
