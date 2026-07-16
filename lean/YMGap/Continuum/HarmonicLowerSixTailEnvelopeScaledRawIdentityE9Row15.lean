/-
# E9 scaled raw identity: mode row 15
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row15

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE9ScaledRaw_row15 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE9ScaledRawRows 15) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE9StructuredRawRows 15)) = true := by
  rfl

#print axioms tailEnvelopeE9ScaledRaw_row15

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row15
