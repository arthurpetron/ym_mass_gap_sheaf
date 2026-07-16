/-
# E9 scaled raw identity: mode row 4
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row4

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE9ScaledRaw_row4 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE9ScaledRawRows 4) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE9StructuredRawRows 4)) = true := by
  rfl

#print axioms tailEnvelopeE9ScaledRaw_row4

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row4
