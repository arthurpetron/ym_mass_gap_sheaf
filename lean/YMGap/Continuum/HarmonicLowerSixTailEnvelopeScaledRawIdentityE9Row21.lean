/-
# E9 scaled raw identity: mode row 21
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row21

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE9ScaledRaw_row21 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE9ScaledRawRows 21) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE9StructuredRawRows 21)) = true := by
  rfl

#print axioms tailEnvelopeE9ScaledRaw_row21

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row21
