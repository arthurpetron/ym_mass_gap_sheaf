/-
# E9 scaled raw identity: mode row 6
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row6

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE9ScaledRaw_row6 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE9ScaledRawRows 6) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE9StructuredRawRows 6)) = true := by
  rfl

#print axioms tailEnvelopeE9ScaledRaw_row6

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row6
