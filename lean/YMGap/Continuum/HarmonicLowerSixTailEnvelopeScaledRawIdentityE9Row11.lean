/-
# E9 scaled raw identity: mode row 11
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row11

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE9ScaledRaw_row11 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE9ScaledRawRows 11) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE9StructuredRawRows 11)) = true := by
  rfl

#print axioms tailEnvelopeE9ScaledRaw_row11

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row11
