/-
# E9 scaled raw identity: mode row 9
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row9

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE9ScaledRaw_row9 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE9ScaledRawRows 9) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE9StructuredRawRows 9)) = true := by
  rfl

#print axioms tailEnvelopeE9ScaledRaw_row9

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row9
