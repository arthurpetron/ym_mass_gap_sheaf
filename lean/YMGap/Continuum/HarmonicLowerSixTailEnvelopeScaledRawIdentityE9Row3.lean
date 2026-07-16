/-
# E9 scaled raw identity: mode row 3
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row3

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE9ScaledRaw_row3 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE9ScaledRawRows 3) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE9StructuredRawRows 3)) = true := by
  rfl

#print axioms tailEnvelopeE9ScaledRaw_row3

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row3
