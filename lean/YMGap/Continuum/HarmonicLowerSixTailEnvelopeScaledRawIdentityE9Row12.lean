/-
# E9 scaled raw identity: mode row 12
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row12

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE9ScaledRaw_row12 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE9ScaledRawRows 12) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE9StructuredRawRows 12)) = true := by
  rfl

#print axioms tailEnvelopeE9ScaledRaw_row12

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row12
