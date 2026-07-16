/-
# E9 scaled raw identity: mode row 24
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row24

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE9ScaledRaw_row24 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE9ScaledRawRows 24) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE9StructuredRawRows 24)) = true := by
  rfl

#print axioms tailEnvelopeE9ScaledRaw_row24

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row24
