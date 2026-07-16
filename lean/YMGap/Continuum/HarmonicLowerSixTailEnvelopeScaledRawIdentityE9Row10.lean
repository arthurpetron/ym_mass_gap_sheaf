/-
# E9 scaled raw identity: mode row 10
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row10

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE9ScaledRaw_row10 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE9ScaledRawRows 10) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE9StructuredRawRows 10)) = true := by
  rfl

#print axioms tailEnvelopeE9ScaledRaw_row10

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row10
