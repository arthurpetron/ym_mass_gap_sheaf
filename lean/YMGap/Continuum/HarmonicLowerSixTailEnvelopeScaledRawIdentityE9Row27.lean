/-
# E9 scaled raw identity: mode row 27
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row27

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE9ScaledRaw_row27 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE9ScaledRawRows 27) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE9StructuredRawRows 27)) = true := by
  rfl

#print axioms tailEnvelopeE9ScaledRaw_row27

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row27
