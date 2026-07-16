/-
# E9 scaled raw identity: mode row 25
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row25

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE9ScaledRaw_row25 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE9ScaledRawRows 25) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE9StructuredRawRows 25)) = true := by
  rfl

#print axioms tailEnvelopeE9ScaledRaw_row25

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row25
