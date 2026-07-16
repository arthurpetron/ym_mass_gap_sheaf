/-
# E8 scaled raw identity: mode row 25
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row25

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE8ScaledRaw_row25 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE8ScaledRawRows 25) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE8StructuredRawRows 25)) = true := by
  rfl

#print axioms tailEnvelopeE8ScaledRaw_row25

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row25
