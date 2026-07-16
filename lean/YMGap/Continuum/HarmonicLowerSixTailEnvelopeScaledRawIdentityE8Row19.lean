/-
# E8 scaled raw identity: mode row 19
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row19

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE8ScaledRaw_row19 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE8ScaledRawRows 19) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE8StructuredRawRows 19)) = true := by
  rfl

#print axioms tailEnvelopeE8ScaledRaw_row19

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row19
