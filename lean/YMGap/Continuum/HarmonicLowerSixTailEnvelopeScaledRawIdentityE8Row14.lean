/-
# E8 scaled raw identity: mode row 14
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row14

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE8ScaledRaw_row14 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE8ScaledRawRows 14) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE8StructuredRawRows 14)) = true := by
  rfl

#print axioms tailEnvelopeE8ScaledRaw_row14

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row14
