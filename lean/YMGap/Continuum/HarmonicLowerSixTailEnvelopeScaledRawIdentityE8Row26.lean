/-
# E8 scaled raw identity: mode row 26
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row26

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE8ScaledRaw_row26 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE8ScaledRawRows 26) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE8StructuredRawRows 26)) = true := by
  rfl

#print axioms tailEnvelopeE8ScaledRaw_row26

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row26
