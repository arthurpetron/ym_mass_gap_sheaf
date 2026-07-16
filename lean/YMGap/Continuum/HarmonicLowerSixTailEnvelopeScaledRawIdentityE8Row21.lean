/-
# E8 scaled raw identity: mode row 21
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row21

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE8ScaledRaw_row21 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE8ScaledRawRows 21) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE8StructuredRawRows 21)) = true := by
  rfl

#print axioms tailEnvelopeE8ScaledRaw_row21

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row21
