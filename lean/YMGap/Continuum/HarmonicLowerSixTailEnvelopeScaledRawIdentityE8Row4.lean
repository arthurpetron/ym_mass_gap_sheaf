/-
# E8 scaled raw identity: mode row 4
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row4

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE8ScaledRaw_row4 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE8ScaledRawRows 4) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE8StructuredRawRows 4)) = true := by
  rfl

#print axioms tailEnvelopeE8ScaledRaw_row4

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row4
