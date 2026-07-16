/-
# E8 scaled raw identity: mode row 3
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row3

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE8ScaledRaw_row3 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE8ScaledRawRows 3) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE8StructuredRawRows 3)) = true := by
  rfl

#print axioms tailEnvelopeE8ScaledRaw_row3

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row3
