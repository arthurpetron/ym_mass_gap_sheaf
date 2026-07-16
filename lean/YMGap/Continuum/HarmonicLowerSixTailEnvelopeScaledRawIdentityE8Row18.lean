/-
# E8 scaled raw identity: mode row 18
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row18

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE8ScaledRaw_row18 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE8ScaledRawRows 18) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE8StructuredRawRows 18)) = true := by
  rfl

#print axioms tailEnvelopeE8ScaledRaw_row18

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row18
