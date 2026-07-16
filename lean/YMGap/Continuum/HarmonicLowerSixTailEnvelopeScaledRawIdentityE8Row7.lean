/-
# E8 scaled raw identity: mode row 7
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row7

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE8ScaledRaw_row7 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE8ScaledRawRows 7) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE8StructuredRawRows 7)) = true := by
  rfl

#print axioms tailEnvelopeE8ScaledRaw_row7

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row7
