/-
# E8 scaled raw identity: mode row 20
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row20

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE8ScaledRaw_row20 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE8ScaledRawRows 20) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE8StructuredRawRows 20)) = true := by
  rfl

#print axioms tailEnvelopeE8ScaledRaw_row20

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row20
