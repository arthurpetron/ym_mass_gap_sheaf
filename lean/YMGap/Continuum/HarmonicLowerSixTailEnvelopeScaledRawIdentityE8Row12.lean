/-
# E8 scaled raw identity: mode row 12
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row12

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE8ScaledRaw_row12 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE8ScaledRawRows 12) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE8StructuredRawRows 12)) = true := by
  rfl

#print axioms tailEnvelopeE8ScaledRaw_row12

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row12
