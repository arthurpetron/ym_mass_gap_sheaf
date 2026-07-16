/-
# E8 scaled raw identity: mode row 23
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row23

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE8ScaledRaw_row23 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE8ScaledRawRows 23) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE8StructuredRawRows 23)) = true := by
  rfl

#print axioms tailEnvelopeE8ScaledRaw_row23

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row23
