/-
# E8 scaled raw identity: mode row 13
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row13

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE8ScaledRaw_row13 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE8ScaledRawRows 13) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE8StructuredRawRows 13)) = true := by
  rfl

#print axioms tailEnvelopeE8ScaledRaw_row13

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row13
