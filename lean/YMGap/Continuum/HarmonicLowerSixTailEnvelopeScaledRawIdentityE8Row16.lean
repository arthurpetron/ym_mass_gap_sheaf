/-
# E8 scaled raw identity: mode row 16
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row16

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE8ScaledRaw_row16 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE8ScaledRawRows 16) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE8StructuredRawRows 16)) = true := by
  rfl

#print axioms tailEnvelopeE8ScaledRaw_row16

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row16
