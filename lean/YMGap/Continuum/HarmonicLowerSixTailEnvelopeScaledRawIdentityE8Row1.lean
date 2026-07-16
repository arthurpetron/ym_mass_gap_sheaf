/-
# E8 scaled raw identity: mode row 1
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row1

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE8ScaledRaw_row1 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE8ScaledRawRows 1) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE8StructuredRawRows 1)) = true := by
  rfl

#print axioms tailEnvelopeE8ScaledRaw_row1

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row1
