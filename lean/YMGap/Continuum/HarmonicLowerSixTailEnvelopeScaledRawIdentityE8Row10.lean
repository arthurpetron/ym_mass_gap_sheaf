/-
# E8 scaled raw identity: mode row 10
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row10

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE8ScaledRaw_row10 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE8ScaledRawRows 10) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE8StructuredRawRows 10)) = true := by
  rfl

#print axioms tailEnvelopeE8ScaledRaw_row10

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row10
