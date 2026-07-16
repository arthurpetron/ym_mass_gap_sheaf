/-
# E8 scaled raw identity: mode row 8
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row8

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE8ScaledRaw_row8 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE8ScaledRawRows 8) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE8StructuredRawRows 8)) = true := by
  rfl

#print axioms tailEnvelopeE8ScaledRaw_row8

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row8
