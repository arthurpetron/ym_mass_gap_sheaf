/-
# E9 scaled raw identity: mode row 2
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row2

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE9ScaledRaw_row2 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE9ScaledRawRows 2) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE9StructuredRawRows 2)) = true := by
  rfl

#print axioms tailEnvelopeE9ScaledRaw_row2

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row2
