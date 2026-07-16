/-
# E8 scaled raw identity: mode row 22
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row22

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE8ScaledRaw_row22 :
    decide
      (RingNormaliser.canon
          (rawRowAt tailEnvelopeE8ScaledRawRows 22) =
        RingNormaliser.canon
          (rawRowAt tailEnvelopeE8StructuredRawRows 22)) = true := by
  rfl

#print axioms tailEnvelopeE8ScaledRaw_row22

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row22
