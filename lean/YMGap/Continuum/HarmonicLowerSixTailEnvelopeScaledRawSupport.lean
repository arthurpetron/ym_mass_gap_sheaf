/-
# Closed support checks for the sharded E8/E9 raw identities
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawSupport

open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeTaylorRaw
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem tailEnvelopeE8ScaledRaw_bound :
    rawFirstExponentBound 28 tailEnvelopeE8ScaledRawPolynomial = true := by
  rfl

theorem tailEnvelopeE9ScaledRaw_bound :
    rawFirstExponentBound 28 tailEnvelopeE9ScaledRawPolynomial = true := by
  rfl

theorem tailEnvelopeTaylor8PrefixRaw_bound :
    rawFirstExponentBound 19 tailEnvelopeTaylor8PrefixSquareRaw = true := by
  rfl

theorem tailEnvelopeTaylor9PrefixRaw_bound :
    rawFirstExponentBound 19 tailEnvelopeTaylor9PrefixSquareRaw = true := by
  rfl

theorem tailEnvelopeTaylorCommonStepRaw_bound :
    rawFirstExponentBound 10 tailEnvelopeTaylorCommonStepRaw = true := by
  rfl

#print axioms tailEnvelopeE8ScaledRaw_bound
#print axioms tailEnvelopeE9ScaledRaw_bound
#print axioms tailEnvelopeTaylor8PrefixRaw_bound
#print axioms tailEnvelopeTaylor9PrefixRaw_bound
#print axioms tailEnvelopeTaylorCommonStepRaw_bound

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawSupport
