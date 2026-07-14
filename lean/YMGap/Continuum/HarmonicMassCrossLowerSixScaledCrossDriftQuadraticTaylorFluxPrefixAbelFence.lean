/-
The ordinary first-order suffix-Abel route does not prove positivity of the
exact-minus-quadratic Taylor correction.  At the first uniform scale, the
old-Gaussian-weighted next carrier already has a strictly negative suffix,
although the complete correction is strictly positive.  Thus a successful
proof must retain the genuinely third-order growth of the Taylor remainder
(or an equivalent higher-moment pairing); monotonicity of the multiplier
alone is insufficient.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxSummedEnvelope

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixAbelFence

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxSummedEnvelope
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

/-- A suffix of the old-Gaussian-weighted next-scale Abel carriers.  These
are the signed cells multiplied by the increasing Taylor remainder in the
prefix correction. -/
def lowerSixTaylorRawCarrierSuffix (k start : Nat) : Q' :=
  finSum
    (fun j => lowerSixAbelWeight k (start + j) *
      lowerSixAbelCarrier (k + 1) (start + j))
    (thetaWindowRight k - start)

/-- Exact fence against the most immediate monotone-weight Abel proof: at
`k = 247`, the suffix beginning with ordinary mode six is negative. -/
theorem lowerSixTaylorRawCarrierSuffix_negative_k247_start5 :
    ¬ ((0 : Q') ≤ lowerSixTaylorRawCarrierSuffix 247 5) := by
  unfold lowerSixTaylorRawCarrierSuffix lowerSixAbelWeight
    lowerSixModeWeight lowerSixAbelCarrier lowerSixModeCarrier
    lowerSixDirichletProfile thetaRootSlope harmW harmU oneSub unit qpow
    finSum
  decide

/-- The failure above is specific to the first-order Abel mechanism, not to
the desired correction: the exact correction is already positive at that
same scale.  Its third-and-higher binomial growth is therefore load-bearing. -/
theorem lowerSixQuadraticTaylorPrefixRemainder_nonnegative_k247 :
    (0 : Q') ≤ lowerSixQuadraticTaylorPrefixRemainder 247 := by
  unfold lowerSixQuadraticTaylorPrefixRemainder
    lowerSixQuadraticTaylorAbelRemainder lowerSixAbelWeight
    lowerSixModeWeight lowerSixAbelCarrier lowerSixModeCarrier
    lowerSixDirichletProfile lowerSixWeightDriftFactor
    lowerSixQuadraticTaylorFactor lowerSixWeightDriftFloor
    lowerSixWeightDriftQuadratic lowerSixQuadraticCoeff lowerSixDriftExcess
    thetaRootSlope driftRatio driftDen harmW harmU oneSub unit qpow finSum
  decide

#print axioms lowerSixTaylorRawCarrierSuffix_negative_k247_start5
#print axioms lowerSixQuadraticTaylorPrefixRemainder_nonnegative_k247

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixAbelFence
