/-
# Exact fences for two false lower-six shortcuts at `k = 390`

The regenerated projective certificates reach the physical splice at
`k = 390`, but two estimates from the older large-scale proof do not.  These
closed counterexamples keep those failed estimates out of future threshold
lowering arguments.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMoment

namespace YMGap.Continuum.HarmonicLowerSixProduction390ShortcutFences

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMoment
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

/-- The last prefix index at `k = 390` is `j = 34`.  The old eighth-window
estimate would require `8 * (2 * (j+1) + 1) <= k+3`, which here is the false
closed inequality `568 <= 393`. -/
theorem oldQuarterWindowObligation_fails_at_k390_j34 :
    thetaWindowRight 390 = 35 ∧
      34 < thetaWindowRight 390 ∧
        ¬ (8 * (2 * (34 + 1) + 1) ≤ 390 + 3) := by
  decide

/-- The old cubic-debt moment coefficient comparison is also false at the
new splice.  This is its exact `k = 390` specialization, with denominators
and all powers retained in the constructive rational substrate. -/
theorem oldCubicDebtMomentCoefficient_fails_at_k390 :
    ¬ (Q'.ofNat 40320 *
          (RingNormaliser.qpow (Q'.ofNat (390 + 2)) 4 *
            (lowerSixPrefixCubicDebtScalar 390 *
              RingNormaliser.qpow (Q'.ofNat (390 + 3)) 4)) ≤
        Q'.ofNat 2916 *
          RingNormaliser.qpow (Q'.ofNat (390 + 2)) 3) := by
  unfold lowerSixPrefixCubicDebtScalar lowerSixDirichletProfile
    lowerSixDriftExcess driftDen harmU unit RingNormaliser.qpow
  decide

/-- The literal cubic-debt moment coefficient remains false immediately
below its sharp uniform cutoff.  This prevents any future proof from claiming
that the old coefficient route itself splices at `k = 1329`. -/
theorem oldCubicDebtMomentCoefficient_fails_at_k1329 :
    ¬ (Q'.ofNat 40320 *
          (RingNormaliser.qpow (Q'.ofNat (1329 + 2)) 4 *
            (lowerSixPrefixCubicDebtScalar 1329 *
              RingNormaliser.qpow (Q'.ofNat (1329 + 3)) 4)) ≤
        Q'.ofNat 2916 *
          RingNormaliser.qpow (Q'.ofNat (1329 + 2)) 3) := by
  unfold lowerSixPrefixCubicDebtScalar lowerSixDirichletProfile
    lowerSixDriftExcess driftDen harmU unit RingNormaliser.qpow
  decide

/-- At the next scale the same exact coefficient comparison is true. -/
theorem oldCubicDebtMomentCoefficient_holds_at_k1330 :
    Q'.ofNat 40320 *
          (RingNormaliser.qpow (Q'.ofNat (1330 + 2)) 4 *
            (lowerSixPrefixCubicDebtScalar 1330 *
              RingNormaliser.qpow (Q'.ofNat (1330 + 3)) 4)) ≤
        Q'.ofNat 2916 *
          RingNormaliser.qpow (Q'.ofNat (1330 + 2)) 3 := by
  unfold lowerSixPrefixCubicDebtScalar lowerSixDirichletProfile
    lowerSixDriftExcess driftDen harmU unit RingNormaliser.qpow
  decide

#print axioms oldQuarterWindowObligation_fails_at_k390_j34
#print axioms oldCubicDebtMomentCoefficient_fails_at_k390
#print axioms oldCubicDebtMomentCoefficient_fails_at_k1329
#print axioms oldCubicDebtMomentCoefficient_holds_at_k1330

end YMGap.Continuum.HarmonicLowerSixProduction390ShortcutFences
