/-
Mode-sensitive seventh-order lower polynomial for the finite-Hermite
remainder.

Unlike the refuted uniform inverse-cube payment, this carrier retains the
exact mode-dependent seventh-order error at both adjacent scales.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticSquareExactWindow

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLower

set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixCubicEnvelope
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSeptic
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticFluxSign
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticSquareExactWindow
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticSquareWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.RGTransport

/-- Explicit lower polynomial with the exact mode-dependent seventh-order
errors retained. -/
def lowerSixHermiteRemainderTaylor6ExactErrorLowerPolynomial
    (k n : Nat) : Q' :=
  let D := Q'.ofNat (k + 2)
  let A := Q'.ofNat (n + 1)
  let N := Q'.ofNat n
  let N2 := Q'.ofNat (n * n)
  let T0 := rootSlopeTaylor6 (harmU k) n
  let T1 := rootSlopeTaylor6 (harmU (k + 1)) n
  let E0 := rootSlopeTaylor6Error (harmU k) n
  let E1 := rootSlopeTaylor6Error (harmU (k + 1)) n
  let C :=
    Q'.ofNat (k + 3) * lowerSixQuadraticTaylorFactor k n *
        (Q'.ofNat 4 * (T1 * T1 + -(Q'.ofNat 4 * E1)) +
          -(lowerSixDirichletProfile (k + 1) * N2)) +
      -(D *
        (Q'.ofNat 4 * (T0 * T0 + Q'.ofNat 3 * E0) +
          -(lowerSixDirichletProfile k * N2)))
  let J := fun m => lowerSixDiscreteHermiteFluxPoly D (Q'.ofNat m)
  (A * A) *
      (Q'.ofNat 48 * RingNormaliser.qpow D 4 * C +
        J n + -(Q'.ofNat 6 * RingNormaliser.qpow D 3)) +
    -(((N + -T0) * (N + -T0)) * J (n + 1))

private theorem ringQpow_nonnegative {a : Q'} (ha : (0 : Q') ≤ a) :
    ∀ n, (0 : Q') ≤ RingNormaliser.qpow a n
  | 0 => by
      show (0 : Q') ≤ (1 : Q')
      decide
  | n + 1 => Q'.mul_nonneg _ _ (ringQpow_nonnegative ha n) ha

private theorem lowerSixQuadraticTaylorFactor_nonnegative (k n : Nat) :
    (0 : Q') ≤ lowerSixQuadraticTaylorFactor k n := by
  have hex : (0 : Q') ≤ lowerSixDriftExcess k :=
    lowerSixDriftExcess_nonnegative k
  have hlin : (0 : Q') ≤ lowerSixWeightDriftFloor k n := by
    unfold lowerSixWeightDriftFloor
    exact Q'.zero_le_add _ _ (by decide)
      (Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _) hex)
  have hquad : (0 : Q') ≤ lowerSixWeightDriftQuadratic k n := by
    unfold lowerSixWeightDriftQuadratic
    exact Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
      (Q'.mul_nonneg _ _ hex hex)
  unfold lowerSixQuadraticTaylorFactor
  exact Q'.zero_le_add _ _ hlin hquad

/-- The mode-sensitive explicit lower polynomial lies below the exact
cleared slope polynomial on the physical left prefix. -/
theorem lowerSixHermiteRemainderTaylor6ExactErrorLowerPolynomial_le_actual
    {k n : Nat} (hk : 390 ≤ k) (hn : n ≤ thetaWindowLeft k) :
    lowerSixHermiteRemainderTaylor6ExactErrorLowerPolynomial k n ≤
      lowerSixHermiteRemainderSlopePolynomial k n
        (thetaRootSlope k n) (thetaRootSlope (k + 1) n) := by
  let D := Q'.ofNat (k + 2)
  let A := Q'.ofNat (n + 1)
  let N := Q'.ofNat n
  let N2 := Q'.ofNat (n * n)
  let S0 := thetaRootSlope k n
  let S1 := thetaRootSlope (k + 1) n
  let T0 := rootSlopeTaylor6 (harmU k) n
  let T1 := rootSlopeTaylor6 (harmU (k + 1)) n
  let E0 := rootSlopeTaylor6Error (harmU k) n
  let E1 := rootSlopeTaylor6Error (harmU (k + 1)) n
  let F := lowerSixQuadraticTaylorFactor k n
  let P0 := lowerSixDirichletProfile k * N2
  let P1 := lowerSixDirichletProfile (k + 1) * N2
  let J := fun m => lowerSixDiscreteHermiteFluxPoly D (Q'.ofNat m)
  let Cactual :=
    Q'.ofNat (k + 3) * F * (Q'.ofNat 4 * (S1 * S1) + -P1) +
      -(D * (Q'.ofNat 4 * (S0 * S0) + -P0))
  let Clower :=
    Q'.ofNat (k + 3) * F *
        (Q'.ofNat 4 * (T1 * T1 + -(Q'.ofNat 4 * E1)) + -P1) +
      -(D * (Q'.ofNat 4 * (T0 * T0 + Q'.ofNat 3 * E0) + -P0))
  have hnextSq : T1 * T1 + -(Q'.ofNat 4 * E1) ≤ S1 * S1 := by
    dsimp only [T1, E1, S1]
    exact lowerSixTaylor6Next_square_sub_four_exactError_le_ThetaRootSlope_square
      hk hn
  have holdSq : S0 * S0 ≤ T0 * T0 + Q'.ofNat 3 * E0 := by
    dsimp only [S0, T0, E0]
    exact lowerSixThetaRootSlope_square_le_Taylor6_square_add_three_exactError
      hk hn
  have hfluxSq : (N + -S0) * (N + -S0) ≤
      (N + -T0) * (N + -T0) := by
    dsimp only [N, S0, T0]
    exact lowerSixOldFluxSlope_square_le_Taylor6Flux_square k n
  have hF0 : (0 : Q') ≤ F := by
    dsimp only [F]
    exact lowerSixQuadraticTaylorFactor_nonnegative k n
  have hcoef0 : (0 : Q') ≤ Q'.ofNat (k + 3) * F :=
    Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _) hF0
  have hfourNext : Q'.ofNat 4 *
        (T1 * T1 + -(Q'.ofNat 4 * E1)) ≤ Q'.ofNat 4 * (S1 * S1) :=
    Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 4) hnextSq (by decide)
  have hnextInner :
      Q'.ofNat 4 * (T1 * T1 + -(Q'.ofNat 4 * E1)) + -P1 ≤
        Q'.ofNat 4 * (S1 * S1) + -P1 :=
    Q'.add_le_add_right _ _ (-P1) hfourNext
  have hnextTerm :
      (Q'.ofNat (k + 3) * F) *
          (Q'.ofNat 4 * (T1 * T1 + -(Q'.ofNat 4 * E1)) + -P1) ≤
        (Q'.ofNat (k + 3) * F) *
          (Q'.ofNat 4 * (S1 * S1) + -P1) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hnextInner hcoef0
  have hfourOld : Q'.ofNat 4 * (S0 * S0) ≤
      Q'.ofNat 4 * (T0 * T0 + Q'.ofNat 3 * E0) :=
    Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 4) holdSq (by decide)
  have holdInner : Q'.ofNat 4 * (S0 * S0) + -P0 ≤
      Q'.ofNat 4 * (T0 * T0 + Q'.ofNat 3 * E0) + -P0 :=
    Q'.add_le_add_right _ _ (-P0) hfourOld
  have hD0 : (0 : Q') ≤ D := by
    dsimp only [D]
    exact HeatKernelRGStep.zero_le_ofNat _
  have holdMul : D * (Q'.ofNat 4 * (S0 * S0) + -P0) ≤
      D * (Q'.ofNat 4 * (T0 * T0 + Q'.ofNat 3 * E0) + -P0) :=
    Q'.mul_le_mul_of_nonneg_left _ _ D holdInner hD0
  have holdTerm :
      -(D * (Q'.ofNat 4 * (T0 * T0 + Q'.ofNat 3 * E0) + -P0)) ≤
        -(D * (Q'.ofNat 4 * (S0 * S0) + -P0)) :=
    Q'.neg_le_neg holdMul
  have hC : Clower ≤ Cactual := by
    dsimp only [Clower, Cactual]
    exact Q'.add_le_add hnextTerm holdTerm
  have hD4 : (0 : Q') ≤ RingNormaliser.qpow D 4 :=
    ringQpow_nonnegative hD0 4
  have h48D4 : (0 : Q') ≤ Q'.ofNat 48 * RingNormaliser.qpow D 4 :=
    Q'.mul_nonneg _ _ (by decide) hD4
  have hX : Q'.ofNat 48 * RingNormaliser.qpow D 4 * Clower ≤
      Q'.ofNat 48 * RingNormaliser.qpow D 4 * Cactual :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hC h48D4
  have hinner :
      Q'.ofNat 48 * RingNormaliser.qpow D 4 * Clower +
          J n + -(Q'.ofNat 6 * RingNormaliser.qpow D 3) ≤
        Q'.ofNat 48 * RingNormaliser.qpow D 4 * Cactual +
          J n + -(Q'.ofNat 6 * RingNormaliser.qpow D 3) :=
    Q'.add_le_add_right _ _ _ (Q'.add_le_add_right _ _ (J n) hX)
  have hA0 : (0 : Q') ≤ A * A :=
    Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
      (HeatKernelRGStep.zero_le_ofNat _)
  have hmain : (A * A) *
        (Q'.ofNat 48 * RingNormaliser.qpow D 4 * Clower +
          J n + -(Q'.ofNat 6 * RingNormaliser.qpow D 3)) ≤
      (A * A) *
        (Q'.ofNat 48 * RingNormaliser.qpow D 4 * Cactual +
          J n + -(Q'.ofNat 6 * RingNormaliser.qpow D 3)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hinner hA0
  have hJ0 : (0 : Q') ≤ J (n + 1) := by
    dsimp only [J, D]
    exact lowerSixDiscreteHermiteFluxPoly_next_nonnegative_large hk hn
  have hfluxMul : ((N + -S0) * (N + -S0)) * J (n + 1) ≤
      ((N + -T0) * (N + -T0)) * J (n + 1) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hfluxSq hJ0
  have hfluxNeg :
      -(((N + -T0) * (N + -T0)) * J (n + 1)) ≤
        -(((N + -S0) * (N + -S0)) * J (n + 1)) :=
    Q'.neg_le_neg hfluxMul
  have htotal := Q'.add_le_add hmain hfluxNeg
  unfold lowerSixHermiteRemainderTaylor6ExactErrorLowerPolynomial
    lowerSixHermiteRemainderSlopePolynomial
  dsimp only [D, A, N, N2, S0, S1, T0, T1, E0, E1, F, P0, P1,
    J, Cactual, Clower] at htotal ⊢
  exact htotal

/-- Positivity of the exact-error lower polynomial suffices for positivity
of the actual discrete Hermite remainder. -/
theorem lowerSixDiscreteHermiteRemainder_nonnegative_of_Taylor6ExactErrorLower
    {k n : Nat} (hk : 390 ≤ k) (hn : n ≤ thetaWindowLeft k)
    (hlower : (0 : Q') ≤
      lowerSixHermiteRemainderTaylor6ExactErrorLowerPolynomial k n) :
    (0 : Q') ≤ lowerSixDiscreteHermiteRemainder k n := by
  have hactual : (0 : Q') ≤
      lowerSixHermiteRemainderSlopePolynomial k n
        (thetaRootSlope k n) (thetaRootSlope (k + 1) n) :=
    Q'.le_trans' _ _ _ hlower
      (lowerSixHermiteRemainderTaylor6ExactErrorLowerPolynomial_le_actual hk hn)
  exact lowerSixDiscreteHermiteRemainder_nonnegative_of_slopePolynomial hactual

#print axioms lowerSixHermiteRemainderTaylor6ExactErrorLowerPolynomial_le_actual
#print axioms lowerSixDiscreteHermiteRemainder_nonnegative_of_Taylor6ExactErrorLower

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLower
