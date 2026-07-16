/-
# Pointwise lower-six second-flux certificate

This module closes the pointwise local inequality used by the lower-six tail
assembly.  The proof uses alternating eighth/ninth order rational Taylor
enclosures for the two adjacent harmonic powers and an exact polynomial
certificate on the physical tail corridor.
-/

import YMGap.Continuum.HarmonicLowerSixTailSlopeReduction
import YMGap.Continuum.HarmonicLowerSixTailTaylorNineCertificate
import YMGap.Continuum.HarmonicLowerSixTailSlopeFloorCertificate
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylorSeven
import YMGap.Continuum.HarmonicLowerSixTailSlopeFloorPhysicalBridge
import YMGap.RG.PolylogTail

namespace YMGap.Continuum.HarmonicLowerSixTailSecondFluxLocalBound

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicLowerSixJointEndpointPayment
open YMGap.Continuum.HarmonicLowerSixSecondFluxSign
open YMGap.Continuum.HarmonicLowerSixTailCorridor
open YMGap.Continuum.HarmonicLowerSixTailLocalWeightReduction
open YMGap.Continuum.HarmonicLowerSixTailPaymentAssembly
open YMGap.Continuum.HarmonicLowerSixTailSlopeReduction
open YMGap.Continuum.HarmonicLowerSixTailTaylorNineCertificate
open YMGap.Continuum.HarmonicLowerSixTailSlopeFloorCertificate
open YMGap.Continuum.HarmonicLowerSixTailSlopeFloorCertificateData
open YMGap.Continuum.HarmonicThetaPascalEvaluation
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxNonnegative
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixCubicEnvelope
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylor
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylorFive
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylorSeven
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticCarrier
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.FusionQuotientCollapse

local infix:50 " ≈ " => Q'.eqv

private theorem tail_local_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "tail_local_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               tail_local_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast, Int.natCast_add, Int.natCast_one,
               Int.natCast_zero,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             try ac_rfl))

/-- Beyond the square-root boundary the exact adjacent-root slope is
nonnegative.  Reciprocal Bernoulli supplies the needed upper bound on the
harmonic power; the corridor inequality clears its denominator. -/
theorem thetaRootSlope_nonnegative_of_den_le_mode_odd
    {k n : Nat} (hden : k + 2 ≤ n * (2 * n + 1)) :
    (0 : Q') ≤ thetaRootSlope k n := by
  let u := harmU k
  let a := qpow (harmW k) (2 * n + 1)
  let D := Q'.ofNat (k + 2)
  let N := Q'.ofNat n
  let A := Q'.ofNat (n + 1)
  let M := Q'.ofNat (2 * n + 1)
  let B := bernDen u (2 * n + 1)
  have hu0 : (0 : Q') ≤ u := by
    dsimp only [u]
    exact harmU_nonneg k
  have hu1 : u ≤ (1 : Q') := by
    dsimp only [u]
    exact harmU_le_one k
  have ha0 : (0 : Q') ≤ a := by
    dsimp only [a]
    exact RGTransport.qpow_nonneg _ (harmW_nonneg k) _
  have hab : a * B ≤ (1 : Q') := by
    dsimp only [a, B, u]
    unfold harmW
    exact oneSub_pow_mul_bernDen_le hu0 hu1 (2 * n + 1)
  have hcast : D ≤ Q'.ofNat (n * (2 * n + 1)) := by
    dsimp only [D]
    exact CReal.ofNat_le_ofNat hden
  have hmul := Q'.mul_le_mul_of_nonneg_right _ _ u hcast hu0
  have hleft : D * u ≈ (1 : Q') := by
    dsimp only [D, u]
    exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (tail_harmU_mul_den k)
  have hright : Q'.ofNat (n * (2 * n + 1)) * u ≈
      (N * M) * u := by
    dsimp only [N, M]
    exact Q'.mul_eqv_congr_right _ _ u
      (HeatKernelRGStep.ofNat_mul_eqv n (2 * n + 1))
  have hone : (1 : Q') ≤ (N * M) * u :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hright))
  have hA : A ≈ N + (1 : Q') := by
    dsimp only [A, N]
    exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv n 1)
      (Q'.add_eqv_congr_left _ _ _ (by decide))
  have hNB : N * B ≈ N + (N * M) * u := by
    dsimp only [B, M, u]
    unfold bernDen
    tail_local_ring
  have hadd := Q'.add_le_add_left N (1 : Q') ((N * M) * u) hone
  have hAB : A ≤ N * B :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hA)
      (Q'.le_trans' _ _ _ hadd (Q'.ge_of_eqv hNB))
  have hmulA := Q'.mul_le_mul_of_nonneg_right _ _ a hAB ha0
  have hNBassoc : (N * B) * a ≈ N * (a * B) := by
    tail_local_ring
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _ N hab
    (HeatKernelRGStep.zero_le_ofNat _)
  have hNone : N * (1 : Q') ≈ N := Q'.mul_one_eqv N
  have hAaN : A * a ≤ N :=
    Q'.le_trans' _ _ _ hmulA
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hNBassoc)
        (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv hNone)))
  unfold thetaRootSlope
  dsimp only [A, N, a] at hAaN ⊢
  exact Q'.sub_nonneg_of_le hAaN

theorem thetaRootSlope_nonnegative_of_den_le_two_sq
    {k n : Nat} (hden : k + 2 ≤ 2 * (n * n)) :
    (0 : Q') ≤ thetaRootSlope k n :=
  thetaRootSlope_nonnegative_of_den_le_mode_odd
    (Nat.le_trans hden (by
      rw [Nat.mul_add, Nat.mul_one]
      have h : n * (2 * n) = 2 * (n * n) := by ac_rfl
      rw [h]
      omega))

def lowerSixTailOldSlopeCeiling (k n : Nat) : Q' :=
  Q'.ofNat n +
    -(Q'.ofNat (n + 1) * lowerSixTailOldPowerLower k n)

/-- Lower carrier obtained by lowering the positive next-slope square and
raising the old-slope square which occurs with a minus sign. -/
def lowerSixTailCarrierLower (k n : Nat) : Q' :=
  let D := Q'.ofNat (k + 2)
  let N2 := Q'.ofNat (n * n)
  let L1 := lowerSixTailNextSlopeFloor k n
  let U0 := lowerSixTailOldSlopeCeiling k n
  Q'.ofNat (k + 3) * lowerSixQuadraticTaylorFactor k n *
      (Q'.ofNat 4 * (L1 * L1) +
        -(lowerSixDirichletProfile (k + 1) * N2)) +
    -(D *
      (Q'.ofNat 4 * (U0 * U0) +
        -(lowerSixDirichletProfile k * N2)))

/-- Coefficient of the exact old Gaussian step after the second-flux and
Hermite-remainder terms are combined. -/
def lowerSixTailStepCoefficient (k n : Nat) : Q' :=
  let D := Q'.ofNat (k + 2)
  let D2 := RingNormaliser.qpow D 2
  lowerSixHermiteSecondFluxPoly D (Q'.ofNat (n + 1)) +
    -(Q'.ofNat 60 * D2 *
      lowerSixDiscreteHermiteFluxPoly D (Q'.ofNat (n + 1)))

/-- Step-free part of the one-sided local envelope. -/
def lowerSixTailEnvelopeBase (k n : Nat) : Q' :=
  let D := Q'.ofNat (k + 2)
  let D2 := RingNormaliser.qpow D 2
  let D3 := RingNormaliser.qpow D 3
  let D4 := RingNormaliser.qpow D 4
  (-lowerSixHermiteSecondFluxPoly D (Q'.ofNat n)) +
    Q'.ofNat 15630 * D4 +
    Q'.ofNat 60 * D2 *
      (Q'.ofNat 48 * D4 * lowerSixTailCarrierLower k n +
        lowerSixDiscreteHermiteFluxPoly D (Q'.ofNat n) +
        -(Q'.ofNat 6 * D3))

def lowerSixTailEnvelope8 (k n : Nat) : Q' :=
  let U := lowerSixTailOldPowerUpper k n
  U * U * lowerSixTailStepCoefficient k n +
    lowerSixTailEnvelopeBase k n

def lowerSixTailEnvelope9 (k n : Nat) : Q' :=
  let L := lowerSixTailOldPowerLower k n
  L * L * lowerSixTailStepCoefficient k n +
    lowerSixTailEnvelopeBase k n

/-- The exact step-free part before the two slope squares are enclosed. -/
def lowerSixTailActualBase (k n : Nat) : Q' :=
  let D := Q'.ofNat (k + 2)
  let D2 := RingNormaliser.qpow D 2
  let D3 := RingNormaliser.qpow D 3
  let D4 := RingNormaliser.qpow D 4
  (-lowerSixHermiteSecondFluxPoly D (Q'.ofNat n)) +
    Q'.ofNat 15630 * D4 +
    Q'.ofNat 60 * D2 *
      (Q'.ofNat 48 * D4 * lowerSixQuadraticTaylorCarrier k n +
        lowerSixDiscreteHermiteFluxPoly D (Q'.ofNat n) +
        -(Q'.ofNat 6 * D3))

/-- Exact weight-free slack of the production local inequality. -/
def lowerSixTailActualSlack (k n : Nat) : Q' :=
  let D := Q'.ofNat (k + 2)
  let D2 := RingNormaliser.qpow D 2
  let D4 := RingNormaliser.qpow D 4
  let step := qpow (harmW k * harmW k) (2 * n + 1)
  (step * lowerSixHermiteSecondFluxPoly D (Q'.ofNat (n + 1)) +
      -lowerSixHermiteSecondFluxPoly D (Q'.ofNat n)) +
    Q'.ofNat 15630 * D4 +
    Q'.ofNat 60 * D2 * lowerSixHermiteRemainderNetBracket k n

private theorem lowerSixTailQuadraticTaylorFactor_nonnegative (k n : Nat) :
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

private theorem tail_sq_le_sq {a b : Q'}
    (ha : (0 : Q') ≤ a) (hab : a ≤ b) :
    a * a ≤ b * b := by
  have hb : (0 : Q') ≤ b := Q'.le_trans' _ _ _ ha hab
  have h1 := Q'.mul_le_mul_of_nonneg_right a b a hab ha
  have h2 := Q'.mul_le_mul_of_nonneg_left a b b hab hb
  exact Q'.le_trans' _ _ _ h1 h2

theorem lowerSixTailOldPower_le_upper (k n : Nat) :
    qpow (harmW k) (2 * n + 1) ≤
      lowerSixTailOldPowerUpper k n := by
  unfold lowerSixTailOldPowerUpper harmW oneSub
  exact qpow_oneSub_le_taylor8 (harmU_nonneg k) (harmU_le_one k) _

theorem lowerSixTailOldPowerLower_le (k n : Nat) :
    lowerSixTailOldPowerLower k n ≤
      qpow (harmW k) (2 * n + 1) := by
  unfold lowerSixTailOldPowerLower harmW oneSub
  exact taylor9_le_qpow_oneSub (harmU_nonneg k) (harmU_le_one k) _

theorem lowerSixTailNextPower_le_upper (k n : Nat) :
    qpow (harmW (k + 1)) (2 * n + 1) ≤
      lowerSixTailNextPowerUpper k n := by
  unfold lowerSixTailNextPowerUpper harmW oneSub
  exact qpow_oneSub_le_taylor8
    (harmU_nonneg (k + 1)) (harmU_le_one (k + 1)) _

theorem lowerSixTailNextSlopeFloor_le (k n : Nat) :
    lowerSixTailNextSlopeFloor k n ≤ thetaRootSlope (k + 1) n := by
  let A := Q'.ofNat (n + 1)
  let q := qpow (harmW (k + 1)) (2 * n + 1)
  let U := lowerSixTailNextPowerUpper k n
  have hqU : q ≤ U := by
    dsimp only [q, U]
    exact lowerSixTailNextPower_le_upper k n
  have hA0 : (0 : Q') ≤ A := by
    dsimp only [A]
    exact HeatKernelRGStep.zero_le_ofNat _
  have hmul := Q'.mul_le_mul_of_nonneg_left q U A hqU hA0
  have hneg := Q'.neg_le_neg hmul
  have hadd := Q'.add_le_add_left (Q'.ofNat n) (-(A * U)) (-(A * q)) hneg
  unfold lowerSixTailNextSlopeFloor thetaRootSlope
  dsimp only [A, q, U] at hadd ⊢
  exact hadd

theorem lowerSixTailOldSlope_le_ceiling (k n : Nat) :
    thetaRootSlope k n ≤ lowerSixTailOldSlopeCeiling k n := by
  let A := Q'.ofNat (n + 1)
  let q := qpow (harmW k) (2 * n + 1)
  let L := lowerSixTailOldPowerLower k n
  have hLq : L ≤ q := by
    dsimp only [L, q]
    exact lowerSixTailOldPowerLower_le k n
  have hA0 : (0 : Q') ≤ A := by
    dsimp only [A]
    exact HeatKernelRGStep.zero_le_ofNat _
  have hmul := Q'.mul_le_mul_of_nonneg_left L q A hLq hA0
  have hneg := Q'.neg_le_neg hmul
  have hadd := Q'.add_le_add_left (Q'.ofNat n) (-(A * q)) (-(A * L)) hneg
  unfold lowerSixTailOldSlopeCeiling thetaRootSlope
  dsimp only [A, q, L] at hadd ⊢
  exact hadd

/-- The one-sided slope squares genuinely lower the exact quadratic Taylor
carrier on the tail corridor. -/
theorem lowerSixTailCarrierLower_le_actual
    {k n : Nat} (hden : k + 2 ≤ 2 * (n * n))
    (hfloor : (0 : Q') ≤ lowerSixTailNextSlopeFloor k n) :
    lowerSixTailCarrierLower k n ≤
      lowerSixQuadraticTaylorCarrier k n := by
  let D := Q'.ofNat (k + 2)
  let N2 := Q'.ofNat (n * n)
  let S0 := thetaRootSlope k n
  let S1 := thetaRootSlope (k + 1) n
  let L1 := lowerSixTailNextSlopeFloor k n
  let U0 := lowerSixTailOldSlopeCeiling k n
  let F := lowerSixQuadraticTaylorFactor k n
  let P0 := lowerSixDirichletProfile k * N2
  let P1 := lowerSixDirichletProfile (k + 1) * N2
  have hn1 : 1 ≤ n := by
    cases n with
    | zero => simp at hden
    | succ n => omega
  have hS0 : (0 : Q') ≤ S0 := by
    dsimp only [S0]
    exact thetaRootSlope_nonnegative_of_den_le_two_sq hden
  have hnextDen : k + 3 ≤ n * (2 * n + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    have h : n * (2 * n) = 2 * (n * n) := by ac_rfl
    rw [h]
    omega
  have hS1 : (0 : Q') ≤ S1 := by
    dsimp only [S1]
    exact thetaRootSlope_nonnegative_of_den_le_mode_odd hnextDen
  have hL1S1 : L1 ≤ S1 := by
    dsimp only [L1, S1]
    exact lowerSixTailNextSlopeFloor_le k n
  have hS0U0 : S0 ≤ U0 := by
    dsimp only [S0, U0]
    exact lowerSixTailOldSlope_le_ceiling k n
  have hnextSq : L1 * L1 ≤ S1 * S1 :=
    tail_sq_le_sq (by simpa only [L1] using hfloor) hL1S1
  have holdSq : S0 * S0 ≤ U0 * U0 :=
    tail_sq_le_sq hS0 hS0U0
  have hF0 : (0 : Q') ≤ F := by
    dsimp only [F]
    exact lowerSixTailQuadraticTaylorFactor_nonnegative k n
  have hcoef0 : (0 : Q') ≤ Q'.ofNat (k + 3) * F :=
    Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _) hF0
  have hfourNext : Q'.ofNat 4 * (L1 * L1) ≤
      Q'.ofNat 4 * (S1 * S1) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hnextSq (by decide)
  have hnextInner : Q'.ofNat 4 * (L1 * L1) + -P1 ≤
      Q'.ofNat 4 * (S1 * S1) + -P1 :=
    Q'.add_le_add_right _ _ (-P1) hfourNext
  have hnextTerm :
      (Q'.ofNat (k + 3) * F) *
          (Q'.ofNat 4 * (L1 * L1) + -P1) ≤
        (Q'.ofNat (k + 3) * F) *
          (Q'.ofNat 4 * (S1 * S1) + -P1) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hnextInner hcoef0
  have hfourOld : Q'.ofNat 4 * (S0 * S0) ≤
      Q'.ofNat 4 * (U0 * U0) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ holdSq (by decide)
  have holdInner : Q'.ofNat 4 * (S0 * S0) + -P0 ≤
      Q'.ofNat 4 * (U0 * U0) + -P0 :=
    Q'.add_le_add_right _ _ (-P0) hfourOld
  have hD0 : (0 : Q') ≤ D := by
    dsimp only [D]
    exact HeatKernelRGStep.zero_le_ofNat _
  have holdMul : D * (Q'.ofNat 4 * (S0 * S0) + -P0) ≤
      D * (Q'.ofNat 4 * (U0 * U0) + -P0) :=
    Q'.mul_le_mul_of_nonneg_left _ _ D holdInner hD0
  have holdTerm : -(D * (Q'.ofNat 4 * (U0 * U0) + -P0)) ≤
      -(D * (Q'.ofNat 4 * (S0 * S0) + -P0)) :=
    Q'.neg_le_neg holdMul
  unfold lowerSixTailCarrierLower lowerSixQuadraticTaylorCarrier
  dsimp only [D, N2, S0, S1, L1, U0, F, P0, P1] at hnextTerm holdTerm ⊢
  exact Q'.add_le_add hnextTerm holdTerm

private theorem tail_ringQpow_nonnegative {a : Q'}
    (ha : (0 : Q') ≤ a) :
    ∀ m, (0 : Q') ≤ RingNormaliser.qpow a m
  | 0 => by
      show (0 : Q') ≤ (1 : Q')
      decide
  | m + 1 =>
      Q'.mul_nonneg _ _ (tail_ringQpow_nonnegative ha m) ha

theorem lowerSixTailEnvelopeBase_le_actualBase
    {k n : Nat} (hden : k + 2 ≤ 2 * (n * n))
    (hfloor : (0 : Q') ≤ lowerSixTailNextSlopeFloor k n) :
    lowerSixTailEnvelopeBase k n ≤ lowerSixTailActualBase k n := by
  let D := Q'.ofNat (k + 2)
  let D2 := RingNormaliser.qpow D 2
  let D3 := RingNormaliser.qpow D 3
  let D4 := RingNormaliser.qpow D 4
  let Clower := lowerSixTailCarrierLower k n
  let Cactual := lowerSixQuadraticTaylorCarrier k n
  let J := lowerSixDiscreteHermiteFluxPoly D (Q'.ofNat n)
  let P := lowerSixHermiteSecondFluxPoly D (Q'.ofNat n)
  have hC : Clower ≤ Cactual := by
    dsimp only [Clower, Cactual]
    exact lowerSixTailCarrierLower_le_actual hden hfloor
  have hD0 : (0 : Q') ≤ D := by
    dsimp only [D]
    exact HeatKernelRGStep.zero_le_ofNat _
  have hD2 : (0 : Q') ≤ D2 := by
    dsimp only [D2]
    exact tail_ringQpow_nonnegative hD0 _
  have hD4 : (0 : Q') ≤ D4 := by
    dsimp only [D4]
    exact tail_ringQpow_nonnegative hD0 _
  have h48D4 : (0 : Q') ≤ Q'.ofNat 48 * D4 :=
    Q'.mul_nonneg _ _ (by decide) hD4
  have hcarrier : Q'.ofNat 48 * D4 * Clower ≤
      Q'.ofNat 48 * D4 * Cactual :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hC h48D4
  have hinner :
      Q'.ofNat 48 * D4 * Clower + J + -(Q'.ofNat 6 * D3) ≤
        Q'.ofNat 48 * D4 * Cactual + J + -(Q'.ofNat 6 * D3) :=
    Q'.add_le_add_right _ _ _ (Q'.add_le_add_right _ _ J hcarrier)
  have h60D2 : (0 : Q') ≤ Q'.ofNat 60 * D2 :=
    Q'.mul_nonneg _ _ (by decide) hD2
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hinner h60D2
  have hcommon := Q'.add_le_add_left
    (-P + Q'.ofNat 15630 * D4) _ _ hscaled
  unfold lowerSixTailEnvelopeBase lowerSixTailActualBase
  dsimp only [D, D2, D3, D4, Clower, Cactual, J, P] at hcommon ⊢
  exact hcommon

private theorem mul_le_mul_of_nonpos_right
    {a b c : Q'} (hab : a ≤ b) (hc : c ≤ (0 : Q')) :
    b * c ≤ a * c := by
  have hnc : (0 : Q') ≤ -c := Q'.nonneg_neg_of_nonpos hc
  have hmul := Q'.mul_le_mul_of_nonneg_right a b (-c) hab hnc
  have hneg := Q'.neg_le_neg hmul
  have hleft : -(b * -c) ≈ b * c := by tail_local_ring
  have hright : -(a * -c) ≈ a * c := by tail_local_ring
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hneg (Q'.le_of_eqv hright))

private theorem lowerSixTailActualSlack_algebra
    (step Pp Pn D4 D2 C Jp Jn D3 : Q') :
    (step * Pp + -Pn) + Q'.ofNat 15630 * D4 +
        Q'.ofNat 60 * D2 *
          ((Q'.ofNat 48 * D4 * C + -(step * Jp + -Jn)) +
            -(Q'.ofNat 6 * D3)) ≈
      step * (Pp + -(Q'.ofNat 60 * D2 * Jp)) +
        ((-Pn) + Q'.ofNat 15630 * D4 +
          Q'.ofNat 60 * D2 *
            (Q'.ofNat 48 * D4 * C + Jn + -(Q'.ofNat 6 * D3))) := by
  tail_local_ring

theorem lowerSixTailActualSlack_eqv_stepCoefficient_add_actualBase
    (k n : Nat) :
    let step := qpow (harmW k * harmW k) (2 * n + 1)
    lowerSixTailActualSlack k n ≈
      step * lowerSixTailStepCoefficient k n +
        lowerSixTailActualBase k n := by
  let D := Q'.ofNat (k + 2)
  let D2 := RingNormaliser.qpow D 2
  let D3 := RingNormaliser.qpow D 3
  let D4 := RingNormaliser.qpow D 4
  let step := qpow (harmW k * harmW k) (2 * n + 1)
  let Pp := lowerSixHermiteSecondFluxPoly D (Q'.ofNat (n + 1))
  let Pn := lowerSixHermiteSecondFluxPoly D (Q'.ofNat n)
  let Jp := lowerSixDiscreteHermiteFluxPoly D (Q'.ofNat (n + 1))
  let Jn := lowerSixDiscreteHermiteFluxPoly D (Q'.ofNat n)
  let C := lowerSixQuadraticTaylorCarrier k n
  unfold lowerSixTailActualSlack lowerSixTailStepCoefficient
    lowerSixTailActualBase lowerSixHermiteRemainderNetBracket
    lowerSixHermiteNetBracket
  dsimp only [D, D2, D3, D4, step, Pp, Pn, Jp, Jn, C]
  exact lowerSixTailActualSlack_algebra step Pp Pn D4 D2 C Jp Jn D3

theorem lowerSixTailActualSlack_ge_envelope8
    {k n : Nat} (hden : k + 2 ≤ 2 * (n * n))
    (hfloor : (0 : Q') ≤ lowerSixTailNextSlopeFloor k n)
    (hK : lowerSixTailStepCoefficient k n ≤ (0 : Q')) :
    lowerSixTailEnvelope8 k n ≤ lowerSixTailActualSlack k n := by
  let a := qpow (harmW k) (2 * n + 1)
  let step := qpow (harmW k * harmW k) (2 * n + 1)
  let U := lowerSixTailOldPowerUpper k n
  let K := lowerSixTailStepCoefficient k n
  let B := lowerSixTailEnvelopeBase k n
  let BA := lowerSixTailActualBase k n
  have ha0 : (0 : Q') ≤ a := by
    dsimp only [a]
    exact RGTransport.qpow_nonneg _ (harmW_nonneg k) _
  have haU : a ≤ U := by
    dsimp only [a, U]
    exact lowerSixTailOldPower_le_upper k n
  have hsquare : a * a ≤ U * U := tail_sq_le_sq ha0 haU
  have hstepEq : step ≈ a * a := by
    dsimp only [step, a]
    exact FusionQuotientCollapse.qpow_mul_self (harmW k) (2 * n + 1)
  have hstepU : step ≤ U * U :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hstepEq) hsquare
  have hstepTerm : (U * U) * K ≤ step * K :=
    mul_le_mul_of_nonpos_right hstepU (by simpa only [K] using hK)
  have hbase : B ≤ BA := by
    dsimp only [B, BA]
    exact lowerSixTailEnvelopeBase_le_actualBase hden hfloor
  have hadd := Q'.add_le_add hstepTerm hbase
  have hactual := lowerSixTailActualSlack_eqv_stepCoefficient_add_actualBase k n
  unfold lowerSixTailEnvelope8
  dsimp only [U, K, B, BA, step] at hadd hactual ⊢
  exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv (Q'.eqv_symm hactual))

theorem lowerSixTailActualSlack_ge_envelope9
    {k n : Nat} (hden : k + 2 ≤ 2 * (n * n))
    (hfloor : (0 : Q') ≤ lowerSixTailNextSlopeFloor k n)
    (hL : (0 : Q') ≤ lowerSixTailOldPowerLower k n)
    (hK : (0 : Q') ≤ lowerSixTailStepCoefficient k n) :
    lowerSixTailEnvelope9 k n ≤ lowerSixTailActualSlack k n := by
  let a := qpow (harmW k) (2 * n + 1)
  let step := qpow (harmW k * harmW k) (2 * n + 1)
  let L := lowerSixTailOldPowerLower k n
  let K := lowerSixTailStepCoefficient k n
  let B := lowerSixTailEnvelopeBase k n
  let BA := lowerSixTailActualBase k n
  have hLa : L ≤ a := by
    dsimp only [L, a]
    exact lowerSixTailOldPowerLower_le k n
  have hsquare : L * L ≤ a * a :=
    tail_sq_le_sq (by simpa only [L] using hL) hLa
  have hstepEq : step ≈ a * a := by
    dsimp only [step, a]
    exact FusionQuotientCollapse.qpow_mul_self (harmW k) (2 * n + 1)
  have hLstep : L * L ≤ step :=
    Q'.le_trans' _ _ _ hsquare (Q'.ge_of_eqv hstepEq)
  have hstepTerm : (L * L) * K ≤ step * K :=
    Q'.mul_le_mul_of_nonneg_right _ _ K hLstep
      (by simpa only [K] using hK)
  have hbase : B ≤ BA := by
    dsimp only [B, BA]
    exact lowerSixTailEnvelopeBase_le_actualBase hden hfloor
  have hadd := Q'.add_le_add hstepTerm hbase
  have hactual := lowerSixTailActualSlack_eqv_stepCoefficient_add_actualBase k n
  unfold lowerSixTailEnvelope9
  dsimp only [L, K, B, BA, step] at hadd hactual ⊢
  exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv (Q'.eqv_symm hactual))

theorem lowerSixTailActualSlack_nonnegative_of_base
    {k n : Nat} (hden : k + 2 ≤ 2 * (n * n))
    (hfloor : (0 : Q') ≤ lowerSixTailNextSlopeFloor k n)
    (hK : (0 : Q') ≤ lowerSixTailStepCoefficient k n)
    (hbase : (0 : Q') ≤ lowerSixTailEnvelopeBase k n) :
    (0 : Q') ≤ lowerSixTailActualSlack k n := by
  let step := qpow (harmW k * harmW k) (2 * n + 1)
  let K := lowerSixTailStepCoefficient k n
  let BA := lowerSixTailActualBase k n
  have hstep0 : (0 : Q') ≤ step := by
    dsimp only [step]
    exact RGTransport.qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _
  have hterm : (0 : Q') ≤ step * K :=
    Q'.mul_nonneg _ _ hstep0 (by simpa only [K] using hK)
  have hBA : (0 : Q') ≤ BA :=
    Q'.le_trans' _ _ _ hbase
      (lowerSixTailEnvelopeBase_le_actualBase hden hfloor)
  have hsum := Q'.zero_le_add _ _ hterm hBA
  have hactual := lowerSixTailActualSlack_eqv_stepCoefficient_add_actualBase k n
  dsimp only [step, K, BA] at hsum hactual ⊢
  exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (Q'.eqv_symm hactual))

private theorem lowerSixTailClearingScale_algebra (R D2 B : Q') :
    R + Q'.ofNat 60 * D2 * B ≈
      R + -((Q'.ofNat 15 * D2) * -(Q'.ofNat 4 * B)) := by
  tail_local_ring

theorem lowerSixTailWeightFreeBound_of_actualSlack_nonnegative
    {k n : Nat} (hslack : (0 : Q') ≤ lowerSixTailActualSlack k n) :
    LowerSixTailSecondFluxWeightFreeBound k n := by
  let D := Q'.ofNat (k + 2)
  let D2 := RingNormaliser.qpow D 2
  let D4 := RingNormaliser.qpow D 4
  let step := qpow (harmW k * harmW k) (2 * n + 1)
  let B := lowerSixHermiteRemainderNetBracket k n
  let L := lowerSixJointSecondClearingScale k * -(Q'.ofNat 4 * B)
  let R :=
    (step * lowerSixHermiteSecondFluxPoly D (Q'.ofNat (n + 1)) +
      -lowerSixHermiteSecondFluxPoly D (Q'.ofNat n)) +
      Q'.ofNat 15630 * D4
  have heq : lowerSixTailActualSlack k n ≈ R + -L := by
    unfold lowerSixTailActualSlack
    dsimp only [D, D2, D4, step, B, L, R]
    unfold lowerSixJointSecondClearingScale
    exact lowerSixTailClearingScale_algebra R D2 B
  have hsub : (0 : Q') ≤ R + -L :=
    Q'.le_trans' _ _ _ hslack (Q'.le_of_eqv heq)
  have hLR : L ≤ R := Q'.le_of_sub_nonneg hsub
  unfold LowerSixTailSecondFluxWeightFreeBound
  dsimp only [D, D2, D4, step, B, L, R] at hLR ⊢
  exact hLR

/-- Sign-safe analytic dispatch.  The four hypotheses are precisely the
closed rational Bernstein outputs: the two full envelopes, positivity of the
ninth-order lower step on `n ≤ D`, and positivity of the step-free base on
`D ≤ n`. -/
theorem lowerSixTailSecondFluxLocalBound_of_envelope_certificates
    {k n : Nat}
    (hleft : thetaWindowLeft k + 1 ≤ n)
    (hfloor : (0 : Q') ≤ lowerSixTailNextSlopeFloor k n)
    (hE8 : (0 : Q') ≤ lowerSixTailEnvelope8 k n)
    (hE9 : (0 : Q') ≤ lowerSixTailEnvelope9 k n)
    (hT9 : n ≤ k + 2 →
      (0 : Q') ≤ lowerSixTailOldPowerLower k n)
    (hbase : k + 2 ≤ n →
      (0 : Q') ≤ lowerSixTailEnvelopeBase k n) :
    LowerSixTailSecondFluxLocalBound k n := by
  have hden : k + 2 ≤ 2 * (n * n) :=
    lowerSixTail_den_le_two_sq_of_left_succ_le hleft
  have hslack : (0 : Q') ≤ lowerSixTailActualSlack k n := by
    by_cases hKneg : lowerSixTailStepCoefficient k n ≤ (0 : Q')
    · exact Q'.le_trans' _ _ _ hE8
        (lowerSixTailActualSlack_ge_envelope8 hden hfloor hKneg)
    · have hKpos : (0 : Q') ≤ lowerSixTailStepCoefficient k n :=
        Q'.le_of_not_le hKneg
      by_cases hnD : n ≤ k + 2
      · exact Q'.le_trans' _ _ _ hE9
          (lowerSixTailActualSlack_ge_envelope9
            hden hfloor (hT9 hnD) hKpos)
      · have hDn : k + 2 ≤ n := by omega
        exact lowerSixTailActualSlack_nonnegative_of_base
          hden hfloor hKpos (hbase hDn)
  have hweightFree :=
    lowerSixTailWeightFreeBound_of_actualSlack_nonnegative hslack
  exact (lowerSixTailSecondFluxLocalBound_iff_weightFree k n).2 hweightFree

#print axioms qpow_oneSub_le_taylor8
#print axioms taylor9_le_qpow_oneSub
#print axioms thetaRootSlope_nonnegative_of_den_le_mode_odd
#print axioms thetaRootSlope_nonnegative_of_den_le_two_sq
#print axioms tailTaylor8Prefix_physical_bridge
#print axioms tailTaylor9Cleared_physical_bridge
#print axioms lowerSixTailOldPowerLower_nonnegative_of_le_den
#print axioms lowerSixTailNextSlopeFloor_nonnegative
#print axioms lowerSixTailSecondFluxLocalBound_of_envelope_certificates

end YMGap.Continuum.HarmonicLowerSixTailSecondFluxLocalBound
