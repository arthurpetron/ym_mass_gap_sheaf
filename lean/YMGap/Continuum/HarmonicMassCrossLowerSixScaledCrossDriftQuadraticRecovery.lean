/-
Localization of the exact quadratic drift payment to the recovery window.

Only the square-root recovery block is needed to pay the adverse cross-scale
prefix.  This file separates that block from the far suffix without losing
the positive quadratic binomial term, and records the exact one-step slope
floor supplied by the consecutive-scale drift estimate.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticRecovery

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftScaleStep
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftSuffix
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledWindowInduction
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixFirstCell
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixReserveDeficit
open YMGap.Continuum.HarmonicMassCrossLowerSixTwoSidedWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubic
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem recovery_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "recovery_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               recovery_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- The exact slope floor obtained by paying the entire consecutive-scale
loss with the same drift excess used by the linear weight floor. -/
def lowerSixNextSlopeFloor (k n : Nat) : Q' :=
  thetaRootSlope k n +
    -(Q'.ofNat (n * n) * lowerSixDriftExcess k)

theorem lowerSixNextSlopeFloor_le
    {k n : Nat} (hsq : 3 * (k + 2) ≤ n * n) :
    lowerSixNextSlopeFloor k n ≤ thetaRootSlope (k + 1) n := by
  have hdrift := lowerSixSlopeDrift_le_excess_of_shape hsq
  have hneg := Q'.neg_le_neg hdrift
  have hadd := Q'.add_le_add_left (thetaRootSlope k n) _ _ hneg
  unfold lowerSixNextSlopeFloor
  exact Q'.le_trans' _ _ _ hadd
    (Q'.le_of_eqv (Q'.eqv_symm (thetaRootSlope_step_eqv k n)))

private theorem lowerSixSuffixAfterFirst_shape_nat_247_645 : ∀ i : Fin 399,
    3 * (i.val + 247 + 2) ≤
      (thetaWindowRight (i.val + 247) + 2) *
        (thetaWindowRight (i.val + 247) + 2) := by
  decide

/-- The tempting first-suffix square shape is false inside the induction
regime; scale 260 is the earliest exceptional scale. -/
theorem lowerSixSuffixEndpoint_shape_fails_k260 :
    ¬ (3 * (260 + 2) ≤
      (thetaWindowRight 260 + 1) * (thetaWindowRight 260 + 1)) := by
  decide

/-- The sharp uniform correction is to start one cell later.  The finite
moving-edge prelude is reduced exactly; the tail follows from the stronger
symbolic endpoint theorem. -/
theorem lowerSixSuffixAfterFirst_shape_nat_from_247
    {k : Nat} (hk : 247 ≤ k) :
    3 * (k + 2) ≤
      (thetaWindowRight k + 2) * (thetaWindowRight k + 2) := by
  by_cases hlarge : 646 ≤ k
  · have h := (lowerSixSuffixEndpoint_shape_nat_large hlarge).1
    exact Nat.le_trans h
      (Nat.mul_le_mul (by omega : thetaWindowRight k + 1 ≤
        thetaWindowRight k + 2) (by omega))
  · let i : Fin 399 := ⟨k - 247, by omega⟩
    have h := lowerSixSuffixAfterFirst_shape_nat_247_645 i
    have hkidx : k - 247 + 247 = k := by omega
    simpa [i, hkidx] using h

theorem lowerSixRecoveryMode_shape
    {k j : Nat} (hk : 247 ≤ k) (hj : 1 ≤ j) :
    3 * (k + 2) ≤
      (thetaWindowRight k + 1 + j) *
        (thetaWindowRight k + 1 + j) := by
  have h0 := lowerSixSuffixAfterFirst_shape_nat_from_247 hk
  have hn : thetaWindowRight k + 2 ≤
      thetaWindowRight k + 1 + j := by omega
  exact Nat.le_trans h0 (Nat.mul_le_mul hn hn)

private theorem lowerSixDriftExcess_le_three_units (k : Nat) :
    lowerSixDriftExcess k ≤
      Q'.ofNat 3 * unit (driftDen k) (driftDen_pos k) := by
  let u := unit (driftDen k) (driftDen_pos k)
  have hu0 : (0 : Q') ≤ u := unit_nonneg _ _
  have hu1 : u ≤ (1 : Q') := by
    dsimp only [u]
    unfold unit
    show (Q'.mkPos 1 (driftDen k) (driftDen_pos k)).num *
        ((1 : Q').den : Int) ≤
      (1 : Q').num *
        ((Q'.mkPos 1 (driftDen k) (driftDen_pos k)).den : Int)
    simp only [Q'.mkPos_num, Q'.mkPos_den]
    have h1n : (1 : Q').num = 1 := rfl
    have h1d : ((1 : Q').den : Int) = 1 := rfl
    rw [h1n, h1d, Int.mul_one, Int.one_mul]
    have hdpos := driftDen_pos k
    exact_mod_cast (show 1 ≤ driftDen k by omega)
  have huu : u * u ≤ u := by
    have h := Q'.mul_le_mul_of_nonneg_left _ _ u hu1 hu0
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_one_eqv u))
  have hadd := Q'.add_le_add_left (u + u) _ _ huu
  have hthree : (u + u) + u ≈ Q'.ofNat 3 * u := by
    have h3 : Q'.ofNat 3 ≈ ((1 : Q') + 1) + 1 := by decide
    refine Q'.eqv_symm (Q'.eqv_trans _ ((((1 : Q') + 1) + 1) * u) _
      (Q'.mul_eqv_congr_right _ _ u h3) ?_)
    refine Q'.eqv_trans _ (((1 : Q') + 1) * u + (1 : Q') * u) _
      (Q'.add_mul_eqv ((1 : Q') + 1) 1 u) ?_
    refine Q'.eqv_trans _ (((1 : Q') * u + (1 : Q') * u) +
      (1 : Q') * u) _
      (Q'.add_eqv_congr_right _ _ _ (Q'.add_mul_eqv 1 1 u)) ?_
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.one_mul_eqv u) (Q'.one_mul_eqv u))
      (Q'.one_mul_eqv u)
  unfold lowerSixDriftExcess
  dsimp only [u] at hadd ⊢
  exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hthree)

private theorem recovery_mode_three_sq_le_driftDen
    {k j : Nat} (hk : 247 ≤ k) (hj : j < lowerSixRecoveryCount k) :
    3 * ((thetaWindowRight k + 1 + j) *
      (thetaWindowRight k + 1 + j)) ≤ driftDen k := by
  let D := k + 2
  let c := thetaWindowCenter k
  let n := thetaWindowRight k + 1 + j
  have hn : n ≤ 2 * c := by
    dsimp only [n, c]
    unfold lowerSixRecoveryCount at hj
    omega
  have hnSq := Nat.mul_le_mul hn hn
  have htwoSq : (2 * c) * (2 * c) = 4 * (c * c) := by ac_rfl
  rw [htwoSq] at hnSq
  have hcSq : c * c ≤ 2 * D + 1 := by
    dsimp only [c, D, thetaWindowCenter, thetaWindowLength]
    exact ChebOrthoMidpointEst.isqrt_sq_le _
  have hfour := Nat.mul_le_mul_left 4 hcSq
  have hnBound : n * n ≤ 4 * (2 * D + 1) :=
    Nat.le_trans hnSq hfour
  have hthree := Nat.mul_le_mul_left 3 hnBound
  have hD25 : 25 ≤ D := by
    dsimp only [D]
    omega
  have hmul : 25 * D ≤ D * D := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right D hD25
  have hpoly : 3 * (4 * (2 * D + 1)) ≤ D * D - 1 := by omega
  unfold driftDen
  dsimp only [D, n] at hthree hpoly ⊢
  exact Nat.le_trans hthree hpoly

theorem lowerSixRecoveryDriftBudget_le_one
    {k j : Nat} (hk : 247 ≤ k) (hj : j < lowerSixRecoveryCount k) :
    Q'.ofNat ((thetaWindowRight k + 1 + j) *
        (thetaWindowRight k + 1 + j)) * lowerSixDriftExcess k ≤
      (1 : Q') := by
  let n := thetaWindowRight k + 1 + j
  let u := unit (driftDen k) (driftDen_pos k)
  have hE := lowerSixDriftExcess_le_three_units k
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat (n * n))
    hE (HeatKernelRGStep.zero_le_ofNat _)
  have hnat := recovery_mode_three_sq_le_driftDen hk hj
  have hnat' : n * n * 3 ≤ driftDen k := by
    dsimp only [n] at hnat ⊢
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hnat
  have hunit : Q'.ofNat (n * n) * (Q'.ofNat 3 * u) ≤ (1 : Q') := by
    dsimp only [u]
    unfold unit
    show (Q'.ofNat (n * n) *
          (Q'.ofNat 3 * Q'.mkPos 1 (driftDen k) (driftDen_pos k))).num *
          ((1 : Q').den : Int) ≤
        (1 : Q').num *
          (Q'.ofNat (n * n) *
            (Q'.ofNat 3 * Q'.mkPos 1 (driftDen k) (driftDen_pos k))).den
    simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast,
      Q'.mkPos_num, Q'.mkPos_den, Q'.mul_num_cast, Q'.mul_den_cast,
      Int.mul_one, Int.one_mul]
    have h1n : (1 : Q').num = 1 := rfl
    have h1d : ((1 : Q').den : Int) = 1 := rfl
    rw [h1n, h1d, Int.mul_one, Int.one_mul]
    push_cast
    exact_mod_cast hnat'
  dsimp only [n, u] at hmul hunit ⊢
  exact Q'.le_trans' _ _ _ hmul hunit

theorem lowerSixScaledDriftQuadratic_nonnegative
    {k : Nat} (hk : 48 ≤ k) (j : Nat) :
    (0 : Q') ≤ lowerSixScaledDriftQuadratic k
      (thetaWindowRight k + 1 + j) := by
  unfold lowerSixScaledDriftQuadratic lowerSixWeightDriftQuadratic
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
      (Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
        (Q'.mul_nonneg _ _
          (lowerSixDriftExcess_nonnegative k)
          (lowerSixDriftExcess_nonnegative k))))
    (lowerSixNextModeCarrier_nonnegative hk j)

/-- Quadratic payment retained only through mode `2c`, the already-derived
one-scale recovery edge. -/
def lowerSixScaledQuadraticRecoverySuffix (k : Nat) : Q' :=
  finSum
    (fun j => lowerSixModeWeight k (thetaWindowRight k + 1 + j) *
      lowerSixScaledDriftQuadratic k
        (thetaWindowRight k + 1 + j))
    (lowerSixRecoveryCount k)

private theorem twice_center_le_anchor
    {k : Nat} (hk : 48 ≤ k) :
    2 * thetaWindowCenter k ≤ growingAnchor k := by
  have hc := thetaWindowCenter_le_harmonicDen (show 38 ≤ k by omega)
  unfold growingAnchor
  omega

private theorem recoveryCount_le_suffixCount
    {k : Nat} (hk : 48 ≤ k) :
    lowerSixRecoveryCount k ≤
      growingAnchor k - thetaWindowRight k := by
  have hR : thetaWindowRight k ≤ 2 * thetaWindowCenter k := by
    unfold thetaWindowRight
    have hdiv := Nat.div_le_self (thetaWindowCenter k) 4
    omega
  have hC := twice_center_le_anchor hk
  unfold lowerSixRecoveryCount
  omega

private theorem finSum_nonnegative_of_terms (f : Nat → Q') : ∀ N,
    (∀ j, j < N → (0 : Q') ≤ f j) → (0 : Q') ≤ finSum f N
  | 0, _ => Q'.le_refl' 0
  | N + 1, h => by
      rw [finSum_succ]
      exact Q'.zero_le_add _ _
        (finSum_nonnegative_of_terms f N
          (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self N))))
        (h N (Nat.lt_succ_self N))

/-- The recovery-window quadratic payment is no larger than the complete
quadratic suffix; the discarded far block is termwise nonnegative. -/
theorem lowerSixScaledQuadraticRecoverySuffix_le_full
    {k : Nat} (hk : 48 ≤ k) :
    lowerSixScaledQuadraticRecoverySuffix k ≤
      lowerSixScaledQuadraticCrossWindowSuffix k := by
  let R := lowerSixRecoveryCount k
  let N := growingAnchor k - thetaWindowRight k
  let f := fun j => lowerSixModeWeight k (thetaWindowRight k + 1 + j) *
    lowerSixScaledDriftQuadratic k (thetaWindowRight k + 1 + j)
  have hRN : R ≤ N := by
    dsimp only [R, N]
    exact recoveryCount_le_suffixCount hk
  have hcount : N = R + (N - R) := by omega
  have hsplit := finSum_split f R (N - R)
  rw [← hcount] at hsplit
  have hfar : (0 : Q') ≤ finSum (fun j => f (R + j)) (N - R) := by
    apply finSum_nonnegative_of_terms
    intro j hj
    exact Q'.mul_nonneg _ _ (lowerSixModeWeight_nonnegative k _)
      (by
        have hindex : thetaWindowRight k + 1 + (R + j) =
            thetaWindowRight k + 1 + (R + j) := rfl
        rw [hindex]
        exact lowerSixScaledDriftQuadratic_nonnegative hk (R + j))
  have hadd := Q'.add_le_self_of_nonneg (finSum f R) _ hfar
  unfold lowerSixScaledQuadraticRecoverySuffix
    lowerSixScaledQuadraticCrossWindowSuffix
  dsimp only [R, N, f] at hsplit hadd ⊢
  exact Q'.le_trans' _ _ _ hadd
    (Q'.le_of_eqv (Q'.eqv_symm hsplit))

/-- A payment by the localized square-root recovery block already closes the
full physical step. -/
theorem lowerSixScaledWindowStep_of_quadratic_recovery_payment
    {k : Nat} (hk : 48 ≤ k)
    (hpay : -lowerSixScaledLinearCrossPaymentResidual k ≤
      lowerSixScaledQuadraticRecoverySuffix k) :
    LowerSixScaledWindowStep k := by
  exact lowerSixScaledWindowStep_of_quadratic_payment hk
    (Q'.le_trans' _ _ _ hpay
      (lowerSixScaledQuadraticRecoverySuffix_le_full hk))

#print axioms lowerSixNextSlopeFloor_le
#print axioms lowerSixSuffixEndpoint_shape_fails_k260
#print axioms lowerSixSuffixAfterFirst_shape_nat_from_247
#print axioms lowerSixRecoveryMode_shape
#print axioms lowerSixRecoveryDriftBudget_le_one
#print axioms lowerSixScaledDriftQuadratic_nonnegative
#print axioms lowerSixScaledQuadraticRecoverySuffix_le_full
#print axioms lowerSixScaledWindowStep_of_quadratic_recovery_payment

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticRecovery
