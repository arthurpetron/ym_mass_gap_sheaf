/-
Exact retention of the nonlinear lower-six drift remainder.

The Bernoulli floor is sufficient for pointwise sign localization on the
right suffix, but it is not quantitatively harmless: the full scaled step has
only a small surplus after paying its negative left prefix.  This file keeps
the exact factor-minus-floor term, proves it nonnegative on every retained
suffix mode, and splits the physical cross suffix into its linear and
nonlinear payments without weakening either one.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftSuffix

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftScaleStep

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftSuffix
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossWindow
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledWindowDifference
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledWindowInduction
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.HarmonicWeightedAbelReserve
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RefinedRetune
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem drift_step_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "drift_step_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               drift_step_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- Exact factor discarded by the first-order Bernoulli floor. -/
def lowerSixWeightDriftRemainder (k n : Nat) : Q' :=
  lowerSixWeightDriftFactor k n +
    -lowerSixWeightDriftFloor k n

/-- The nonlinear part of the exact scaled carrier after the linear floor is
removed. -/
def lowerSixScaledDriftRemainder (k n : Nat) : Q' :=
  Q'.ofNat (k + 3) * lowerSixWeightDriftRemainder k n *
    lowerSixModeCarrier (k + 1) n

theorem lowerSixWeightDriftRemainder_nonnegative (k n : Nat) :
    (0 : Q') ≤ lowerSixWeightDriftRemainder k n := by
  unfold lowerSixWeightDriftRemainder
  exact Q'.sub_nonneg_of_le (lowerSixWeightDriftFloor_le_factor k n)

/-- On every old right-suffix mode the exact nonlinear drift remainder is
nonnegative, because the new-scale carrier is now known unconditionally. -/
theorem lowerSixScaledDriftRemainder_nonnegative
    {k : Nat} (hk : 48 ≤ k) (j : Nat) :
    (0 : Q') ≤ lowerSixScaledDriftRemainder k
      (thetaWindowRight k + 1 + j) := by
  unfold lowerSixScaledDriftRemainder
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
      (lowerSixWeightDriftRemainder_nonnegative k _))
    (lowerSixNextModeCarrier_nonnegative hk j)

/-- Exact carrier decomposition.  No part of the exponential drift is
discarded. -/
theorem lowerSixScaledDriftCarrier_eqv_linear_add_remainder (k n : Nat) :
    lowerSixScaledDriftCarrier k n ≈
      lowerSixScaledLinearDriftCarrier k n +
        lowerSixScaledDriftRemainder k n := by
  let D1 := Q'.ofNat (k + 3)
  let D0 := Q'.ofNat (k + 2)
  let F := lowerSixWeightDriftFactor k n
  let L := lowerSixWeightDriftFloor k n
  let C1 := lowerSixModeCarrier (k + 1) n
  let C0 := lowerSixModeCarrier k n
  have hsplit : F ≈ L + (F + -L) := by
    apply Q'.eqv_symm
    refine Q'.eqv_trans _ ((L + F) + -L) _
      (Q'.eqv_symm (Q'.add_assoc_eqv L F (-L))) ?_
    refine Q'.eqv_trans _ ((F + L) + -L) _
      (Q'.add_eqv_congr_right _ _ (-L) (Q'.add_comm_eqv L F)) ?_
    refine Q'.eqv_trans _ (F + (L + -L)) _
      (Q'.add_assoc_eqv F L (-L)) ?_
    refine Q'.eqv_trans _ (F + 0) _
      (Q'.add_eqv_congr_left F _ _ (Q'.add_neg_self_eqv L)) ?_
    exact QPoly.q_add_zero_eqv F
  have hscaled : D1 * F * C1 ≈
      D1 * L * C1 + D1 * (F + -L) * C1 := by
    refine Q'.eqv_trans _ (D1 * (L + (F + -L)) * C1) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ C1
        (Q'.mul_eqv_congr_left D1 _ _ hsplit)
    · refine Q'.eqv_trans _ ((D1 * L + D1 * (F + -L)) * C1) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_add_eqv D1 L (F + -L))
      · exact Q'.add_mul_eqv (D1 * L) (D1 * (F + -L)) C1
  unfold lowerSixScaledDriftCarrier lowerSixScaledLinearDriftCarrier
    lowerSixScaledDriftRemainder lowerSixWeightDriftRemainder
  dsimp only [D1, D0, F, L, C1, C0] at hscaled ⊢
  refine Q'.eqv_trans _
    ((Q'.ofNat (k + 3) * lowerSixWeightDriftFloor k n *
          lowerSixModeCarrier (k + 1) n +
        Q'.ofNat (k + 3) *
          (lowerSixWeightDriftFactor k n +
            -lowerSixWeightDriftFloor k n) *
          lowerSixModeCarrier (k + 1) n) +
      -(Q'.ofNat (k + 2) * lowerSixModeCarrier k n)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _ hscaled
  · let X := Q'.ofNat (k + 3) * lowerSixWeightDriftFloor k n *
        lowerSixModeCarrier (k + 1) n
    let Y := Q'.ofNat (k + 3) *
        (lowerSixWeightDriftFactor k n +
          -lowerSixWeightDriftFloor k n) *
        lowerSixModeCarrier (k + 1) n
    let Z := -(Q'.ofNat (k + 2) * lowerSixModeCarrier k n)
    change (X + Y) + Z ≈ (X + Z) + Y
    refine Q'.eqv_trans _ (X + (Y + Z)) _ (Q'.add_assoc_eqv X Y Z) ?_
    refine Q'.eqv_trans _ (X + (Z + Y)) _
      (Q'.add_eqv_congr_left X _ _ (Q'.add_comm_eqv Y Z)) ?_
    exact Q'.eqv_symm (Q'.add_assoc_eqv X Z Y)

/-! ## Exact consecutive-slope transport -/

/-- Odd power occurring in the root-slope carrier. -/
def lowerSixOddPower (k n : Nat) : Q' :=
  qpow (harmW k) (2 * n + 1)

/-- Exact decrease of the root slope across one harmonic scale. -/
def lowerSixSlopeDrift (k n : Nat) : Q' :=
  Q'.ofNat (n + 1) * lowerSixOddPower k n *
    (qpow (driftRatio k) (2 * n + 1) + -(1 : Q'))

/-- Reciprocal-growth envelope for the exact slope drift. -/
def lowerSixSlopeDriftEnvelope (k n : Nat) : Q' :=
  Q'.ofNat (n + 1) * Q'.ofNat (2 * n + 1) *
    unit (driftDen k) (driftDen_pos k) * lowerSixOddPower (k + 1) n

theorem lowerSixOddPower_step_eqv (k n : Nat) :
    lowerSixOddPower (k + 1) n ≈
      lowerSixOddPower k n * qpow (driftRatio k) (2 * n + 1) := by
  unfold lowerSixOddPower
  exact Q'.eqv_trans _ _ _
    (qpow_eqv_congr_base (harmW_step_eqv k) (2 * n + 1))
    (qpow_mul_base (harmW k) (driftRatio k) (2 * n + 1))

private abbrev PE := RingNormaliser.PolyExpr

private def slopeStepL : PE :=
  let N := RingNormaliser.PolyExpr.var 0
  let A := RingNormaliser.PolyExpr.var 1
  let t := RingNormaliser.PolyExpr.var 2
  let q := RingNormaliser.PolyExpr.var 3
  .add N (.neg (.mul A (.mul t q)))

private def slopeStepR : PE :=
  let N := RingNormaliser.PolyExpr.var 0
  let A := RingNormaliser.PolyExpr.var 1
  let t := RingNormaliser.PolyExpr.var 2
  let q := RingNormaliser.PolyExpr.var 3
  .add (.add N (.neg (.mul A t)))
    (.neg (.mul (.mul A t) (.add q (.neg (.const 1)))))

private theorem slopeStep_normal :
    RingNormaliser.normalize slopeStepL =
      RingNormaliser.normalize slopeStepR := by decide

private theorem slope_step_algebra (N A t q : Q') :
    N + -(A * (t * q)) ≈
      (N + -(A * t)) + -(A * t * (q + -(1 : Q'))) := by
  simpa [slopeStepL, slopeStepR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      slopeStepL slopeStepR slopeStep_normal
      (fun | 0 => N | 1 => A | 2 => t | _ => q))

/-- The next root slope is exactly the old slope minus the positive harmonic
power drift. -/
theorem thetaRootSlope_step_eqv (k n : Nat) :
    thetaRootSlope (k + 1) n ≈
      thetaRootSlope k n + -lowerSixSlopeDrift k n := by
  have hp := lowerSixOddPower_step_eqv k n
  unfold thetaRootSlope lowerSixSlopeDrift lowerSixOddPower
  refine Q'.eqv_trans _
    (Q'.ofNat n +
      -(Q'.ofNat (n + 1) *
        (qpow (harmW k) (2 * n + 1) *
          qpow (driftRatio k) (2 * n + 1)))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left _ _ _ hp))
  · exact slope_step_algebra _ _ _ _

theorem lowerSixSlopeDrift_nonnegative (k n : Nat) :
    (0 : Q') ≤ lowerSixSlopeDrift k n := by
  let u := unit (driftDen k) (driftDen_pos k)
  let q := qpow (driftRatio k) (2 * n + 1)
  have hbern := qpow_one_add_bernoulli_lower
    (unit_nonneg (driftDen k) (driftDen_pos k)) (2 * n + 1)
  have hpow := qpow_eqv_congr_base
    (driftRatio_eqv_one_add_unitDen k) (2 * n + 1)
  have hq1 : (1 : Q') ≤ q := by
    have hnonneg : (0 : Q') ≤ Q'.ofNat (2 * n + 1) * u :=
      Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
        (unit_nonneg _ _)
    exact Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg (1 : Q') _ hnonneg)
      (Q'.le_trans' _ _ _ hbern
        (Q'.le_of_eqv (Q'.eqv_symm hpow)))
  have hqsub : (0 : Q') ≤ q + -(1 : Q') :=
    Q'.sub_nonneg_of_le hq1
  unfold lowerSixSlopeDrift
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
      (qpow_nonneg _ (harmW_nonneg k) _)) hqsub

/-- The exact slope drift is bounded by a next-power reciprocal-growth
envelope.  This keeps the old/new power cancellation intact. -/
theorem lowerSixSlopeDrift_le_envelope (k n : Nat) :
    lowerSixSlopeDrift k n ≤ lowerSixSlopeDriftEnvelope k n := by
  let t := lowerSixOddPower k n
  let q := qpow (driftRatio k) (2 * n + 1)
  let u := unit (driftDen k) (driftDen_pos k)
  let A := Q'.ofNat (n + 1)
  let P := Q'.ofNat (2 * n + 1)
  have hq : q + -(1 : Q') ≤ P * u * q := by
    dsimp only [q, P, u]
    exact qpow_one_add_increment_le (unit_nonneg _ _)
      (driftRatio_eqv_one_add_unitDen k) (2 * n + 1)
  have hAt0 : (0 : Q') ≤ A * t :=
    Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
      (qpow_nonneg _ (harmW_nonneg k) _)
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ (A * t) hq hAt0
  have hnext := lowerSixOddPower_step_eqv k n
  unfold lowerSixSlopeDrift lowerSixSlopeDriftEnvelope
  dsimp only [A, P, t, q, u] at hmul hnext ⊢
  exact Q'.le_trans' _ _ _ hmul
    (Q'.le_of_eqv (Q'.eqv_trans _
      (Q'.ofNat (n + 1) * Q'.ofNat (2 * n + 1) *
        unit (driftDen k) (driftDen_pos k) *
          (lowerSixOddPower k n *
            qpow (driftRatio k) (2 * n + 1))) _
      (by drift_step_ring)
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hnext))))

/-- Exact natural-number budget behind the consecutive-slope estimate.  The
square condition first gives `D+1 ≤ n²`; after expanding only
`(n+1)(2n+1) = 2n²+3n+1`, the remaining comparison is coefficientwise. -/
private theorem slope_drift_nat_budget
    {D n : Nat} (hD : 1 ≤ D) (hsq : 3 * D ≤ n * n) :
    (n + 1) * (2 * n + 1) * (D + 1) * (D * D - 1) ≤
      (n * n) * (2 * (D * D - 1) + 1) *
        (D + 1 + (2 * n + 1)) := by
  let d := D * D - 1
  let r := n + (2 * n + 1)
  let S := (2 * d) * (2 * n + 1) + (D + 1) + (2 * n + 1)
  have hfirst : r ≤ 3 * (2 * n + 1) := by
    dsimp only [r]
    omega
  have hsecond : D + 1 ≤ 2 * D := by omega
  have hcoeff : r * (D + 1) ≤
      (3 * (2 * n + 1)) * (2 * D) :=
    Nat.mul_le_mul hfirst hsecond
  have hsmall : r * (D + 1) * d ≤
      (3 * (2 * n + 1)) * (2 * D) * d :=
    Nat.mul_le_mul_right d hcoeff
  have hinside : (2 * d) * (2 * n + 1) ≤ S := by
    dsimp only [S]
    omega
  have hshape : 3 * D * S ≤ (n * n) * S :=
    Nat.mul_le_mul_right S hsq
  have hresidual : r * (D + 1) * d ≤
      (n * n) * S := by
    refine Nat.le_trans hsmall ?_
    refine Nat.le_trans ?_ hshape
    refine Nat.le_trans ?_ (Nat.mul_le_mul_left (3 * D) hinside)
    exact Nat.le_of_eq (by ac_rfl)
  have hquad : (n + 1) * (2 * n + 1) =
      2 * (n * n) + r := by
    dsimp only [r]
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
    ac_rfl
  have hleft :
      (n + 1) * (2 * n + 1) * (D + 1) * d =
        2 * (n * n) * (D + 1) * d +
          r * (D + 1) * d := by
    rw [hquad]
    simp only [Nat.add_mul]
  have hright :
      (n * n) * (2 * d + 1) * (D + 1 + (2 * n + 1)) =
        2 * (n * n) * (D + 1) * d + (n * n) * S := by
    have hinner :
        (2 * d + 1) * (D + 1 + (2 * n + 1)) =
          2 * (D + 1) * d + S := by
      dsimp only [S]
      simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul]
      ac_rfl
    rw [Nat.mul_assoc, hinner, Nat.mul_add]
    ac_rfl
  change (n + 1) * (2 * n + 1) * (D + 1) * d ≤
    (n * n) * (2 * d + 1) * (D + 1 + (2 * n + 1))
  rw [hleft, hright]
  exact Nat.add_le_add_left hresidual _

private theorem slope_drift_nat_budget_unreduced
    {D n : Nat} (hD : 1 ≤ D) (hsq : 3 * D ≤ n * n) :
    let d := D * D - 1
    (n + 1) * (2 * n + 1) *
        (d * d * (d * d) * (D + 1)) ≤
      (n * n) * ((d + d) * (d * d) + d * d) *
          (D + 1 + (2 * n + 1)) * d := by
  let d := D * D - 1
  have hnat := slope_drift_nat_budget hD hsq
  have hscaled := Nat.mul_le_mul_right (d * d * d) hnat
  dsimp only
  change
    ((n + 1) * (2 * n + 1) * (D + 1) * d) * (d * d * d) ≤
      ((n * n) * (2 * d + 1) * (D + 1 + (2 * n + 1))) *
        (d * d * d) at hscaled
  have hfactor :
      ((d + d) * (d * d) + d * d) =
        (2 * d + 1) * (d * d) := by
    simp only [Nat.add_mul, Nat.one_mul, Nat.two_mul]
  rw [hfactor]
  calc
    _ = ((n + 1) * (2 * n + 1) * (D + 1) * d) *
          (d * d * d) := by
      dsimp only [d]
      ac_rfl
    _ ≤ ((n * n) * (2 * d + 1) *
          (D + 1 + (2 * n + 1))) * (d * d * d) := hscaled
    _ = _ := by
      dsimp only [d]
      ac_rfl

/-- On the square-root right range, the reciprocal-growth slope envelope is
paid by the exact Bernoulli drift excess used in the linear carrier. -/
theorem lowerSixSlopeDriftEnvelope_le_excess_of_shape
    {k n : Nat} (hsq : 3 * (k + 2) ≤ n * n) :
    lowerSixSlopeDriftEnvelope k n ≤
      Q'.ofNat (n * n) * lowerSixDriftExcess k := by
  let A := Q'.ofNat (n + 1)
  let P := Q'.ofNat (2 * n + 1)
  let u := unit (driftDen k) (driftDen_pos k)
  let t := lowerSixOddPower (k + 1) n
  let B := bernDen (harmU (k + 1)) (2 * n + 1)
  have htB : t * B ≤ (1 : Q') := by
    dsimp only [t, B, lowerSixOddPower]
    unfold harmW
    exact oneSub_pow_mul_bernDen_le
      (harmU_nonneg (k + 1)) (harmU_le_one (k + 1)) (2 * n + 1)
  have hAPu0 : (0 : Q') ≤ A * P * u :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
        (HeatKernelRGStep.zero_le_ofNat _)) (unit_nonneg _ _)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (A * P * u) htB hAPu0
  have hleft : lowerSixSlopeDriftEnvelope k n * B ≈
      (A * P * u) * (t * B) := by
    unfold lowerSixSlopeDriftEnvelope
    dsimp only [A, P, u, t]
    drift_step_ring
  have hright : (A * P * u) * (1 : Q') ≈ A * P * u :=
    Q'.mul_one_eqv _
  have henvelopeCleared : lowerSixSlopeDriftEnvelope k n * B ≤
      A * P * u :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))
  have hnat := slope_drift_nat_budget_unreduced
    (D := k + 2) (n := n) (by omega) hsq
  have hbudget : A * P * u ≤
      (Q'.ofNat (n * n) * lowerSixDriftExcess k) * B := by
    show (A * P * u).num *
        (((Q'.ofNat (n * n) * lowerSixDriftExcess k) * B).den : Int) ≤
      ((Q'.ofNat (n * n) * lowerSixDriftExcess k) * B).num *
        (A * P * u).den
    unfold A P u B lowerSixDriftExcess driftDen harmU unit bernDen
    simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast,
      Q'.mkPos_num, Q'.mkPos_den, Q'.add_num_cast, Q'.add_den_cast,
      Q'.mul_num_cast, Q'.mul_den_cast, Int.mul_one, Int.one_mul]
    have h1n : (1 : Q').num = 1 := rfl
    have h1d : ((1 : Q').den : Int) = 1 := rfl
    rw [h1n, h1d, Int.mul_one, Int.one_mul]
    push_cast
    dsimp only at hnat
    rw [show k + 2 + 1 = k + 1 + 1 + 1 by omega] at hnat
    exact_mod_cast hnat
  have hboth : lowerSixSlopeDriftEnvelope k n * B ≤
      (Q'.ofNat (n * n) * lowerSixDriftExcess k) * B :=
    Q'.le_trans' _ _ _ henvelopeCleared hbudget
  exact BakryEmery.le_of_mul_le_mul_right_pos
    (bernDen_pos (harmU_nonneg (k + 1)) (2 * n + 1)) hboth

/-- Consequently the exact consecutive-slope loss is bounded by the same
drift excess that appears in the weight floor. -/
theorem lowerSixSlopeDrift_le_excess_of_shape
    {k n : Nat} (hsq : 3 * (k + 2) ≤ n * n) :
    lowerSixSlopeDrift k n ≤
      Q'.ofNat (n * n) * lowerSixDriftExcess k :=
  Q'.le_trans' _ _ _ (lowerSixSlopeDrift_le_envelope k n)
    (lowerSixSlopeDriftEnvelope_le_excess_of_shape hsq)

/-- Old-weighted linear payment over the complete retained right suffix. -/
def lowerSixScaledLinearCrossWindowSuffix (k : Nat) : Q' :=
  finSum
    (fun j => lowerSixModeWeight k (thetaWindowRight k + 1 + j) *
      lowerSixScaledLinearDriftCarrier k
        (thetaWindowRight k + 1 + j))
    (growingAnchor k - thetaWindowRight k)

/-- Old-weighted exact nonlinear remainder over the same suffix. -/
def lowerSixScaledRemainderCrossWindowSuffix (k : Nat) : Q' :=
  finSum
    (fun j => lowerSixModeWeight k (thetaWindowRight k + 1 + j) *
      lowerSixScaledDriftRemainder k
        (thetaWindowRight k + 1 + j))
    (growingAnchor k - thetaWindowRight k)

private theorem finSum_eqv_congr (f g : Nat → Q') : ∀ N,
    (∀ j, j < N → f j ≈ g j) → finSum f N ≈ finSum g N
  | 0, _ => Q'.eqv_refl 0
  | N + 1, h => by
      rw [finSum_succ, finSum_succ]
      exact Q'.add_eqv_congr'
        (finSum_eqv_congr f g N
          (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self N))))
        (h N (Nat.lt_succ_self N))

private theorem finSum_nonnegative_of_terms (f : Nat → Q') : ∀ N,
    (∀ j, j < N → (0 : Q') ≤ f j) → (0 : Q') ≤ finSum f N
  | 0, _ => Q'.le_refl' 0
  | N + 1, h => by
      rw [finSum_succ]
      exact Q'.zero_le_add _ _
        (finSum_nonnegative_of_terms f N
          (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self N))))
        (h N (Nat.lt_succ_self N))

private theorem suffix_crossTerm_eqv_weightedCarrier
    {k j : Nat} (hk : 48 ≤ k) :
    lowerSixScaledCrossTerm k (thetaWindowRight k + j) ≈
      lowerSixModeWeight k (thetaWindowRight k + 1 + j) *
        lowerSixScaledDriftCarrier k
          (thetaWindowRight k + 1 + j) := by
  have hR : 0 < thetaWindowRight k := by
    have hc : 1 ≤ thetaWindowCenter k :=
      Nat.le_trans (by decide : 1 ≤ 9)
        (thetaWindowCenter_ge_nine (show 38 ≤ k by omega))
    unfold thetaWindowRight
    omega
  let p := thetaWindowRight k + j - 1
  have hidx : thetaWindowRight k + j = p + 1 := by
    dsimp only [p]
    omega
  have hmode : p + 2 = thetaWindowRight k + 1 + j := by
    dsimp only [p]
    omega
  rw [hidx, ← hmode]
  exact lowerSixScaledCrossTerm_mode_factor k p

/-- Exact decomposition of the physical cross suffix into the Bernoulli
linear payment and the retained nonlinear drift remainder. -/
theorem lowerSixScaledCrossWindowSuffix_eqv_linear_add_remainder
    {k : Nat} (hk : 48 ≤ k) :
    lowerSixScaledCrossWindowSuffix k ≈
      lowerSixScaledLinearCrossWindowSuffix k +
        lowerSixScaledRemainderCrossWindowSuffix k := by
  let N := growingAnchor k - thetaWindowRight k
  let W := fun j => lowerSixModeWeight k
    (thetaWindowRight k + 1 + j)
  let L := fun j => lowerSixScaledLinearDriftCarrier k
    (thetaWindowRight k + 1 + j)
  let E := fun j => lowerSixScaledDriftRemainder k
    (thetaWindowRight k + 1 + j)
  have hterm : ∀ j, j < N →
      lowerSixScaledCrossTerm k (thetaWindowRight k + j) ≈
        W j * L j + W j * E j := by
    intro j hj
    refine Q'.eqv_trans _ _ _ (suffix_crossTerm_eqv_weightedCarrier hk) ?_
    refine Q'.eqv_trans _ (W j * (L j + E j)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left (W j) _ _
        (lowerSixScaledDriftCarrier_eqv_linear_add_remainder k
          (thetaWindowRight k + 1 + j))
    · exact Q'.mul_add_eqv (W j) (L j) (E j)
  have hsum := finSum_eqv_congr
    (fun j => lowerSixScaledCrossTerm k (thetaWindowRight k + j))
    (fun j => W j * L j + W j * E j) N hterm
  unfold lowerSixScaledCrossWindowSuffix
    lowerSixScaledLinearCrossWindowSuffix
    lowerSixScaledRemainderCrossWindowSuffix
  dsimp only [N, W, L, E] at hsum ⊢
  exact Q'.eqv_trans _ _ _ hsum
    (finSum_add
      (fun j => lowerSixModeWeight k (thetaWindowRight k + 1 + j) *
        lowerSixScaledLinearDriftCarrier k
          (thetaWindowRight k + 1 + j))
      (fun j => lowerSixModeWeight k (thetaWindowRight k + 1 + j) *
        lowerSixScaledDriftRemainder k
          (thetaWindowRight k + 1 + j))
      (growingAnchor k - thetaWindowRight k))

/-- The retained exact-minus-linear suffix is unconditionally nonnegative. -/
theorem lowerSixScaledRemainderCrossWindowSuffix_nonnegative
    {k : Nat} (hk : 48 ≤ k) :
    (0 : Q') ≤ lowerSixScaledRemainderCrossWindowSuffix k := by
  unfold lowerSixScaledRemainderCrossWindowSuffix
  apply finSum_nonnegative_of_terms
  intro j hj
  exact Q'.mul_nonneg _ _ (lowerSixModeWeight_nonnegative k _)
    (lowerSixScaledDriftRemainder_nonnegative hk j)

/-- The complete signed payment left after the linear suffix is placed
against the negative cross-window prefix. -/
def lowerSixScaledLinearCrossPaymentResidual (k : Nat) : Q' :=
  lowerSixScaledCrossWindowPrefix k +
    lowerSixScaledLinearCrossWindowSuffix k

/-- Exact shared-residual decomposition exposing the load-bearing nonlinear
payment next to the linear prefix/suffix residual. -/
theorem lowerSixScaledCrossShared_eqv_linearResidual_add_remainder
    {k : Nat} (hk : 48 ≤ k) :
    lowerSixScaledCrossShared k ≈
      lowerSixScaledLinearCrossPaymentResidual k +
        lowerSixScaledRemainderCrossWindowSuffix k := by
  exact Q'.eqv_trans _ _ _ (lowerSixScaledCrossShared_eqv_window hk)
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (lowerSixScaledCrossWindowPrefix k) _ _
        (lowerSixScaledCrossWindowSuffix_eqv_linear_add_remainder hk))
      (by
        unfold lowerSixScaledLinearCrossPaymentResidual
        exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)))

/-- A direct payment theorem retaining both the linear suffix and the exact
nonlinear drift remainder. -/
theorem lowerSixScaledWindowStep_of_linearResidual_payment
    {k : Nat} (hk : 48 ≤ k)
    (hpay : -lowerSixScaledLinearCrossPaymentResidual k ≤
      lowerSixScaledRemainderCrossWindowSuffix k) :
    LowerSixScaledWindowStep k := by
  have hsum : (0 : Q') ≤
      lowerSixScaledLinearCrossPaymentResidual k +
        lowerSixScaledRemainderCrossWindowSuffix k := by
    have h := Q'.add_le_add_left
      (lowerSixScaledLinearCrossPaymentResidual k) _ _ hpay
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.add_neg_self_eqv
            (lowerSixScaledLinearCrossPaymentResidual k)))) h
  have hshared : (0 : Q') ≤ lowerSixScaledCrossShared k :=
    Q'.le_trans' _ _ _ hsum
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (lowerSixScaledCrossShared_eqv_linearResidual_add_remainder hk)))
  exact lowerSixScaledWindowStep_of_shared_nonnegative hk hshared

#print axioms lowerSixWeightDriftRemainder_nonnegative
#print axioms lowerSixScaledDriftRemainder_nonnegative
#print axioms lowerSixScaledDriftCarrier_eqv_linear_add_remainder
#print axioms lowerSixOddPower_step_eqv
#print axioms thetaRootSlope_step_eqv
#print axioms lowerSixSlopeDrift_nonnegative
#print axioms lowerSixSlopeDrift_le_envelope
#print axioms lowerSixSlopeDriftEnvelope_le_excess_of_shape
#print axioms lowerSixSlopeDrift_le_excess_of_shape
#print axioms lowerSixScaledCrossWindowSuffix_eqv_linear_add_remainder
#print axioms lowerSixScaledRemainderCrossWindowSuffix_nonnegative
#print axioms lowerSixScaledCrossShared_eqv_linearResidual_add_remainder
#print axioms lowerSixScaledWindowStep_of_linearResidual_payment

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftScaleStep
