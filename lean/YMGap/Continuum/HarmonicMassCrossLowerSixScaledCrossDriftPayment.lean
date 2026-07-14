/-
Constructive lower payment extracted from the exact lower-six weight drift.

The unrestricted drift carrier is not nonnegative: its central band remains
adverse.  On the right suffix, however, the exact squared drift factor has a
Bernoulli floor.  This file proves that floor in `Q'`, packages the resulting
linearized carrier, and transports its pointwise payment to the complete
cross suffix.  A closed rational fence shows that deleting the drift factor
already fails at the first suffix mode in the induction regime.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftCarrier
import YMGap.Continuum.HarmonicWeightedAbelReserve

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftPayment

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicDriftAntisymmetry
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.HarmonicWeightedAbelReserve
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem drift_payment_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "drift_payment_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               drift_payment_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

private theorem bernoulli_step_algebra (N u : Q') :
    ((1 : Q') + N * u) * ((1 : Q') + u) ≈
      ((1 : Q') + (N + 1) * u) + N * (u * u) := by
  drift_payment_ring

private theorem square_one_add_algebra (u : Q') :
    ((1 : Q') + u) * ((1 : Q') + u) ≈
      (1 : Q') + ((u + u) + u * u) := by
  drift_payment_ring

/-- Constructive lower Bernoulli inequality for the project power function. -/
theorem qpow_one_add_bernoulli_lower {u : Q'} (hu : (0 : Q') ≤ u) :
    ∀ n, (1 : Q') + Q'.ofNat n * u ≤ qpow ((1 : Q') + u) n
  | 0 => by
      exact Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (1 : Q') _ _
          (Q'.zero_mul_eqv u)) (QPoly.q_add_zero_eqv 1))
  | n + 1 => by
      let r := (1 : Q') + u
      let L := (1 : Q') + Q'.ofNat n * u
      let T := (1 : Q') + (Q'.ofNat n + 1) * u
      have hr0 : (0 : Q') ≤ r := by
        dsimp only [r]
        exact Q'.zero_le_add _ _ (by decide) hu
      have hmul : L * r ≤ qpow r n * r :=
        Q'.mul_le_mul_of_nonneg_right _ _ r
          (qpow_one_add_bernoulli_lower hu n) hr0
      have hextra : (0 : Q') ≤ Q'.ofNat n * (u * u) :=
        Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
          (Q'.mul_nonneg _ _ hu hu)
      have hstep : T ≤ L * r := by
        have hadd := Q'.add_le_self_of_nonneg T
          (Q'.ofNat n * (u * u)) hextra
        exact Q'.le_trans' _ _ _ hadd
          (Q'.le_of_eqv
            (Q'.eqv_symm (bernoulli_step_algebra (Q'.ofNat n) u)))
      have hcast : Q'.ofNat (n + 1) ≈ Q'.ofNat n + 1 := by
        refine Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv n 1) ?_
        exact Q'.add_eqv_congr_left _ _ _ (by decide)
      have htarget : (1 : Q') + Q'.ofNat (n + 1) * u ≈ T := by
        dsimp only [T]
        exact Q'.add_eqv_congr_left (1 : Q') _ _
          (Q'.mul_eqv_congr_right _ _ u hcast)
      change (1 : Q') + Q'.ofNat (n + 1) * u ≤ qpow r n * r
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv htarget)
        (Q'.le_trans' _ _ _ hstep hmul)

/-- Exact positive excess in the squared harmonic drift base. -/
def lowerSixDriftExcess (k : Nat) : Q' :=
  let u := unit (driftDen k) (driftDen_pos k)
  (u + u) + u * u

/-- First-order-in-the-exponent floor retained from the exact weight drift. -/
def lowerSixWeightDriftFloor (k n : Nat) : Q' :=
  (1 : Q') + Q'.ofNat (n * n) * lowerSixDriftExcess k

theorem lowerSixDriftExcess_nonnegative (k : Nat) :
    (0 : Q') ≤ lowerSixDriftExcess k := by
  let u := unit (driftDen k) (driftDen_pos k)
  have hu : (0 : Q') ≤ u := unit_nonneg _ _
  unfold lowerSixDriftExcess
  dsimp only [u]
  exact Q'.zero_le_add _ _
    (Q'.zero_le_add _ _ hu hu)
    (Q'.mul_nonneg _ _ hu hu)

private theorem lowerSix_squaredDriftBase_eqv (k : Nat) :
    driftRatio k * driftRatio k ≈
      (1 : Q') + lowerSixDriftExcess k := by
  let u := unit (driftDen k) (driftDen_pos k)
  have hr := driftRatio_eqv_one_add_unitDen k
  refine Q'.eqv_trans _
    (((1 : Q') + u) * ((1 : Q') + u)) _ ?_ ?_
  · exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hr)
      (Q'.mul_eqv_congr_left _ _ _ hr)
  · unfold lowerSixDriftExcess
    dsimp only [u]
    exact square_one_add_algebra u

/-- The exact exponential weight drift dominates its constructive Bernoulli
floor at every scale and mode. -/
theorem lowerSixWeightDriftFloor_le_factor (k n : Nat) :
    lowerSixWeightDriftFloor k n ≤ lowerSixWeightDriftFactor k n := by
  have hbase := lowerSix_squaredDriftBase_eqv k
  have hpow := qpow_eqv_congr_base hbase (n * n)
  have hbern := qpow_one_add_bernoulli_lower
    (lowerSixDriftExcess_nonnegative k) (n * n)
  unfold lowerSixWeightDriftFloor lowerSixWeightDriftFactor
  exact Q'.le_trans' _ _ _ hbern (Q'.le_of_eqv (Q'.eqv_symm hpow))

/-- Linearized drift carrier obtained by replacing the exact exponential
factor with its proved lower floor. -/
def lowerSixScaledLinearDriftCarrier (k n : Nat) : Q' :=
  Q'.ofNat (k + 3) * lowerSixWeightDriftFloor k n *
      lowerSixModeCarrier (k + 1) n +
    -(Q'.ofNat (k + 2) * lowerSixModeCarrier k n)

/-- If the next-scale mode carrier is nonnegative, payment by the linearized
carrier implies payment by the exact drift carrier. -/
theorem lowerSixScaledDriftCarrier_nonnegative_of_linear
    {k n : Nat}
    (hnext : (0 : Q') ≤ lowerSixModeCarrier (k + 1) n)
    (hlinear : (0 : Q') ≤ lowerSixScaledLinearDriftCarrier k n) :
    (0 : Q') ≤ lowerSixScaledDriftCarrier k n := by
  have hfactor := lowerSixWeightDriftFloor_le_factor k n
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat (k + 3)) hfactor (HeatKernelRGStep.zero_le_ofNat _)
  have hmode := Q'.mul_le_mul_of_nonneg_right _ _
    (lowerSixModeCarrier (k + 1) n) hscale hnext
  have hadd := Q'.add_le_add_right _ _
    (-(Q'.ofNat (k + 2) * lowerSixModeCarrier k n)) hmode
  unfold lowerSixScaledLinearDriftCarrier at hlinear
  unfold lowerSixScaledDriftCarrier
  exact Q'.le_trans' _ _ _ hlinear hadd

/-- Exact pointwise sufficient certificate on the retained right suffix. -/
def LowerSixLinearDriftSuffixCertificate (k : Nat) : Prop :=
  ∀ j, j < growingAnchor k - thetaWindowRight k →
    let n := thetaWindowRight k + j + 1
    (0 : Q') ≤ lowerSixModeCarrier (k + 1) n ∧
      (0 : Q') ≤ lowerSixScaledLinearDriftCarrier k n

/-- The linear drift certificate pays the complete exact cross suffix. -/
theorem lowerSixScaledCrossWindowSuffix_nonnegative_of_linearCertificate
    {k : Nat} (hk : 48 ≤ k)
    (hcert : LowerSixLinearDriftSuffixCertificate k) :
    (0 : Q') ≤ lowerSixScaledCrossWindowSuffix k := by
  apply lowerSixScaledCrossWindowSuffix_nonnegative_of_driftCarriers hk
  intro j hj
  exact lowerSixScaledDriftCarrier_nonnegative_of_linear
    (hcert j hj).1 (hcert j hj).2

/-- Carrier with the harmonic weight drift incorrectly replaced by one. -/
def lowerSixUnitDriftCarrier (k n : Nat) : Q' :=
  Q'.ofNat (k + 3) * lowerSixModeCarrier (k + 1) n +
    -(Q'.ofNat (k + 2) * lowerSixModeCarrier k n)

/-- Deleting the weight drift fails exactly at the first right-suffix mode
at the first symbolic induction scale. -/
theorem lowerSix_unitDrift_fails_k248_firstSuffix :
    ¬ ((0 : Q') ≤ lowerSixUnitDriftCarrier 248
      (thetaWindowRight 248 + 1)) := by
  unfold lowerSixUnitDriftCarrier lowerSixModeCarrier
    lowerSixDirichletProfile thetaRootSlope thetaWindowRight
    thetaWindowCenter thetaWindowLength harmW harmU oneSub unit qpow
  decide

/-- The unrestricted exact drift carrier is still false in the adverse
central band, so the suffix range in the payment theorem is load-bearing. -/
theorem lowerSix_driftCarrier_unrestricted_fails_k48_n8 :
    ¬ ((0 : Q') ≤ lowerSixScaledDriftCarrier 48 8) := by
  unfold lowerSixScaledDriftCarrier lowerSixWeightDriftFactor
    lowerSixModeCarrier lowerSixDirichletProfile thetaRootSlope
    driftRatio Q'.divPos Q'.recipPos
    harmW harmU oneSub unit qpow
  decide

/-- At the first induction scale and first suffix mode, the proved linear
floor already restores the sign lost by the unit-drift surrogate. -/
theorem lowerSix_linearDrift_holds_k248_firstSuffix :
    (0 : Q') ≤ lowerSixScaledLinearDriftCarrier 248
      (thetaWindowRight 248 + 1) := by
  unfold lowerSixScaledLinearDriftCarrier lowerSixWeightDriftFloor
    lowerSixDriftExcess lowerSixModeCarrier lowerSixDirichletProfile
    thetaRootSlope thetaWindowRight thetaWindowCenter thetaWindowLength
    driftDen harmW harmU oneSub unit qpow
  decide

#print axioms qpow_one_add_bernoulli_lower
#print axioms lowerSixDriftExcess_nonnegative
#print axioms lowerSixWeightDriftFloor_le_factor
#print axioms lowerSixScaledDriftCarrier_nonnegative_of_linear
#print axioms lowerSixScaledCrossWindowSuffix_nonnegative_of_linearCertificate
#print axioms lowerSix_unitDrift_fails_k248_firstSuffix
#print axioms lowerSix_driftCarrier_unrestricted_fails_k48_n8
#print axioms lowerSix_linearDrift_holds_k248_firstSuffix

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftPayment
