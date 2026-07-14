/-
Exact drift-carrier coordinates for the denominator-scaled lower-six step.

The old and new squared heat-kernel weights differ by the square of the
exact harmonic drift ratio at every exponent.  Factoring this positive old
weight out of a common-mode cross term leaves one explicit drift carrier.
This retains the exponentially amplified suffix reserve: replacing the
drift factor by one is not a sound route to the required cross-scale sign.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossWindow
import YMGap.Continuum.HarmonicWeightDriftFence

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftCarrier

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossWindow
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledWindowDifference
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.RefinedRetune
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem drift_carrier_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "drift_carrier_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               drift_carrier_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

private theorem scaled_drift_factor_algebra
    (D1 D W F C1 C0 : Q') :
    D1 * ((W * F) * C1) + -(D * (W * C0)) ≈
      W * (D1 * F * C1 + -(D * C0)) := by
  drift_carrier_ring

private theorem square_drift_algebra (W R : Q') :
    (W * R) * (W * R) ≈ (W * W) * (R * R) := by
  drift_carrier_ring

/-- Exact multiplicative drift of the squared base at mode `n`. -/
def lowerSixWeightDriftFactor (k n : Nat) : Q' :=
  qpow (driftRatio k * driftRatio k) (n * n)

/-- The carrier left after extracting the old squared heat-kernel weight
from a denominator-scaled common-mode difference. -/
def lowerSixScaledDriftCarrier (k n : Nat) : Q' :=
  Q'.ofNat (k + 3) * lowerSixWeightDriftFactor k n *
      lowerSixModeCarrier (k + 1) n +
    -(Q'.ofNat (k + 2) * lowerSixModeCarrier k n)

/-- Denominator-scaled difference of one physical Dirichlet mode. -/
def lowerSixScaledIncrementDifference (k n : Nat) : Q' :=
  Q'.ofNat (k + 3) * lowerSixDirichletIncrement (k + 1) n +
    -(Q'.ofNat (k + 2) * lowerSixDirichletIncrement k n)

/-- Exact mode-wise transport of the squared heat-kernel weight. -/
theorem lowerSixModeWeight_step_eqv (k n : Nat) :
    lowerSixModeWeight (k + 1) n ≈
      lowerSixModeWeight k n * lowerSixWeightDriftFactor k n := by
  have hs : harmW (k + 1) * harmW (k + 1) ≈
      (harmW k * harmW k) * (driftRatio k * driftRatio k) := by
    have h := harmW_step_eqv k
    refine Q'.eqv_trans _
      ((harmW k * driftRatio k) * (harmW k * driftRatio k)) _ ?_ ?_
    · exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ h)
        (Q'.mul_eqv_congr_left _ _ _ h)
    · exact square_drift_algebra _ _
  unfold lowerSixModeWeight lowerSixWeightDriftFactor
  refine Q'.eqv_trans _
    (qpow ((harmW k * harmW k) *
      (driftRatio k * driftRatio k)) (n * n)) _ ?_ ?_
  · exact qpow_eqv_congr_base hs (n * n)
  · exact qpow_mul_base (harmW k * harmW k)
      (driftRatio k * driftRatio k) (n * n)

/-- The physical scaled increment factors as an old positive weight times
the exact drift carrier. -/
theorem lowerSixScaledIncrementDifference_mode_factor (k n : Nat) :
    lowerSixScaledIncrementDifference k n ≈
      lowerSixModeWeight k n * lowerSixScaledDriftCarrier k n := by
  have hnext := lowerSixDirichletIncrement_mode_factor (k + 1) n
  have hold := lowerSixDirichletIncrement_mode_factor k n
  have hmode : lowerSixScaledIncrementDifference k n ≈
      Q'.ofNat (k + 3) *
          (lowerSixModeWeight (k + 1) n * lowerSixModeCarrier (k + 1) n) +
        -(Q'.ofNat (k + 2) *
          (lowerSixModeWeight k n * lowerSixModeCarrier k n)) := by
    unfold lowerSixScaledIncrementDifference
    exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left (Q'.ofNat (k + 3)) _ _ hnext)
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat (k + 2)) _ _ hold))
  have hw := lowerSixModeWeight_step_eqv k n
  refine Q'.eqv_trans _ _ _ hmode ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (k + 3) *
        ((lowerSixModeWeight k n * lowerSixWeightDriftFactor k n) *
          lowerSixModeCarrier (k + 1) n) +
      -(Q'.ofNat (k + 2) *
        (lowerSixModeWeight k n * lowerSixModeCarrier k n))) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat (k + 3)) _ _
        (Q'.mul_eqv_congr_right _ _ _ hw))
  · unfold lowerSixScaledDriftCarrier
    exact scaled_drift_factor_algebra _ _ _ _ _ _

/-- The exact common-mode cross term at every noninitial Abel index factors
as an old positive weight times the new drift carrier. -/
theorem lowerSixScaledCrossTerm_mode_factor (k j : Nat) :
    lowerSixScaledCrossTerm k (j + 1) ≈
      lowerSixModeWeight k (j + 2) *
        lowerSixScaledDriftCarrier k (j + 2) := by
  have hnext := lowerSixAbel_term_eqv (k + 1) (j + 1)
  have hold := lowerSixAbel_term_eqv k (j + 1)
  have hnext' : lowerSixWeightedAbelTerm (k + 1) (j + 1) ≈
      lowerSixDirichletIncrement (k + 1) (j + 2) := by
    simpa [lowerSixWeightedAbelTerm, lowerSixAugmentedIncrement,
      Nat.add_assoc] using hnext
  have hold' : lowerSixWeightedAbelTerm k (j + 1) ≈
      lowerSixDirichletIncrement k (j + 2) := by
    simpa [lowerSixWeightedAbelTerm, lowerSixAugmentedIncrement,
      Nat.add_assoc] using hold
  have hphysical : lowerSixScaledCrossTerm k (j + 1) ≈
      lowerSixScaledIncrementDifference k (j + 2) := by
    unfold lowerSixScaledCrossTerm lowerSixScaledIncrementDifference
    exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left (Q'.ofNat (k + 3)) _ _ hnext')
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat (k + 2)) _ _ hold'))
  exact Q'.eqv_trans _ _ _ hphysical
    (lowerSixScaledIncrementDifference_mode_factor k (j + 2))

theorem lowerSixModeWeight_nonnegative (k n : Nat) :
    (0 : Q') ≤ lowerSixModeWeight k n := by
  unfold lowerSixModeWeight
  exact qpow_nonneg _
    (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _

/-- A nonnegative drift carrier gives the corresponding noninitial
common-mode cross term. -/
theorem lowerSixScaledCrossTerm_nonnegative_of_driftCarrier
    {k j : Nat}
    (hcarrier : (0 : Q') ≤ lowerSixScaledDriftCarrier k (j + 2)) :
    (0 : Q') ≤ lowerSixScaledCrossTerm k (j + 1) := by
  have hproduct : (0 : Q') ≤
      lowerSixModeWeight k (j + 2) *
        lowerSixScaledDriftCarrier k (j + 2) :=
    Q'.mul_nonneg _ _ (lowerSixModeWeight_nonnegative k (j + 2)) hcarrier
  exact Q'.le_trans' _ _ _ hproduct
    (Q'.le_of_eqv
      (Q'.eqv_symm (lowerSixScaledCrossTerm_mode_factor k j)))

private theorem finSum_nonnegative_of_terms (f : Nat → Q') : ∀ N,
    (∀ j, j < N → (0 : Q') ≤ f j) → (0 : Q') ≤ finSum f N
  | 0, _ => Q'.le_refl' 0
  | N + 1, h => by
      rw [finSum_succ]
      exact Q'.zero_le_add _ _
        (finSum_nonnegative_of_terms f N
          (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self N))))
        (h N (Nat.lt_succ_self N))

private theorem thetaWindowRight_pos {k : Nat} (hk : 48 ≤ k) :
    0 < thetaWindowRight k := by
  have hc : 1 ≤ thetaWindowCenter k :=
    Nat.le_trans (by decide : 1 ≤ 9)
      (thetaWindowCenter_ge_nine (show 38 ≤ k by omega))
  unfold thetaWindowRight
  omega

/-- Pointwise nonnegativity of the exact drift carriers on the retained
right suffix is sufficient for nonnegativity of the whole cross suffix. -/
theorem lowerSixScaledCrossWindowSuffix_nonnegative_of_driftCarriers
    {k : Nat} (hk : 48 ≤ k)
    (hcarrier : ∀ j, j < growingAnchor k - thetaWindowRight k →
      (0 : Q') ≤ lowerSixScaledDriftCarrier k
        (thetaWindowRight k + j + 1)) :
    (0 : Q') ≤ lowerSixScaledCrossWindowSuffix k := by
  unfold lowerSixScaledCrossWindowSuffix
  apply finSum_nonnegative_of_terms
  intro j hj
  have hR : 0 < thetaWindowRight k := thetaWindowRight_pos hk
  let p := thetaWindowRight k + j - 1
  have hindex : thetaWindowRight k + j = p + 1 := by
    dsimp only [p]
    omega
  rw [hindex]
  apply lowerSixScaledCrossTerm_nonnegative_of_driftCarrier
  have hmode : p + 2 = thetaWindowRight k + j + 1 := by
    dsimp only [p]
    omega
  rw [hmode]
  exact hcarrier j hj

#print axioms lowerSixModeWeight_step_eqv
#print axioms lowerSixScaledIncrementDifference_mode_factor
#print axioms lowerSixScaledCrossTerm_mode_factor
#print axioms lowerSixModeWeight_nonnegative
#print axioms lowerSixScaledCrossTerm_nonnegative_of_driftCarrier
#print axioms lowerSixScaledCrossWindowSuffix_nonnegative_of_driftCarriers

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftCarrier
