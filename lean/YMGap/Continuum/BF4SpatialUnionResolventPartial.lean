/-
# Rate-dependent geometric sums of the SAME union two-step transfer

S_n x = sum_{j<n} T_{2j}(center x). The actual one-step squared-norm
rate q(w) gives ||T_2 v||^2 <= q(w)^2 ||v||^2. Weighted positivity,
not a strengthened nome guard, bounds every partial sum by
(1-q(w))^(-2) ||center x||^2. Exact splitting and the existing geometric
cutoff make the original partial-sum representatives a Cauchy row family.

All constants and both layers of moduli remain data. This is fixed-spacing
small-nome SU(2), not a continuum inverse or physical mass calibration.
-/

import YMGap.Continuum.BF4SpatialUnionWeightedNorm
import YMGap.Continuum.BF4SpatialUnionCauchyRows

namespace YMGap.Continuum.BF4SpatialUnionResolventPartial

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4SpatialUnion (zeroStage)
open YMGap.Continuum.BF4SpatialUnionSeminorm
open YMGap.Continuum.BF4SpatialUnionPairingData
open YMGap.Continuum.BF4SpatialUnionGeometry
open YMGap.Continuum.BF4SpatialUnionLinear
open YMGap.Continuum.BF4SpatialUnionBilinear
open YMGap.Continuum.BF4SpatialUnionLinearLaws
open YMGap.Continuum.BF4SpatialUnionUnitProjection
open YMGap.Continuum.BF4SpatialUnionCentered
open YMGap.Continuum.BF4SpatialUnionCompletedDistance
open YMGap.Continuum.BF4SpatialUnionRelaxation
open YMGap.Continuum.BF4SpatialUnionWeightedNorm
open YMGap.Continuum.CRealSeminormCauchyRows
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap
  (twoStepRate twoStepRate_positive twoStepRate_lt_one)
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

theorem scale_congr {a b : Q'} (h : a.eqv b) (r : RC) : RCscale a r = RCscale b r := by
  refine Quotient.inductionOn r ?_
  intro R
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.mul_eqv_congr_right a b (R.approx n) h))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "DP" => distanceData hw0 hw1 hsmall hd hs
local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs
local notation "C" => center hw0 hw1 hsmall hd hs
local notation "P" => unitProjection hw0 hw1 hsmall hd hs
local notation "A" => completedAdd hw0 hw1 hsmall hd hs
local notation "Z" => completedZero hw0 hw1 hsmall hd hs
local notation "q" => twoStepRate w hd
local notation "K" => budget q (twoStepRate_lt_one hw0 hd hs)

theorem completedTime_zeroState (n : Nat) : T n Z = Z := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro y
  rw [completedInner_time_balance, completedInner_zero_left, completedInner_zero_left]

theorem center_zero : C Z = Z :=
  (center_fixed_iff hw0 hw1 hsmall hd hs Z).mpr
    (completedInner_zero_left hw0 hw1 hsmall hd hs (completedUnit hw0 hw1 hsmall hd hs))

theorem sub_add_right_cancel (x y : V) : completedSub hw0 hw1 hsmall hd hs (A x y) y = x := by
  change A (A x y) (completedNeg hw0 hw1 hsmall hd hs y) = x
  rw [completedAdd_assoc, completedAdd_comm hw0 hw1 hsmall hd hs y (completedNeg hw0 hw1 hsmall hd hs y),
    completedNeg_add, completedAdd_zero]

theorem sub_add_left_cancel (x y : V) : completedSub hw0 hw1 hsmall hd hs (A x y) x = y := by
  rw [completedAdd_comm hw0 hw1 hsmall hd hs x y, sub_add_right_cancel]

/-- Finite sums on the original completed carrier, with actual centering and time. -/
def partialSum (x : V) : Nat → V
  | 0 => Z
  | n+1 => A (C x) (T 2 (partialSum x n))

theorem partial_centered (x : V) : ∀ n,
    C (partialSum hw0 hw1 hsmall hd hs x n) = partialSum hw0 hw1 hsmall hd hs x n
  | 0 => center_zero hw0 hw1 hsmall hd hs
  | n+1 => by
      change C (A (C x) (T 2 (partialSum hw0 hw1 hsmall hd hs x n))) = _
      rw [center_add, center_idempotent, ← completedTime_center, partial_centered x n]
      rfl

theorem partial_time (lag : Nat) (x : V) : ∀ n,
    partialSum hw0 hw1 hsmall hd hs (T lag x) n = T lag (partialSum hw0 hw1 hsmall hd hs x n)
  | 0 => (completedTime_zeroState hw0 hw1 hsmall hd hs lag).symm
  | n+1 => by
      simp only [partialSum, ← completedTime_center, partial_time lag x n,
        completedTime_addition, ← completedTime_add]
      rw [Nat.add_comm 2 lag]

theorem partial_split (x : V) : ∀ n k,
    partialSum hw0 hw1 hsmall hd hs x (n+k) =
      A (partialSum hw0 hw1 hsmall hd hs x n) (T (2*n) (partialSum hw0 hw1 hsmall hd hs x k))
  | 0, k => by
      rw [Nat.zero_add, Nat.mul_zero, completedTime_zero]
      exact (completedZero_add hw0 hw1 hsmall hd hs _).symm
  | n+1, k => by
      rw [show n+1+k = (n+k)+1 by omega]
      change A (C x) (T 2 (partialSum hw0 hw1 hsmall hd hs x (n+k))) = _
      rw [partial_split x n k, completedTime_addition, ← completedTime_add,
        ← completedAdd_assoc]
      rw [show 2+2*n = 2*(n+1) by omega]
      rfl

/-- The budget depends explicitly on the actual rate, not on the sum length. -/
theorem partial_norm_bound (x : V) : ∀ n,
    RCle (B (partialSum hw0 hw1 hsmall hd hs x n) (partialSum hw0 hw1 hsmall hd hs x n))
      (RCscale K (B (C x) (C x)))
  | 0 => by
      rw [partialSum, completedInner_zero_left]
      have h := RCscale_mono (budget_nonnegative q (twoStepRate_lt_one hw0 hd hs))
        (completedInner_nonnegative hw0 hw1 hsmall hd hs (C x))
      rw [RCscale_RCzero] at h
      exact h
  | n+1 => by
      have ht := centered_norm_decay hw0 hw1 hsmall hd hs (partialSum hw0 hw1 hsmall hd hs x n) 2
      rw [partial_centered] at ht
      have ht' := RCle_trans ht
        (RCscale_mono (Q'.pow_nonneg q (Q'.le_of_lt (twoStepRate_positive hw0 hd)) 2)
          (partial_norm_bound x n))
      rw [RCscale_RCscale] at ht'
      have hq2 : (q^2).eqv (q*q) :=
        Q'.mul_eqv_congr_left q (q*1) q (Q'.mul_one_eqv q)
      rw [scale_congr (Q'.mul_eqv_congr_right _ _ K hq2)] at ht'
      exact series_step_bound hw0 hw1 hsmall hd hs q (twoStepRate_positive hw0 hd)
        (twoStepRate_lt_one hw0 hd hs) (C x) (T 2 (partialSum hw0 hw1 hsmall hd hs x n)) ht'

theorem partial_tail (x : V) (n k : Nat) :
    completedSub hw0 hw1 hsmall hd hs (partialSum hw0 hw1 hsmall hd hs x (n+k))
      (partialSum hw0 hw1 hsmall hd hs x n) = partialSum hw0 hw1 hsmall hd hs (T (2*n) x) k := by
  rw [partial_split, sub_add_left_cancel, partial_time]

theorem partial_tail_bound (x : V) (n k : Nat) :
    RCle (completedDist hw0 hw1 hsmall hd hs (partialSum hw0 hw1 hsmall hd hs x (n+k))
      (partialSum hw0 hw1 hsmall hd hs x n))
      (RCscale K (completedDist hw0 hw1 hsmall hd hs (T (2*n) x) (P x))) := by
  unfold completedDist
  rw [partial_tail, relaxation_difference, completedTime_center]
  exact partial_norm_bound hw0 hw1 hsmall hd hs (T (2*n) x) k

/-- Every finite sum has computed representatives; no quotient lift is selected. -/
def partialCauchy (X : (D).Cauchy) : Nat → (D).Cauchy
  | 0 => (D).constant zeroStage
  | n+1 => addCauchy hw0 hw1 hsmall hd hs (centerCauchy hw0 hw1 hsmall hd hs X)
      ((timeNonexpansive hw0 hw1 hsmall hd hs 2).mapCauchy (partialCauchy X n))

theorem partialCauchy_pin (X : (D).Cauchy) : ∀ n,
    Quotient.mk (D).completionSetoid (partialCauchy hw0 hw1 hsmall hd hs X n) =
      partialSum hw0 hw1 hsmall hd hs (Quotient.mk (D).completionSetoid X) n
  | 0 => rfl
  | n+1 => by
      change A (C (Quotient.mk (D).completionSetoid X))
        (T 2 (Quotient.mk (D).completionSetoid (partialCauchy hw0 hw1 hsmall hd hs X n))) = _
      rw [partialCauchy_pin]
      rfl

def seriesModulus (X : (D).Cauchy) (epsilon : Q') : Nat :=
  geometricCutoff q (K * normCap hw0 hw1 hsmall hd hs X) epsilon

theorem partial_tail_small (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n k : Nat) (hn : seriesModulus hw0 hw1 hsmall hd hs X epsilon ≤ n) :
    RCle (completedDist hw0 hw1 hsmall hd hs
      (partialSum hw0 hw1 hsmall hd hs (Quotient.mk (D).completionSetoid X) (n+k))
      (partialSum hw0 hw1 hsmall hd hs (Quotient.mk (D).completionSetoid X) n))
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  have hK := budget_nonnegative q (twoStepRate_lt_one hw0 hd hs)
  have hq := Q'.le_of_lt (twoStepRate_positive hw0 hd)
  have h := RCle_trans (partial_tail_bound hw0 hw1 hsmall hd hs _ n k)
    (RCscale_mono hK (RCle_trans
      (relaxation_norm_bound hw0 hw1 hsmall hd hs (2*n) (Quotient.mk (D).completionSetoid X))
      (RCscale_mono (Q'.pow_nonneg q hq (2*n)) (norm_le_cap hw0 hw1 hsmall hd hs X))))
  apply RCle_trans h
  apply leEv_le_ofQ'_of_approx_le
  intro j
  have heq : (K * (q^(2*n) * normCap hw0 hw1 hsmall hd hs X)).eqv
      (q^(2*n) * (K * normCap hw0 hw1 hsmall hd hs X)) :=
    RingNormaliser.poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => K | 1 => q^(2*n) | _ => normCap hw0 hw1 hsmall hd hs X)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
    (geometric_bound hq (twoStepRate_lt_one hw0 hd hs)
      (Q'.mul_nonneg _ _ hK (normCap_nonnegative hw0 hw1 hsmall hd hs X)) he (2*n)
      (Nat.le_trans hn (by omega)))

def seriesRows (X : (D).Cauchy) : CauchyRows DP where
  row := partialCauchy hw0 hw1 hsmall hd hs X
  modulus := seriesModulus hw0 hw1 hsmall hd hs X
  isCauchy := by
    intro epsilon he m n hm hn
    change RCle (completedDist hw0 hw1 hsmall hd hs
      (Quotient.mk (D).completionSetoid (partialCauchy hw0 hw1 hsmall hd hs X m))
      (Quotient.mk (D).completionSetoid (partialCauchy hw0 hw1 hsmall hd hs X n))) _
    rw [partialCauchy_pin, partialCauchy_pin]
    by_cases hmn : m ≤ n
    · rw [completedDist_symm, show n = m+(n-m) by omega]
      exact partial_tail_small hw0 hw1 hsmall hd hs X epsilon he m (n-m) hm
    · rw [show m = n+(m-n) by omega]
      exact partial_tail_small hw0 hw1 hsmall hd hs X epsilon he n (m-n) hn

theorem seriesRows_point (X : (D).Cauchy) (n : Nat) :
    rowPoint DP (seriesRows hw0 hw1 hsmall hd hs X) n =
      partialSum hw0 hw1 hsmall hd hs (Quotient.mk (D).completionSetoid X) n :=
  partialCauchy_pin hw0 hw1 hsmall hd hs X n

end YMGap.Continuum.BF4SpatialUnionResolventPartial

#print axioms YMGap.Continuum.BF4SpatialUnionResolventPartial.scale_congr
#print axioms YMGap.Continuum.BF4SpatialUnionResolventPartial.completedTime_zeroState
#print axioms YMGap.Continuum.BF4SpatialUnionResolventPartial.center_zero
#print axioms YMGap.Continuum.BF4SpatialUnionResolventPartial.sub_add_right_cancel
#print axioms YMGap.Continuum.BF4SpatialUnionResolventPartial.sub_add_left_cancel
#print axioms YMGap.Continuum.BF4SpatialUnionResolventPartial.partialSum
#print axioms YMGap.Continuum.BF4SpatialUnionResolventPartial.partial_centered
#print axioms YMGap.Continuum.BF4SpatialUnionResolventPartial.partial_time
#print axioms YMGap.Continuum.BF4SpatialUnionResolventPartial.partial_split
#print axioms YMGap.Continuum.BF4SpatialUnionResolventPartial.partial_norm_bound
#print axioms YMGap.Continuum.BF4SpatialUnionResolventPartial.partial_tail
#print axioms YMGap.Continuum.BF4SpatialUnionResolventPartial.partial_tail_bound
#print axioms YMGap.Continuum.BF4SpatialUnionResolventPartial.partialCauchy
#print axioms YMGap.Continuum.BF4SpatialUnionResolventPartial.partialCauchy_pin
#print axioms YMGap.Continuum.BF4SpatialUnionResolventPartial.seriesModulus
#print axioms YMGap.Continuum.BF4SpatialUnionResolventPartial.partial_tail_small
#print axioms YMGap.Continuum.BF4SpatialUnionResolventPartial.seriesRows
#print axioms YMGap.Continuum.BF4SpatialUnionResolventPartial.seriesRows_point
