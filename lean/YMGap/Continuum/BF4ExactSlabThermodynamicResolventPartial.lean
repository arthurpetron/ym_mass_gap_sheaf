/-
# Geometric partial sums of the ORIGINAL two-step time operator

For the actual thermodynamic plaquette OS completion, put
S_n x = sum_{j<n} T_{2j}(center x). The existing squared-norm decay gives
||T_2 v||^2 <= (1/4)||v||^2 on the unit complement. The sqrt-free triangle
then proves ||S_n x||^2 <= 4||center x||^2 by induction, with no spectral
decomposition. Exact splitting identifies every tail with a translated
partial sum. The existing relaxation modulus therefore makes these partial
sums a represented Cauchy family on the SAME carrier.

The scalar budget is independently checked by
computations/original_thermodynamic_resolvent_budget.py. This is a fixed-nome,
fixed-spacing SU(2) statement, not full observable realization or continuum
scaling. The limit and inverse identities are separate downstream results.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicFixedUnit
import YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows

namespace YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPosdef
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar
open YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)

local notation "D" => seminorm
local notation "B" => completedInner

theorem scale_congr {a b : Q'} (h : a.eqv b) (r : RC) : RCscale a r = RCscale b r := by
  refine Quotient.inductionOn r ?_
  intro R
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.mul_eqv_congr_right a b (R.approx n) h))

theorem four_copies (r : RC) : RCadd (RCadd r r) (RCadd r r) = RCscale 4 r := by
  refine Quotient.inductionOn r ?_
  intro R
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0)))
      (.mul (.const 4) (.var 0)) (by decide) (fun _ => R.approx n)))

theorem sub_add_right_cancel (x y : Completion) : completedSub (completedAdd x y) y = x := by
  change completedAdd (completedAdd x y) (completedNeg y) = x
  rw [completedAdd_assoc, completedAdd_comm y (completedNeg y), completedNeg_add, completedAdd_zero]

theorem sub_add_left_cancel (x y : Completion) : completedSub (completedAdd x y) x = y := by
  rw [completedAdd_comm x y, sub_add_right_cancel]

theorem norm_add_bound (x y : Completion) :
    RCle (B (completedAdd x y) (completedAdd x y))
      (RCadd (RCadd (B x x) (B x x)) (RCadd (B y y) (B y y))) := by
  have h := completedDist_triangle (completedAdd x y) y completedZero
  unfold completedDist at h
  rw [completedSub_zero, sub_add_right_cancel, completedSub_zero] at h
  exact h

/-- The finite geometric series of the actual time operator, centered at input. -/
def partialSum (x : Completion) : Nat → Completion
  | 0 => completedZero
  | n+1 => completedAdd (center x) (completedTime 2 (partialSum x n))

theorem partial_centered (x : Completion) : ∀ n, center (partialSum x n) = partialSum x n
  | 0 => center_zero
  | n+1 => by
      change center (completedAdd (center x) (completedTime 2 (partialSum x n))) = _
      rw [center_add, center_idempotent, ← completedTime_center, partial_centered x n]
      rfl

theorem partial_time (lag : Nat) (x : Completion) : ∀ n,
    partialSum (completedTime lag x) n = completedTime lag (partialSum x n)
  | 0 => (completedTime_zeroState lag).symm
  | n+1 => by
      simp only [partialSum, ← completedTime_center, partial_time lag x n,
        completedTime_add, completedTime_comp]
      rw [Nat.add_comm 2 lag]

theorem partial_split (x : Completion) : ∀ n k,
    partialSum x (n+k) = completedAdd (partialSum x n) (completedTime (2*n) (partialSum x k))
  | 0, k => by rw [Nat.zero_add, Nat.mul_zero, completedTime_zero]; exact (completedZero_add _).symm
  | n+1, k => by
      rw [show n+1+k = (n+k)+1 by omega]
      change completedAdd (center x) (completedTime 2 (partialSum x (n+k))) = _
      rw [partial_split x n k, completedTime_add, completedTime_comp,
        ← completedAdd_assoc]
      rw [show 2*n+2 = 2*(n+1) by omega]
      rfl

/-- A common squared-norm ceiling, with no bound on the number of terms. -/
theorem partial_norm_bound (x : Completion) : ∀ n,
    RCle (B (partialSum x n) (partialSum x n)) (RCscale 4 (B (center x) (center x)))
  | 0 => by
      rw [partialSum, completedInner_zero_left]
      have h := RCscale_mono (by decide : (0 : Q') ≤ 4) (completedInner_nonnegative (center x))
      rw [RCscale_RCzero] at h
      exact h
  | n+1 => by
      have ht := centered_norm_decay (partialSum x n) 2
      rw [partial_centered] at ht
      have ht' := RCle_trans ht (RCscale_mono (by decide : (0 : Q') ≤ HalfPow.half^2)
        (partial_norm_bound x n))
      rw [RCscale_RCscale, scale_congr (by decide : (HalfPow.half^2*4).eqv 1), RCscale_one] at ht'
      have h := RCle_trans (norm_add_bound (center x) (completedTime 2 (partialSum x n)))
        (RCadd_le_add (RCle_refl _) (RCadd_le_add ht' ht'))
      rw [four_copies] at h
      exact h

/-- The exact tail is a translated geometric sum of the same centered source. -/
theorem partial_tail (x : Completion) (n k : Nat) :
    completedSub (partialSum x (n+k)) (partialSum x n) = partialSum (completedTime (2*n) x) k := by
  rw [partial_split, sub_add_left_cancel, partial_time]

theorem partial_tail_bound (x : Completion) (n k : Nat) :
    RCle (completedDist (partialSum x (n+k)) (partialSum x n))
      (RCscale 4 (completedDist (completedTime (2*n) x) (unitProjection x))) := by
  unfold completedDist
  rw [partial_tail, relaxation_difference, completedTime_center]
  exact partial_norm_bound (completedTime (2*n) x) k

/-- Original Cauchy data for every finite series, not chosen quotient representatives. -/
def partialCauchy (X : (D).Cauchy) : Nat → (D).Cauchy
  | 0 => (D).constant zeroPresentation
  | n+1 => addition.mapCauchy (centerCauchy X) (timeCauchy 2 (partialCauchy X n))

theorem partialCauchy_pin (X : (D).Cauchy) : ∀ n,
    Quotient.mk (D).completionSetoid (partialCauchy X n) = partialSum (Quotient.mk (D).completionSetoid X) n
  | 0 => rfl
  | n+1 => by
      change completedAdd (center (Quotient.mk (D).completionSetoid X))
        (completedTime 2 (Quotient.mk (D).completionSetoid (partialCauchy X n))) = _
      rw [partialCauchy_pin]
      rfl

def seriesModulus (X : (D).Cauchy) (epsilon : Q') : Nat := relaxationModulus X (quarter epsilon)

theorem four_quarter_scale (epsilon : Q') :
    RCscale 4 (Quotient.mk crealSetoid (ofQ' (quarter epsilon))) =
      Quotient.mk crealSetoid (ofQ' epsilon) := by
  rw [← four_copies]
  exact Quotient.sound (ofQ'_equiv_of_eqv (Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (ExpNeg.two_halves (HalfPow.half*epsilon)) (ExpNeg.two_halves (HalfPow.half*epsilon)))
    (ExpNeg.two_halves epsilon)))

theorem partial_tail_small (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n k : Nat) (hn : seriesModulus X epsilon ≤ n) :
    RCle (completedDist (partialSum (Quotient.mk (D).completionSetoid X) (n+k))
      (partialSum (Quotient.mk (D).completionSetoid X) n)) (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  have ht := relaxation_small X (quarter epsilon) (quarter_pos he) (2*n) (by
    exact Nat.le_trans hn (by omega))
  have h := RCle_trans (partial_tail_bound _ n k) (RCscale_mono (by decide : (0 : Q') ≤ 4) ht)
  rw [four_quarter_scale] at h
  exact h

def seriesRows (X : (D).Cauchy) : CauchyRows where
  row := partialCauchy X
  modulus := seriesModulus X
  isCauchy := by
    intro epsilon he m n hm hn
    rw [partialCauchy_pin, partialCauchy_pin]
    by_cases hmn : m ≤ n
    · rw [completedDist_symm, show n = m+(n-m) by omega]
      exact partial_tail_small X epsilon he m (n-m) hm
    · rw [show m = n+(m-n) by omega]
      exact partial_tail_small X epsilon he n (m-n) hn

theorem seriesRows_point (X : (D).Cauchy) (n : Nat) :
    rowPoint (seriesRows X) n = partialSum (Quotient.mk (D).completionSetoid X) n := partialCauchy_pin X n

end YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial.scale_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial.four_copies
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial.sub_add_right_cancel
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial.sub_add_left_cancel
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial.norm_add_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial.partialSum
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial.partial_centered
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial.partial_time
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial.partial_split
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial.partial_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial.partial_tail
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial.partial_tail_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial.partialCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial.partialCauchy_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial.seriesModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial.four_quarter_scale
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial.partial_tail_small
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial.seriesRows
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial.seriesRows_point
