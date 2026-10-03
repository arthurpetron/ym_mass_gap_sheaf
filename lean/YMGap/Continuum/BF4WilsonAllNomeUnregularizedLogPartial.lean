/-
# Literal finite logarithm on the original Wilson completion

The finite sum below acts on the supplied vector itself, without the time-one
regularizing factor in `LogPartial`. On an actual time-one input it is exactly
that existing polynomial. Its computed finite Lipschitz cost is sufficient to
transport graph approximations at each fixed cutoff. No infinite series on the
ambient completion, generator identification, or continuum claim is made here.
-/

import YMGap.Continuum.BF4WilsonAllNomeLogPartial
import YMGap.Continuum.BF4WilsonAllNomeDefectContraction
import YMGap.Continuum.BF4WilsonAllNomeTimeAverages

namespace YMGap.Continuum.BF4WilsonAllNomeUnregularizedLogPartial

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
open YMGap.Continuum.BF4WilsonAllNomeDefectPolynomial (defect_pair_bound)
open YMGap.Continuum.BF4WilsonAllNomeDefectContraction (defectPower_sub)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeTail (positiveTimeTail)
open YMGap.Continuum.BF4WilsonAllNomeLogPartial
  (logTerm logTail logPartial logPartial_add_tail)
open YMGap.Continuum.BF4WilsonAllNomeTimeAverages
  (vectorSum sum_sub sum_norm_bound smul_sub)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "DP" => defectPower hw0 hw1
local notation "dist" => completedDist hw0 hw1

/-- The literal sum `sum (j<n), D^(j+1)x/(j+1)` on the SAME completion.
There is no inverse transfer or changed carrier in this definition. -/
def unregularizedLogPartial (n : Nat) (x : V) : V :=
  vectorSum hw0 hw1 n (fun j => S (Q'.invSucc j) (DP (j+1) x))

/-- The original regularized finite logarithm is this literal finite sum
applied to the actual time-one vector. -/
theorem unregularizedLogPartial_time (n : Nat) (x : V) :
    unregularizedLogPartial hw0 hw1 n (T 1 x) = logPartial hw0 hw1 n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change A (unregularizedLogPartial hw0 hw1 n (T 1 x))
        (S (Q'.invSucc n) (DP (n+1) (T 1 x))) =
        logPartial hw0 hw1 (n+1) x
      rw [ih]
      have h := logPartial_add_tail hw0 hw1 x n 1
      simpa only [logTail, logTerm, positiveTimeTail, completedAdd_zero] using h.symm

/-- Finite logarithms preserve subtraction on the original completion. -/
theorem unregularizedLogPartial_sub (n : Nat) (x y : V) :
    unregularizedLogPartial hw0 hw1 n (Sub x y) =
      Sub (unregularizedLogPartial hw0 hw1 n x)
        (unregularizedLogPartial hw0 hw1 n y) := by
  unfold unregularizedLogPartial
  rw [← sum_sub]
  apply congrArg (vectorSum hw0 hw1 n)
  funext j
  rw [defectPower_sub, smul_sub]

private theorem term_norm_bound (j : Nat) (x : V) :
    RCle (B (S (Q'.invSucc j) (DP (j+1) x))
      (S (Q'.invSucc j) (DP (j+1) x))) (B x x) := by
  rw [completedInner_smul_left, completedInner_smul_right, RCscale_RCscale]
  have hc : Q'.invSucc j ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le (Nat.zero_le j)) (by decide)
  have hcc : Q'.invSucc j * Q'.invSucc j ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hc (Q'.invSucc_nonneg j))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _)) hc)
  have h := RCle_trans
    (RCscale_mono (Q'.mul_nonneg _ _ (Q'.invSucc_nonneg j)
      (Q'.invSucc_nonneg j)) (defect_pair_bound hw0 hw1 x (j+1) (j+1)))
    (RCscale_scalar_mono hcc (completedInner_nonnegative hw0 hw1 x))
  simpa only [RCscale_one] using h

/-- A deliberately loose computed finite norm bound, valid also at cutoff zero.
It is a continuity cost, not a bound on an infinite ambient logarithm. -/
theorem unregularizedLogPartial_norm_bound (n : Nat) (x : V) :
    RCle (B (unregularizedLogPartial hw0 hw1 n x)
      (unregularizedLogPartial hw0 hw1 n x))
      (RCscale (Q'.ofNat n * Q'.ofNat n) (B x x)) := by
  exact sum_norm_bound hw0 hw1 n
    (fun j => S (Q'.invSucc j) (DP (j+1) x)) (B x x)
    (fun j _ => term_norm_bound hw0 hw1 j x)

/-- Fixed-cutoff continuity uses only the two original inputs. In particular
it requires no norm bound on any preimage in a derivative graph approximation. -/
theorem unregularizedLogPartial_distance_bound (n : Nat) (x y : V) :
    RCle (dist (unregularizedLogPartial hw0 hw1 n x)
      (unregularizedLogPartial hw0 hw1 n y))
      (RCscale (Q'.ofNat n * Q'.ofNat n) (dist x y)) := by
  unfold completedDist
  rw [← unregularizedLogPartial_sub]
  exact unregularizedLogPartial_norm_bound hw0 hw1 n (Sub x y)

#print axioms unregularizedLogPartial
#print axioms unregularizedLogPartial_time
#print axioms unregularizedLogPartial_sub
#print axioms unregularizedLogPartial_norm_bound
#print axioms unregularizedLogPartial_distance_bound

end YMGap.Continuum.BF4WilsonAllNomeUnregularizedLogPartial
