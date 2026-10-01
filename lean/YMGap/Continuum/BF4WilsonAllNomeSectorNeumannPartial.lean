/-
# Finite geometric iteration of the actual normalized vacuum inverse

All iterates retain original sector and vacuum-complement witnesses.
Convexity bounds their norms; contraction bounds their differences directly,
without selecting representatives or assuming a spectral decomposition.
The tail estimate is the quantitative input for the actual shifted inverse.
-/

import YMGap.Continuum.BF4WilsonAllNomeSectorVacuumInverse
import YMGap.Continuum.BF4WilsonAllNomeRootResolventPartial
import YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit

namespace YMGap.Continuum.BF4WilsonAllNomeSectorNeumannPartial

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar (completed_eq_of_pairings)
open YMGap.Continuum.BF4WilsonAllNomeSectorVacuumInverse
  (Centered val val_zero val_add val_smul contraction contraction_norm_bound
   contraction_dist_bound)
open YMGap.Continuum.RCSignedPairBudget (scale_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "C" => Centered hw0 hw1 (width := width)
local notation "v" => val hw0 hw1
local notation "B" => completedInner hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "L" => contraction hw0 hw1

/-- Exact squared-distance scaling for the affine iteration step. -/
theorem affine_dist (b : V) (q : Q') (x y : V) :
    dist (A b (S q x)) (A b (S q y)) = RCscale (q*q) (dist x y) := by
  have hs : Sub (A b (S q x)) (A b (S q y)) = S q (Sub x y) := by
    apply completed_eq_of_pairings hw0 hw1
    intro z
    simp only [completedInner_sub_left, completedInner_add_left, completedInner_smul_left]
    refine Quotient.inductionOn₃ (B b z) (B x z) (B y z) ?_
    intro a c d
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.mul (.var 3) (.var 1)))
          (.neg (.add (.var 0) (.mul (.var 3) (.var 2)))))
        (.mul (.var 3) (.add (.var 1) (.neg (.var 2))))
        (by decide) (fun | 0 => a.approx n | 1 => c.approx n | 2 => d.approx n | _ => q)))
  unfold completedDist
  rw [hs, completedInner_smul_left, completedInner_smul_right, RCscale_RCscale]

/-- Normalized original-sector Neumann partials. No range witness is dropped. -/
def neumannPartial (q : Q') (x : C) : Nat → C
  | 0 => BF4WilsonAllNomeSectorVacuumInverse.zero hw0 hw1
  | n+1 => BF4WilsonAllNomeSectorVacuumInverse.add hw0 hw1
      (BF4WilsonAllNomeSectorVacuumInverse.smul hw0 hw1 (1-q) x)
      (BF4WilsonAllNomeSectorVacuumInverse.smul hw0 hw1 q
        (L (neumannPartial q x n)))

theorem partial_succ (q : Q') (x : C) (n : Nat) :
    v (neumannPartial hw0 hw1 q x (n+1)) =
      A (S (1-q) (v x)) (S q (v (L (neumannPartial hw0 hw1 q x n)))) := rfl

/-- Every normalized neumannPartial is norm bounded by the SAME original input. -/
theorem partial_norm_bound (q : Q') (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (n : Nat) (x : C) :
    RCle (B (v (neumannPartial hw0 hw1 q x n)) (v (neumannPartial hw0 hw1 q x n)))
      (B (v x) (v x)) := by
  induction n with
  | zero =>
      rw [neumannPartial, val_zero, completedInner_zero_left]
      exact completedInner_nonnegative hw0 hw1 (v x)
  | succ n ih =>
      rw [partial_succ]
      have hc := BF4WilsonAllNomeRootResolventPartial.convex_norm_le hw0 hw1
        q hq0 (Q'.le_of_lt hq1) (v x) (v (L (neumannPartial hw0 hw1 q x n)))
      have hl := RCle_trans (contraction_norm_bound hw0 hw1 _) ih
      have h := RCle_trans hc (RCadd_le_add (RCle_refl _) (RCscale_mono hq0 hl))
      have hp : Q'.eqv ((1-q)+q) 1 :=
        poly_identity_of_normal_eq
          (.add (.add (.const 1) (.neg (.var 0))) (.var 0)) (.const 1)
          (by decide) (fun _ => q)
      have heq : RCadd (RCscale (1-q) (B (v x) (v x)))
          (RCscale q (B (v x) (v x))) = B (v x) (v x) := by
        rw [← completedInner_smul_right, ← completedInner_smul_right,
          ← completedInner_add_right, completedAdd_smul,
          completedSmul_congr hw0 hw1 hp, completedSmul_one]
      rwa [heq] at h

/-- The affine step contracts squared distance by q squared. -/
theorem partial_step_bound (q : Q') (x : C) (m n : Nat) :
    RCle (dist (v (neumannPartial hw0 hw1 q x (m+1))) (v (neumannPartial hw0 hw1 q x (n+1))))
      (RCscale (q*q) (dist (v (neumannPartial hw0 hw1 q x m))
        (v (neumannPartial hw0 hw1 q x n)))) := by
  rw [partial_succ, partial_succ, affine_dist]
  exact RCscale_mono (SumOfSquares.q_mul_self_nonneg q)
    (contraction_dist_bound hw0 hw1 _ _)

/-- Uniform tail over EVERY later finite neumannPartial, with the original norm. -/
theorem partial_tail_bound (q : Q') (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (n k : Nat) (x : C) :
    RCle (dist (v (neumannPartial hw0 hw1 q x (n+k))) (v (neumannPartial hw0 hw1 q x n)))
      (RCscale (q^n*q^n) (B (v x) (v x))) := by
  induction n with
  | zero =>
      rw [Nat.zero_add, neumannPartial, val_zero,
        BF4WilsonAllNomeRowPairingLimit.dist_zero, Q'.pow_zero]
      rw [scale_congr (by decide : Q'.eqv ((1 : Q')*1) 1), RCscale_one]
      exact partial_norm_bound hw0 hw1 q hq0 hq1 k x
  | succ n ih =>
      rw [show n+1+k = (n+k)+1 by omega]
      have h := RCle_trans (partial_step_bound hw0 hw1 q x (n+k) n)
        (RCscale_mono (SumOfSquares.q_mul_self_nonneg q) ih)
      rw [RCscale_RCscale] at h
      have hp : Q'.eqv ((q*q)*(q^n*q^n)) (q^(n+1)*q^(n+1)) := by
        rw [Q'.pow_succ]
        exact poly_identity_of_normal_eq
          (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
          (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
          (by decide) (fun | 0 => q | _ => q^n)
      rwa [scale_congr hp] at h

#print axioms affine_dist
#print axioms neumannPartial
#print axioms partial_norm_bound
#print axioms partial_step_bound
#print axioms partial_tail_bound

end YMGap.Continuum.BF4WilsonAllNomeSectorNeumannPartial
