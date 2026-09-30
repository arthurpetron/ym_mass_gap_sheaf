/-
Adjacent constructed inverse comparison on the SAME original Wilson carrier.
The exact inverse difference is D^2 applied to the two-inverse product.
The positive mixed-moment square bounds it independently of the positive
shift. No spectral calculus, new carrier, or removal of the boundary kernel.
This is an input to dyadic resolvent convergence, not physical mass control.
-/

import YMGap.Continuum.BF4WilsonAllNomeShiftedRootResolvent
import YMGap.Continuum.BF4WilsonAllNomeResolventSquareComparison

namespace YMGap.Continuum.BF4WilsonAllNomeAdjacentRootResolvent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
  (completedInner_sub_left)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics
open YMGap.Continuum.BF4WilsonAllNomeNestedRootCompatibility
open YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay
  (mesh_generator_commutes defectPower)
open YMGap.Continuum.BF4WilsonAllNomeShiftedRootResolvent
open YMGap.Continuum.BF4WilsonAllNomeResolventSquareComparison
open YMGap.Continuum.RCSignedPairBudget (scale_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "R" => root hw0 hw1
local notation "F" => denominator hw0 hw1
local notation "J" => inverse hw0 hw1
local notation "DP" => defectPower hw0 hw1

theorem denominator_root_commute (depth mesh : Nat) (delta b : Q') (x : V) :
    F depth delta b (R mesh x) = R mesh (F depth delta b x) := by
  have hc : R depth (R mesh x) = R mesh (R depth x) :=
    mesh_generator_commutes hw0 hw1 depth 1 mesh x
  unfold denominator
  rw [root_sub, root_smul, root_smul, hc]

theorem inverse_root_commute (depth mesh : Nat) (delta b : Q')
    (hd : (0 : Q') < delta) (hb : (0 : Q') ≤ b) (x : V) :
    J depth delta b hd hb (R mesh x) = R mesh (J depth delta b hd hb x) :=
  inverse_commutes hw0 hw1 depth delta b hd hb (R mesh)
    (denominator_root_commute hw0 hw1 depth mesh delta b) x

theorem inverse_denominator_commute (depth mesh : Nat) (delta b eta c : Q')
    (hd : (0 : Q') < delta) (hb : (0 : Q') ≤ b) (x : V) :
    J depth delta b hd hb (F mesh eta c x) =
      F mesh eta c (J depth delta b hd hb x) := by
  unfold denominator
  rw [inverse_sub, inverse_smul, inverse_smul, inverse_root_commute]

private theorem denominator_product_pin (depth : Nat) (alpha : Q') (z : V) :
    denominatorProduct hw0 hw1 (depth+1) alpha z =
      F depth alpha 1 (F (depth+1) alpha 2 z) := by
  rw [denominatorProduct_pin]
  unfold literalProduct denominator
  rw [completedSmul_one,
    completedSmul_congr hw0 hw1 (Q'.add_comm_eqv alpha 1),
    completedSmul_congr hw0 hw1 (Q'.add_comm_eqv alpha 2)]

/-- The exact difference of the two denominators is the fine-root defect square. -/
theorem denominator_difference (depth : Nat) (alpha : Q') (z : V) :
    Sub (F (depth+1) alpha 2 z) (F depth alpha 1 z) = DP (depth+1) 2 z := by
  apply completed_eq_of_pairings hw0 hw1
  intro y
  have hd : B (DP (depth+1) 2 z) y =
      RCsub (RCsub (B z y) (B (R (depth+1) z) y))
        (RCsub (B (R (depth+1) z) y) (B (R depth z) y)) := by
    change B (Sub (Sub z (R (depth+1) z))
      (R (depth+1) (Sub z (R (depth+1) z)))) y = _
    rw [root_sub, root_square]
    simp only [completedInner_sub_left]
  rw [hd]
  unfold denominator
  simp only [completedInner_sub_left, completedInner_smul_left]
  refine Quotient.inductionOn₃ (B z y) (B (R (depth+1) z) y) (B (R depth z) y) ?_
  intro X Y Z'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.mul (.add (.var 0) (.const 2)) (.var 1))
        (.neg (.mul (.const 2) (.var 2))))
        (.neg (.add (.mul (.add (.var 0) (.const 1)) (.var 1))
          (.neg (.mul (.const 1) (.var 3))))))
      (.add (.add (.var 1) (.neg (.var 2)))
        (.neg (.add (.var 2) (.neg (.var 3)))))
      (by decide)
      (fun | 0 => alpha | 1 => X.approx n | 2 => Y.approx n | _ => Z'.approx n)))

/-- Actual two-inverse product, with no supplied inverse or representative choice. -/
def inverseProduct (depth : Nat) (alpha : Q') (ha : (0 : Q') < alpha) (x : V) : V :=
  J depth alpha 1 ha (by decide) (J (depth+1) alpha 2 ha (by decide) x)

theorem inverseProduct_coarse (depth : Nat) (alpha : Q')
    (ha : (0 : Q') < alpha) (x : V) :
    F depth alpha 1 (inverseProduct hw0 hw1 depth alpha ha x) =
      J (depth+1) alpha 2 ha (by decide) x := by
  unfold inverseProduct
  rw [inverse_right]

theorem inverseProduct_fine (depth : Nat) (alpha : Q')
    (ha : (0 : Q') < alpha) (x : V) :
    F (depth+1) alpha 2 (inverseProduct hw0 hw1 depth alpha ha x) =
      J depth alpha 1 ha (by decide) x := by
  unfold inverseProduct
  rw [← inverse_denominator_commute, inverse_right]

theorem inverseProduct_pin (depth : Nat) (alpha : Q')
    (ha : (0 : Q') < alpha) (x : V) :
    denominatorProduct hw0 hw1 (depth+1) alpha
      (inverseProduct hw0 hw1 depth alpha ha x) = x := by
  rw [denominator_product_pin, inverseProduct_fine, inverse_right]

theorem inverse_difference (depth : Nat) (alpha : Q')
    (ha : (0 : Q') < alpha) (x : V) :
    Sub (J depth alpha 1 ha (by decide) x)
      (J (depth+1) alpha 2 ha (by decide) x) =
      DP (depth+1) 2 (inverseProduct hw0 hw1 depth alpha ha x) := by
  rw [← inverseProduct_fine hw0 hw1 depth alpha ha x,
    ← inverseProduct_coarse hw0 hw1 depth alpha ha x]
  exact denominator_difference hw0 hw1 depth alpha _

/-- Sharp estimate, with no dependence on the positive shift in the constant. -/
theorem inverse_difference_bound (depth : Nat) (alpha : Q')
    (ha : (0 : Q') < alpha) (x : V) :
    RCle (RCscale 4
      (B (Sub (J depth alpha 1 ha (by decide) x)
          (J (depth+1) alpha 2 ha (by decide) x))
        (Sub (J depth alpha 1 ha (by decide) x)
          (J (depth+1) alpha 2 ha (by decide) x)))) (B x x) := by
  rw [inverse_difference]
  have h := positive_square_comparison hw0 hw1 (depth+1) alpha (Q'.le_of_lt ha)
    (inverseProduct hw0 hw1 depth alpha ha x)
  rw [inverseProduct_pin] at h
  exact h

private theorem scale_one (a : RC) : RCscale 1 a = a := by
  refine Quotient.inductionOn a ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.one_mul_eqv (X.approx n)))

/-- The adjacent inverse comparison in the h-scaled form used by resolvents. -/
theorem scaled_difference_bound (depth : Nat) (alpha h : Q')
    (ha : (0 : Q') < alpha) (x : V) :
    RCle
      (B (Sub (S h (J depth alpha 1 ha (by decide) x))
          (S h (J (depth+1) alpha 2 ha (by decide) x)))
        (Sub (S h (J depth alpha 1 ha (by decide) x))
          (S h (J (depth+1) alpha 2 ha (by decide) x))))
      (RCscale (h*h*(HalfPow.half*HalfPow.half)) (B x x)) := by
  have hh : (0 : Q') ≤ HalfPow.half*HalfPow.half := by decide
  have hq := RCscale_mono hh (inverse_difference_bound hw0 hw1 depth alpha ha x)
  rw [RCscale_RCscale, scale_congr (by decide :
    Q'.eqv ((HalfPow.half*HalfPow.half)*4) 1), scale_one] at hq
  rw [← BF4WilsonAllNomeTimeAverages.smul_sub,
    completedInner_smul_left, completedInner_smul_right, RCscale_RCscale]
  have hs := RCscale_mono (SumOfSquares.q_mul_self_nonneg h) hq
  rw [RCscale_RCscale] at hs
  exact hs

#print axioms denominator_root_commute
#print axioms inverse_root_commute
#print axioms inverse_denominator_commute
#print axioms denominator_difference
#print axioms inverseProduct
#print axioms inverseProduct_coarse
#print axioms inverseProduct_fine
#print axioms inverseProduct_pin
#print axioms inverse_difference
#print axioms inverse_difference_bound
#print axioms scaled_difference_bound

end YMGap.Continuum.BF4WilsonAllNomeAdjacentRootResolvent
