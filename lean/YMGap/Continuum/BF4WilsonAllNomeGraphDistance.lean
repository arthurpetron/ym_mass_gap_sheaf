/-
# Elementary distance estimates on the all-nome Wilson completion

These are same-carrier consequences of the existing squared distance and
completed bilinear form.  They add no norm, scalar, or analytic hypotheses.
-/

import YMGap.Continuum.BF4WilsonAllNomeDistance
import YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity

namespace YMGap.Continuum.BF4WilsonAllNomeGraphDistance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "N" => completedNeg hw0 hw1
local notation "S" => completedSub hw0 hw1
local notation "d" => completedDist hw0 hw1

private theorem completedNeg_neg (x : V) : N (N x) = x := by
  unfold completedNeg
  rw [completedSmul_mul, show (-1 : Q') * (-1) = 1 by decide,
    completedSmul_one]

private theorem completedNeg_add_dist (x y : V) :
    N (A x y) = A (N x) (N y) := by
  unfold completedNeg
  exact completedSmul_add hw0 hw1 (-1) x y

private theorem completedSub_shared_right (x x' y : V) :
    S (S x y) (S x' y) = S x x' := by
  unfold completedSub
  rw [completedNeg_add_dist, completedNeg_neg]
  calc
    A (A x (N y)) (A (N x') y) = A x (A (N y) (A (N x') y)) := by
      rw [completedAdd_assoc]
    _ = A x (A (A (N y) (N x')) y) := by
      exact congrArg (A x) (completedAdd_assoc hw0 hw1 (N y) (N x') y).symm
    _ = A x (A (A (N x') (N y)) y) := by
      rw [completedAdd_comm hw0 hw1 (N y) (N x')]
    _ = A x (A (N x') (A (N y) y)) := by
      rw [completedAdd_assoc]
    _ = A x (A (N x') (completedZero hw0 hw1 width)) := by
      rw [completedNeg_add]
    _ = A x (N x') := by
      rw [completedAdd_zero]

private theorem completedSub_shared_left (x y z : V) :
    S (S x y) (S x z) = S z y := by
  unfold completedSub
  rw [completedNeg_add_dist, completedNeg_neg]
  calc
    A (A x (N y)) (A (N x) z) = A x (A (N y) (A (N x) z)) := by
      rw [completedAdd_assoc]
    _ = A x (A (A (N y) (N x)) z) := by
      exact congrArg (A x) (completedAdd_assoc hw0 hw1 (N y) (N x) z).symm
    _ = A x (A (A (N x) (N y)) z) := by
      rw [completedAdd_comm hw0 hw1 (N y) (N x)]
    _ = A x (A (N x) (A (N y) z)) := by
      rw [completedAdd_assoc]
    _ = A (A x (N x)) (A (N y) z) := by
      rw [← completedAdd_assoc]
    _ = A (completedZero hw0 hw1 width) (A (N y) z) := by
      rw [completedAdd_comm hw0 hw1 x (N x), completedNeg_add]
    _ = A (N y) z := by
      rw [completedZero_add]
    _ = A z (N y) := by
      rw [completedAdd_comm hw0 hw1]

/-- The distance from a vector to zero is its diagonal completed pairing. -/
theorem dist_zero_right (x : V) : d x (completedZero hw0 hw1 width) = B x x := by
  have hzero : N (completedZero hw0 hw1 width) = completedZero hw0 hw1 width := by
    have h := completedNeg_add hw0 hw1 (completedZero hw0 hw1 width)
    rw [completedAdd_zero] at h
    exact h
  unfold completedDist
  rw [show S x (completedZero hw0 hw1 width) = x by
    unfold completedSub
    rw [hzero, completedAdd_zero]]

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  exact fun A' => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_zero_add_eqv (A'.approx n)))

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun A' => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_add_zero_eqv (A'.approx n)))

private theorem rc_neg_zero : RCneg RCzero = RCzero :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun _ => (by decide : Q'.eqv (-(0 : Q')) 0)))

private theorem rc_sub_zero (a : RC) : RCsub a RCzero = a := by
  unfold RCsub
  rw [rc_neg_zero]
  rw [rc_add_zero]

private theorem rc_zero_sub (a : RC) : RCsub RCzero a = RCneg a := by
  unfold RCsub
  rw [rc_zero_add]

private theorem rc_neg_neg (a : RC) : RCneg (RCneg a) = a := by
  refine Quotient.inductionOn a ?_
  intro A'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.neg_neg_eqv (A'.approx n)))

private theorem rc_sub_neg (a b : RC) : RCsub a (RCneg b) = RCadd a b := by
  unfold RCsub
  rw [rc_neg_neg]

private theorem completedDist_orthogonal_eq (x y : V)
    (hxy : B x y = RCzero) :
    d x y = RCadd (B x x) (B y y) := by
  have hyx : B y x = RCzero := by
    rw [completedInner_symm hw0 hw1 y x, hxy]
  unfold completedDist
  rw [completedInner_sub_left hw0 hw1, completedInner_sub_right hw0 hw1,
    completedInner_sub_right hw0 hw1, hxy, hyx,
    rc_sub_zero, rc_zero_sub, rc_sub_neg]

/-- An orthogonal component's squared norm is bounded by the squared distance
to the other component. -/
theorem norm_le_dist_of_orthogonal (x y : V) (hxy : B x y = RCzero) :
    RCle (B x x) (d x y) := by
  rw [completedDist_orthogonal_eq hw0 hw1 x y hxy]
  have h := RCadd_le_add (RCle_refl (B x x))
    (completedInner_nonnegative hw0 hw1 y)
  rw [rc_add_zero] at h
  exact h

/-- Squared distance between two pairwise differences is controlled by the
two original squared distances, with the sharp two-term triangle constant. -/
theorem completedDist_sub_le (x x' y y' : V) :
    RCle (d (S x y) (S x' y'))
      (RCadd (RCadd (d x x') (d x x'))
        (RCadd (d y y') (d y y'))) := by
  have htri := completedDist_triangle hw0 hw1
    (S x y) (S x' y) (S x' y')
  have hleft : d (S x y) (S x' y) = d x x' := by
    unfold completedDist
    rw [completedSub_shared_right]
  have hright : d (S x' y) (S x' y') = d y' y := by
    unfold completedDist
    rw [completedSub_shared_left]
  rw [hleft, hright, completedDist_symm hw0 hw1 y' y] at htri
  exact htri

#print axioms dist_zero_right
#print axioms norm_le_dist_of_orthogonal
#print axioms completedDist_sub_le

end YMGap.Continuum.BF4WilsonAllNomeGraphDistance
