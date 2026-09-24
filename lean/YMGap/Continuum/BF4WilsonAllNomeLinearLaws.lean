/-
# Rational linear laws on the SAME all-nome Wilson completion

The explicit-modulus operations obey the rational vector laws on the actual
Cauchy quotient. Dense expressions need not have equal radii or syntax:
equality of their reflected pairings proves zero distance, with an explicit
closeness witness. No representative choice or different carrier is used.
This is rational algebra, not a claim of full real Hilbert/QFT structure.
-/

import YMGap.Continuum.BF4WilsonAllNomeLinear

namespace YMGap.Continuum.BF4WilsonAllNomeLinearLaws

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm (sum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra (smul zero)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm (intrinsicForm)
open YMGap.Continuum.BF4WilsonAllNomeFormLaws
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion)
open YMGap.Continuum.BF4WilsonAllNomeLinear

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "F" => intrinsicForm hw0 hw1
local notation "V" => Completion hw0 hw1 width
local notation "A" => completedAdd hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "Z" => completedZero hw0 hw1 width

theorem completedAdd_assoc (x y z : V) : A (A x y) z = A x (A y z) := by
  refine Quotient.inductionOn₃ x y z ?_
  intro X Y Z'
  apply completion_eq_of_pointwise hw0 hw1
  intro n t
  have hl := (intrinsicForm_sum_left hw0 hw1 (sum (X.seq n) (Y.seq n)) (Z'.seq n) t).trans
    (Equiv_add (intrinsicForm_sum_left hw0 hw1 (X.seq n) (Y.seq n) t) (Equiv.refl _))
  have hr := (intrinsicForm_sum_left hw0 hw1 (X.seq n) (sum (Y.seq n) (Z'.seq n)) t).trans
    (Equiv_add (Equiv.refl _) (intrinsicForm_sum_left hw0 hw1 (Y.seq n) (Z'.seq n) t))
  exact hl.trans ((SumOfSquares.Equiv_of_approx_eqv (fun k =>
    Q'.add_assoc_eqv ((F (X.seq n) t).approx k) ((F (Y.seq n) t).approx k)
      ((F (Z'.seq n) t).approx k))).trans hr.symm)

theorem completedAdd_comm (x y : V) : A x y = A y x := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  apply completion_eq_of_pointwise hw0 hw1
  intro n t
  exact (intrinsicForm_sum_left hw0 hw1 (X.seq n) (Y.seq n) t).trans
    ((SumOfSquares.Equiv_of_approx_eqv (fun k =>
      Q'.add_comm_eqv ((F (X.seq n) t).approx k) ((F (Y.seq n) t).approx k))).trans
      (intrinsicForm_sum_left hw0 hw1 (Y.seq n) (X.seq n) t).symm)

theorem completedZero_add (x : V) : A Z x = x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply completion_eq_of_pointwise hw0 hw1
  intro n t
  exact (intrinsicForm_sum_left hw0 hw1 (zero width) (X.seq n) t).trans
    ((Equiv_add (intrinsicForm_zero_left hw0 hw1 t) (Equiv.refl _)).trans
      (SumOfSquares.Equiv_of_approx_eqv (fun k =>
        by
          change ((0 : Q') + (F (X.seq n) t).approx k).eqv ((F (X.seq n) t).approx k)
          rw [Q'.zero_add']
          exact Q'.eqv_refl _)))

theorem completedAdd_zero (x : V) : A x Z = x :=
  (completedAdd_comm hw0 hw1 x Z).trans (completedZero_add hw0 hw1 x)

theorem completedNeg_add (x : V) : A (completedNeg hw0 hw1 x) x = Z := by
  refine Quotient.inductionOn x ?_
  intro X
  apply completion_eq_of_pointwise hw0 hw1
  intro n t
  refine (intrinsicForm_sum_left hw0 hw1 (smul (-1) (X.seq n)) (X.seq n) t).trans ?_
  refine (Equiv_add (intrinsicForm_smul_left hw0 hw1 (-1) (X.seq n) t)
    (Equiv.refl _)).trans ?_
  refine Equiv.trans ?_ (intrinsicForm_zero_left hw0 hw1 t).symm
  apply SumOfSquares.Equiv_of_approx_eqv
  intro k
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.mul (.neg (.const 1)) (.var 0)) (.var 0)) (.const 0)
    (by decide) (fun _ => (F (X.seq n) t).approx k)

theorem completedSub_self (x : V) : completedSub hw0 hw1 x x = Z :=
  (completedAdd_comm hw0 hw1 x (completedNeg hw0 hw1 x)).trans
    (completedNeg_add hw0 hw1 x)

theorem completedSmul_one (x : V) : S 1 x = x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply completion_eq_of_pointwise hw0 hw1
  intro n t
  exact (intrinsicForm_smul_left hw0 hw1 1 (X.seq n) t).trans
    (SumOfSquares.Equiv_of_approx_eqv (fun k =>
      Q'.one_mul_eqv ((F (X.seq n) t).approx k)))

theorem completedSmul_zero (x : V) : S 0 x = Z := by
  refine Quotient.inductionOn x ?_
  intro X
  apply completion_eq_of_pointwise hw0 hw1
  intro n t
  exact (intrinsicForm_smul_left hw0 hw1 0 (X.seq n) t).trans
    ((SumOfSquares.Equiv_of_approx_eqv (fun k =>
      Q'.zero_mul_eqv ((F (X.seq n) t).approx k))).trans
      (intrinsicForm_zero_left hw0 hw1 t).symm)

theorem completedSmul_mul (a b : Q') (x : V) : S a (S b x) = S (a*b) x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply completion_eq_of_pointwise hw0 hw1
  intro n t
  refine (intrinsicForm_smul_left hw0 hw1 a (smul b (X.seq n)) t).trans ?_
  refine (Pivot2.mul_congr_right (intrinsicForm_smul_left hw0 hw1 b (X.seq n) t)).trans ?_
  exact (SumOfSquares.Equiv_of_approx_eqv (fun k =>
    Q'.eqv_symm (Q'.mul_assoc_eqv a b ((F (X.seq n) t).approx k)))).trans
    (intrinsicForm_smul_left hw0 hw1 (a*b) (X.seq n) t).symm

theorem completedSmul_add (c : Q') (x y : V) : S c (A x y) = A (S c x) (S c y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  apply completion_eq_of_pointwise hw0 hw1
  intro n t
  have hl := (intrinsicForm_smul_left hw0 hw1 c (sum (X.seq n) (Y.seq n)) t).trans
    (Pivot2.mul_congr_right (intrinsicForm_sum_left hw0 hw1 (X.seq n) (Y.seq n) t))
  have hr := (intrinsicForm_sum_left hw0 hw1 (smul c (X.seq n)) (smul c (Y.seq n)) t).trans
    (Equiv_add (intrinsicForm_smul_left hw0 hw1 c (X.seq n) t)
      (intrinsicForm_smul_left hw0 hw1 c (Y.seq n) t))
  exact hl.trans ((SumOfSquares.Equiv_of_approx_eqv (fun k =>
    Q'.mul_add_eqv c ((F (X.seq n) t).approx k) ((F (Y.seq n) t).approx k))).trans hr.symm)

theorem completedAdd_smul (a b : Q') (x : V) : A (S a x) (S b x) = S (a+b) x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply completion_eq_of_pointwise hw0 hw1
  intro n t
  refine (intrinsicForm_sum_left hw0 hw1 (smul a (X.seq n)) (smul b (X.seq n)) t).trans ?_
  refine (Equiv_add (intrinsicForm_smul_left hw0 hw1 a (X.seq n) t)
    (intrinsicForm_smul_left hw0 hw1 b (X.seq n) t)).trans ?_
  exact (SumOfSquares.Equiv_of_approx_eqv (fun k =>
    Q'.eqv_symm (Q'.add_mul_eqv a b ((F (X.seq n) t).approx k)))).trans
    (intrinsicForm_smul_left hw0 hw1 (a+b) (X.seq n) t).symm

theorem completedSmul_congr {a b : Q'} (h : a.eqv b) (x : V) : S a x = S b x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply completion_eq_of_pointwise hw0 hw1
  intro n t
  exact (intrinsicForm_smul_left hw0 hw1 a (X.seq n) t).trans
    ((Pivot2.mul_congr_left (SumOfSquares.Equiv_of_approx_eqv (fun _ => h))).trans
      (intrinsicForm_smul_left hw0 hw1 b (X.seq n) t).symm)

#print axioms completedAdd_assoc
#print axioms completedAdd_comm
#print axioms completedZero_add
#print axioms completedAdd_zero
#print axioms completedNeg_add
#print axioms completedSub_self
#print axioms completedSmul_one
#print axioms completedSmul_zero
#print axioms completedSmul_mul
#print axioms completedSmul_add
#print axioms completedAdd_smul
#print axioms completedSmul_congr

end YMGap.Continuum.BF4WilsonAllNomeLinearLaws
