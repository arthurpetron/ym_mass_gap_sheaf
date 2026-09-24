/-
# Fixed-parameter geometry of the literal all-nome Wilson completion

The existing squared distance is definite relative to the embedded literal
zero.  This is a same-carrier statement at fixed nome and width.  The final
fixed-point corollary uses the existing completed two-step estimate; it is
not a vacuum-isolation, physical-mass, or continuum claim.
-/

import YMGap.Continuum.BF4WilsonAllNomeCompletedGap
import YMGap.Continuum.CRealSeminormPairingPosdef

namespace YMGap.Continuum.BF4WilsonAllNomeGeometry

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra (zero)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm (intrinsicForm)
open YMGap.Continuum.BF4WilsonAllNomeFormLaws
  (intrinsicForm_difference_diagonal intrinsicForm_zero_left
    intrinsicForm_zero_right)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedGap
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap
  (twoStepRate twoStepRate_lt_one)
open YMGap.Continuum.CRealSeminormPairingCompletion
  (completedInner_posdef scalar_contraction_zero)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat)

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "U" => unitState hw0 hw1 width

/-- The literal all-nome squared distance to the algebraic zero is the
existing diagonal form, before passing to the completed quotient. -/
theorem distSq_zero (x : IntrinsicExpression width) :
    Equiv (YMGap.Continuum.BF4WilsonAllNomeSeminorm.distSq hw0 hw1 x (zero width))
      (intrinsicForm hw0 hw1 x x) := by
  have h := intrinsicForm_difference_diagonal hw0 hw1 x (zero width)
  have hclean : Equiv
      (sub (sub (intrinsicForm hw0 hw1 x x)
        (intrinsicForm hw0 hw1 x (zero width)))
        (sub (intrinsicForm hw0 hw1 (zero width) x)
          (intrinsicForm hw0 hw1 (zero width) (zero width))))
      (sub (sub (intrinsicForm hw0 hw1 x x) czero)
        (sub czero czero)) :=
    Equiv_add
      (Equiv_add (Equiv.refl _)
        (neg_congr (intrinsicForm_zero_right hw0 hw1 x)))
      (neg_congr (Equiv_add
        (intrinsicForm_zero_left hw0 hw1 x)
        (neg_congr (intrinsicForm_zero_right hw0 hw1 (zero width)))))
  refine h.trans (hclean.trans ?_)
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.const 0)))
      (.neg (.add (.const 0) (.neg (.const 0)))))
    (.var 0) (by decide) (fun _ => (intrinsicForm hw0 hw1 x x).approx n)

/-- Zero completed norm is exactly the embedded literal zero. -/
theorem completedInner_posdef (x : V) :
    B x x = RCzero ↔ x = embed hw0 hw1 (zero width) := by
  exact CRealSeminormPairingCompletion.completedInner_posdef
    (pairingData hw0 hw1 (width := width)) (zero width)
    (fun y => distSq_zero hw0 hw1 width y)
    (intrinsicForm_zero_right hw0 hw1 (zero width)) x

/-- A fixed vector in the orthogonal complement cannot be fixed by the
two-step completed physical-time map, at this fixed nome and width. -/
theorem vacuumComplement_twoStep_fixed_eq_zero
    (x : VacuumComplement hw0 hw1 (width := width))
    (hfixed : T 2 x.val = x.val) :
    x.val = embed hw0 hw1 (zero width) := by
  have hgap := completed_twoStep_form_gap hw0 hw1 width x.val
    ((completedInner_symm hw0 hw1 x.val U).trans x.property)
  rw [hfixed] at hgap
  have hzero : B x.val x.val = RCzero :=
    scalar_contraction_zero (twoStepRate hw0 hw1 width)
      (twoStepRate_lt_one hw0 hw1 width) (B x.val x.val)
      (completedInner_nonnegative hw0 hw1 x.val) hgap
  exact (completedInner_posdef hw0 hw1 width x.val).mp hzero

#print axioms distSq_zero
#print axioms completedInner_posdef
#print axioms vacuumComplement_twoStep_fixed_eq_zero

end YMGap.Continuum.BF4WilsonAllNomeGeometry
