/-
Computed primitives of finite u/h monomial rows.  The output is an actual
finite row with nonnegative weights when the input weights are nonnegative.
Its expanded coefficient polynomial has exactly the original derivative and
zero initial value.  No analytic integration or assumed sign is used.
-/

import YMGap.Constructive.QPolyUHRow
import YMGap.Constructive.QPolyPositivePrimitive

namespace YMGap.Constructive.QPolyUHRowPrimitive

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyPositivePrimitive
open YMGap.Constructive.QPolyUHRow
open YMGap.Constructive.QPolyCoefficientEvaluation

/-- The positive primitive as literal u/h row data, with the SAME recursion as
the existing rational polynomial primitive. -/
def primitiveRow : Nat → Nat → Row
  | 0, b => scale (Q'.invSucc b) (singleton 0 (b + 1))
  | a + 1, b =>
      scale (Q'.invSucc b) (singleton (a + 1) (b + 1)) ++
        scale (Q'.ofNat (a + 1) * Q'.invSucc b) (primitiveRow a (b + 1))

/-- The row expands to the ACTUAL existing computed primitive, coefficientwise. -/
theorem polynomial_primitiveRow (a b : Nat) :
    CoeffEqv (polynomial (primitiveRow a b)) (primitive a b) := by
  induction a generalizing b with
  | zero =>
      exact (polynomial_scale _ _).trans
        (((polynomial_singleton 0 (b + 1)).trans
          (coeffEqv_pmul_one_left (polynomialPower coordinate (b + 1)))).pscale _)
  | succ a ih =>
      exact (polynomial_append _ _).trans
        (CoeffEqv.padd
          ((polynomial_scale _ _).trans
            ((polynomial_singleton (a + 1) (b + 1)).pscale _))
          ((polynomial_scale _ _).trans ((ih (b + 1)).pscale _)))

/-- Every primitive row has nonnegative computed weights. -/
theorem nonnegative_primitiveRow (a b : Nat) : nonnegative (primitiveRow a b) := by
  induction a generalizing b with
  | zero =>
      exact nonnegative_scale _ (Q'.invSucc_nonneg b) _
        (nonnegative_singleton 0 (b + 1))
  | succ a ih =>
      exact nonnegative_append _ _
        (nonnegative_scale _ (Q'.invSucc_nonneg b) _
          (nonnegative_singleton (a + 1) (b + 1)))
        (nonnegative_scale _
          (Q'.mul_nonneg _ _ (Q'.le_of_lt (Q'.ofNat_succ_pos a))
            (Q'.invSucc_nonneg b)) _ (ih (b + 1)))

/-- Termwise finite primitive row; signed input weights remain literal. -/
def integralRow : Row → Row
  | [] => []
  | t :: r => scale t.weight (primitiveRow t.uDegree t.hDegree) ++ integralRow r

/-- The derivative of the computed row polynomial is exactly the INPUT row
polynomial, with no nonnegative-weight hypothesis required for this identity. -/
theorem integralRow_derivative (r : Row) :
    CoeffEqv (pderiv (polynomial (integralRow r))) (polynomial r) := by
  induction r with
  | nil => exact CoeffEqv.refl []
  | cons t r ih =>
      have ht : CoeffEqv
          (pderiv (polynomial (scale t.weight (primitiveRow t.uDegree t.hDegree))))
          (pscale t.weight (monomial t.uDegree t.hDegree)) :=
        (polynomial_scale _ _).pderiv.trans
          ((pderiv_pscale _ _).trans
            (((polynomial_primitiveRow _ _).pderiv.trans
              (primitive_derivative _ _)).pscale _))
      exact (polynomial_append _ _).pderiv.trans
        ((pderiv_padd _ _).trans (CoeffEqv.padd ht ih))

private theorem primitiveRow_zero (a b : Nat) :
    (eval (polynomial (primitiveRow a b)) 0).eqv 0 :=
  Q'.eqv_trans _ _ _ (coefficient_eval (polynomial_primitiveRow a b) 0)
    (primitive_zero a b)

/-- The actual termwise primitive has zero initial value for every finite row. -/
theorem integralRow_zero (r : Row) : (eval (polynomial (integralRow r)) 0).eqv 0 := by
  induction r with
  | nil => exact Q'.eqv_refl 0
  | cons t r ih =>
      have ht : (eval (polynomial (scale t.weight
          (primitiveRow t.uDegree t.hDegree))) 0).eqv 0 :=
        Q'.eqv_trans _ _ _ (coefficient_eval (polynomial_scale _ _) 0)
          (Q'.eqv_trans _ _ _ (eval_pscale _ _ 0)
            (Q'.eqv_trans _ _ _
              (Q'.mul_eqv_congr_left _ _ 0 (primitiveRow_zero _ _))
              (q_mul_zero _)))
      exact Q'.eqv_trans _ _ _ (coefficient_eval (polynomial_append _ _) 0)
        (Q'.eqv_trans _ _ _ (eval_padd _ _ 0)
          (Q'.eqv_trans _ _ _ (q_add_congr ht ih) (q_add_zero_eqv 0)))

/-- Nonnegative input weights give nonnegative OUTPUT weights, as actual row
data rather than a pointwise positivity assumption. -/
theorem nonnegative_integralRow (r : Row) (hr : nonnegative r) :
    nonnegative (integralRow r) := by
  induction r with
  | nil => exact True.intro
  | cons t r ih =>
      exact nonnegative_append _ _
        (nonnegative_scale _ hr.1 _ (nonnegative_primitiveRow _ _)) (ih hr.2)

end YMGap.Constructive.QPolyUHRowPrimitive

#print axioms YMGap.Constructive.QPolyUHRowPrimitive.primitiveRow
#print axioms YMGap.Constructive.QPolyUHRowPrimitive.polynomial_primitiveRow
#print axioms YMGap.Constructive.QPolyUHRowPrimitive.nonnegative_primitiveRow
#print axioms YMGap.Constructive.QPolyUHRowPrimitive.integralRow
#print axioms YMGap.Constructive.QPolyUHRowPrimitive.integralRow_derivative
#print axioms YMGap.Constructive.QPolyUHRowPrimitive.integralRow_zero
#print axioms YMGap.Constructive.QPolyUHRowPrimitive.nonnegative_integralRow
