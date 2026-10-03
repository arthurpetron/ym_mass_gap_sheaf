/-
# Signed finite-polynomial Taylor cell bound

The remainder is bounded by a computed absolute coefficient budget on every
rational cell of [0,1]. The proof uses exact power differences and monomial
primitive rectangles, not an analytic derivative or a derivative-sign input.
This finite estimate is intended for the Laurent endpoint-order construction;
it does not assert that construction or a conditional heat variance bound.
-/

import YMGap.Continuum.RationalPolynomialIntervalOrder

namespace YMGap.Continuum.RationalPolynomialTaylorCell

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.SemicircleAtanEndpointMonomialRiemann
open YMGap.Continuum.RationalPolynomialIntervalOrder

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (a : Q') : (-a).num = -a.num := rfl
private theorem zero_num : (0 : Q').num = 0 := rfl
private theorem zero_den : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num : (1 : Q').num = 1 := rfl
private theorem one_den : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast, zero_num, zero_den, one_num, one_den,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

/-- A literal finite coefficient budget for a primitive starting at degree k. -/
def primitiveCellBudget : Nat → Poly → Q'
  | _, [] => 0
  | k, c::cs => Q'.abs c * Q'.ofNat k + primitiveCellBudget (k+1) cs

theorem primitiveCellBudget_nonnegative : ∀ k p,
    (0 : Q') ≤ primitiveCellBudget k p
  | _, [] => Q'.le_refl' _
  | k, c::cs => Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (Q'.abs_nonneg c) (zero_le_ofNat k))
      (primitiveCellBudget_nonnegative (k+1) cs)

/-- The unit-interval power difference has an explicit degree-Lipschitz bound. -/
theorem power_cell_difference_le (k : Nat) (x y : Q')
    (hx : (0 : Q') ≤ x) (hxy : x ≤ y) (hy : y ≤ (1 : Q')) :
    qpow y k + -qpow x k ≤ (y + -x) * Q'.ofNat k := by
  cases k with
  | zero =>
      change (1 : Q') + -1 ≤ (y + -x) * 0
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_neg_self_eqv 1))
        (Q'.ge_of_eqv (Q'.mul_zero_eqv _))
  | succ k =>
      have hy0 : (0 : Q') ≤ y := Q'.le_trans' _ _ _ hx hxy
      have hco : mixedPowSum x y k ≤ Q'.ofNat (k+1) := by
        exact Q'.le_trans' _ _ _ (mixedPowSum_upper hx hxy k)
          (Q'.le_trans' _ _ _
            (Q'.mul_le_mul_of_nonneg_left _ _ _ (qpow_le_one hy0 hy k)
              (zero_le_ofNat (k+1)))
            (Q'.le_of_eqv (Q'.mul_one_eqv _)))
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (mixedPowSum_factor x y k))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hco (Q'.sub_nonneg_of_le hxy))

/-- Exact monomial primitive minus its left rectangle costs at most k*mesh². -/
theorem monomial_cell_error (k : Nat) (x y : Q')
    (hx : (0 : Q') ≤ x) (hxy : x ≤ y) (hy : y ≤ (1 : Q')) :
    Q'.abs (monomialIncrement x y k + -((y + -x) * qpow x k)) ≤
      ((y + -x) * (y + -x)) * Q'.ofNat k := by
  let δ := y + -x
  have hδ : (0 : Q') ≤ δ := Q'.sub_nonneg_of_le hxy
  have hlo : (0 : Q') ≤ monomialIncrement x y k + -(δ * qpow x k) :=
    Q'.sub_nonneg_of_le (leftRectangle_le_increment hx hxy k)
  have hu : monomialIncrement x y k + -(δ * qpow x k) ≤
      δ * (qpow y k + -qpow x k) := by
    have h := Q'.add_le_add_right _ _ (-(δ * qpow x k))
      (increment_le_rightRectangle hx hxy k)
    have he : δ * qpow y k + -(δ * qpow x k) ≈
        δ * (qpow y k + -qpow x k) :=
      RingNormaliser.poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
        (.mul (.var 0) (.add (.var 1) (.neg (.var 2)))) (by decide)
        (fun | 0 => δ | 1 => qpow y k | _ => qpow x k)
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv he)
  have htop : monomialIncrement x y k + -(δ * qpow x k) ≤
      (δ * δ) * Q'.ofNat k := by
    have hp : δ * (qpow y k + -qpow x k) ≤ δ * (δ * Q'.ofNat k) :=
      Q'.mul_le_mul_of_nonneg_left _ _ δ (power_cell_difference_le k x y hx hxy hy) hδ
    exact Q'.le_trans' _ _ _ hu
      (Q'.le_trans' _ _ _ hp
        (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv δ δ (Q'.ofNat k)))))
  have hcap : (0 : Q') ≤ (δ*δ)*Q'.ofNat k :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hδ hδ) (zero_le_ofNat k)
  exact Q'.abs_le (Q'.le_trans' _ _ _ (Q'.neg_le_neg hcap) hlo) htop

/-- Signed finite primitive-cell error, with no positivity of coefficients. -/
theorem primitive_cell_error (k : Nat) (p : Poly) (x y : Q')
    (hx : (0 : Q') ≤ x) (hxy : x ≤ y) (hy : y ≤ (1 : Q')) :
    Q'.abs (primitiveIncrement k p x y + -((y + -x) * powerEval k p x)) ≤
      ((y + -x) * (y + -x)) * primitiveCellBudget k p := by
  induction p generalizing k with
  | nil =>
      change Q'.abs ((0 : Q') + -((y + -x) * 0)) ≤
        ((y + -x) * (y + -x)) * 0
      have hz : (0 : Q') + -((y + -x)*0) ≈ 0 :=
        Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left 0 _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_zero_eqv _)))
          (by decide)
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.abs_eqv_congr hz) (by decide)))
        (Q'.ge_of_eqv (Q'.mul_zero_eqv _))
  | cons c cs ih =>
      let δ := y + -x
      let A := monomialIncrement x y k
      let B := δ * qpow x k
      let C := primitiveIncrement (k+1) cs x y
      let D := δ * powerEval (k+1) cs x
      have he : (c*A+C) + -(δ*(c*qpow x k+powerEval (k+1) cs x)) ≈
          c*(A + -B) + (C + -D) :=
        RingNormaliser.poly_identity_of_normal_eq
          (.add (.add (.mul (.var 0) (.var 1)) (.var 2))
            (.neg (.mul (.var 3) (.add (.mul (.var 0) (.var 4)) (.var 5)))))
          (.add (.mul (.var 0) (.add (.var 1) (.neg (.mul (.var 3) (.var 4)))))
            (.add (.var 2) (.neg (.mul (.var 3) (.var 5))))) (by decide)
          (fun
            | 0 => c
            | 1 => A
            | 2 => C
            | 3 => δ
            | 4 => qpow x k
            | _ => powerEval (k+1) cs x)
      have hc : Q'.abs (c*(A + -B)) ≤ Q'.abs c * ((δ*δ)*Q'.ofNat k) :=
        Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
          (Q'.mul_le_mul_of_nonneg_left _ _ _ (monomial_cell_error k x y hx hxy hy)
            (Q'.abs_nonneg c))
      have ht : Q'.abs (C + -D) ≤ (δ*δ)*primitiveCellBudget (k+1) cs := ih (k+1)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr he))
        (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
          (Q'.le_trans' _ _ _ (Q'.add_le_add hc ht) (Q'.le_of_eqv (by
            change Q'.abs c * ((δ*δ)*Q'.ofNat k) +
                (δ*δ)*primitiveCellBudget (k+1) cs ≈
              (δ*δ)*(Q'.abs c*Q'.ofNat k+primitiveCellBudget (k+1) cs)
            ring_qeqv))))

/-- Computed Taylor budget: the degree-weighted absolute derivative coefficients. -/
def taylorCellBudget (p : Poly) : Q' := primitiveCellBudget 0 (pderiv p)

theorem taylorCellBudget_nonnegative (p : Poly) : (0 : Q') ≤ taylorCellBudget p :=
  primitiveCellBudget_nonnegative 0 (pderiv p)

/-- Literal signed-polynomial first-order Taylor remainder on any rational
cell in [0,1], including equal endpoints and degree-zero polynomials. -/
theorem polynomial_taylor_cell_error (p : Poly) (x y : Q')
    (hx : (0 : Q') ≤ x) (hxy : x ≤ y) (hy : y ≤ (1 : Q')) :
    Q'.abs ((eval p y + -eval p x) + -((y + -x) * eval (pderiv p) x)) ≤
      ((y + -x) * (y + -x)) * taylorCellBudget p := by
  have he : primitiveIncrement 0 (pderiv p) x y +
      -((y + -x)*powerEval 0 (pderiv p) x) ≈
      (eval p y + -eval p x) + -((y + -x)*eval (pderiv p) x) :=
    Q'.add_eqv_congr' (formal_derivative_increment p x y)
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (powerEval_horner 0 (pderiv p) x) (Q'.one_mul_eqv _))))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_eqv_congr he))
    (primitive_cell_error 0 (pderiv p) x y hx hxy hy)

end YMGap.Continuum.RationalPolynomialTaylorCell

#print axioms YMGap.Continuum.RationalPolynomialTaylorCell.primitiveCellBudget
#print axioms YMGap.Continuum.RationalPolynomialTaylorCell.primitiveCellBudget_nonnegative
#print axioms YMGap.Continuum.RationalPolynomialTaylorCell.power_cell_difference_le
#print axioms YMGap.Continuum.RationalPolynomialTaylorCell.monomial_cell_error
#print axioms YMGap.Continuum.RationalPolynomialTaylorCell.primitive_cell_error
#print axioms YMGap.Continuum.RationalPolynomialTaylorCell.taylorCellBudget
#print axioms YMGap.Continuum.RationalPolynomialTaylorCell.taylorCellBudget_nonnegative
#print axioms YMGap.Continuum.RationalPolynomialTaylorCell.polynomial_taylor_cell_error
