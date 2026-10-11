/-
# Finite coefficient norms for the actual regularized-log primitive

The reciprocal coefficients and zero-initial primitive are the computed
objects of RegularizedLogPolynomialProductDefect. Dividing the kth coefficient
by a positive successor does not increase its weighted absolute norm; adding
the initial zero contributes exactly one factor of the radius.

The finite power-difference bound is intended for defect_primitive evaluated
at a NEGATIVE artanh-window argument. It bounds the actual signed polynomial,
not an interval derivative or a replacement primitive. No analytic integration,
logarithm law, operator estimate or physical survival conclusion is assumed.
-/

import YMGap.Continuum.RegularizedLogPolynomialProductDefect
import YMGap.Constructive.QPolyWeightedL1

namespace YMGap.Continuum.RegularizedLogPrimitiveNorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyWeightedL1
open YMGap.Constructive.QPolyPositivePrimitive (polynomialPower)
open YMGap.Constructive.QPolyFinitePowerDifference
open YMGap.Continuum.RegularizedLogPolynomialProductDefect
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem reciprocal_abs_le_one (start : Nat) :
    Q'.abs (Q'.invSucc start) ≤ (1 : Q') := by
  rw [ExpNeg.abs_of_nonneg (Q'.invSucc_nonneg start)]
  exact Q'.le_trans' _ _ _
    (ExpNeg.invSucc_le_of_le (Nat.zero_le start)) (by decide)

/-- Every starting coefficient index is allowed, including zero; the
polynomial coefficients may have arbitrary signs. -/
theorem reciprocalCoefficients_weightedL1_le
    (rho : Q') (hrho : (0 : Q') ≤ rho) (start : Nat) (p : Poly) :
    weightedL1 rho (reciprocalCoefficients start p) ≤ weightedL1 rho p := by
  induction p generalizing start with
  | nil => exact Q'.le_refl' _
  | cons c p ih =>
      change Q'.abs (Q'.invSucc start*c) +
          rho*weightedL1 rho (reciprocalCoefficients (start+1) p) ≤
        Q'.abs c + rho*weightedL1 rho p
      have hhead : Q'.abs (Q'.invSucc start*c) ≤ Q'.abs c :=
        Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
          (Q'.le_trans' _ _ _
            (Q'.mul_le_mul_of_nonneg_right _ _ (Q'.abs c)
              (reciprocal_abs_le_one start) (Q'.abs_nonneg c))
            (Q'.le_of_eqv (Q'.one_mul_eqv _)))
      exact Q'.add_le_add hhead
        (Q'.mul_le_mul_of_nonneg_left _ _ rho (ih (start+1)) hrho)

/-- The literal zero-initial primitive is bounded by radius times input norm.
In particular radius zero and the zero polynomial require no special inverse. -/
theorem primitive_weightedL1_le
    (rho : Q') (hrho : (0 : Q') ≤ rho) (p : Poly) :
    weightedL1 rho (primitive p) ≤ rho*weightedL1 rho p :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv (weightedL1_zero_cons_eqv rho (reciprocalCoefficients 0 p)))
    (Q'.mul_le_mul_of_nonneg_left _ _ rho
      (reciprocalCoefficients_weightedL1_le rho hrho 0 p) hrho)

private theorem unit_norm (rho : Q') : weightedL1 rho [1] ≈ (1 : Q') := by
  change Q'.abs (1 : Q')+rho*0 ≈ (1 : Q')
  exact Q'.eqv_trans _ _ _
    (q_add_congr (by decide : Q'.abs (1 : Q') ≈ 1) (q_mul_zero rho))
    (q_add_zero_eqv 1)

/-- Powers of the original coefficient polynomial obey submultiplicativity,
including exponent zero and signed coefficients. -/
theorem polynomialPower_weightedL1_le
    (rho : Q') (hrho : (0 : Q') ≤ rho) (p : Poly) (n : Nat) :
    weightedL1 rho (polynomialPower p n) ≤ (weightedL1 rho p)^n := by
  induction n with
  | zero => exact Q'.le_of_eqv (unit_norm rho)
  | succ n ih =>
      exact Q'.le_trans' _ _ _ (weightedL1_pmul_le rho hrho p _)
        (Q'.mul_le_mul_of_nonneg_left _ _ (weightedL1 rho p) ih
          (weightedL1_nonnegative rho hrho p))

/-- A supplied rational coefficient-radius ceiling, not an analytic premise,
propagates to every finite polynomial power. -/
theorem polynomialPower_weightedL1_le_cap
    (rho : Q') (hrho : (0 : Q') ≤ rho) (p : Poly)
    (R : Q') (hR : (0 : Q') ≤ R) (hp : weightedL1 rho p ≤ R) (n : Nat) :
    weightedL1 rho (polynomialPower p n) ≤ R^n := by
  induction n with
  | zero => exact Q'.le_of_eqv (unit_norm rho)
  | succ n ih =>
      exact Q'.le_trans' _ _ _ (weightedL1_pmul_le rho hrho p _)
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ (weightedL1 rho p) ih
            (weightedL1_nonnegative rho hrho p))
          (Q'.mul_le_mul_of_nonneg_right _ _ (R^n) hp (Q'.pow_nonneg R hR n)))

private theorem row_step (R : Q') (n : Nat) :
    R*(Q'.ofNat (n+1)*R^n)+R^(n+1) ≈ Q'.ofNat (n+2)*R^(n+1) := by
  have hcoef : Q'.ofNat (n+2) ≈ Q'.ofNat (n+1)+1 :=
    Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv (n+1) 1)
      (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_refl (1 : Q')))
  have hring : R*(Q'.ofNat (n+1)*R^n)+R^(n+1) ≈
      (Q'.ofNat (n+1)+1)*R^(n+1) :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 0) (.var 2)))
      (.mul (.add (.var 1) (.const 1)) (.mul (.var 0) (.var 2)))
      (by decide) (fun | 0 => R | 1 => Q'.ofNat (n+1) | _ => R^n)
  exact Q'.eqv_trans _ _ _ hring
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hcoef))

/-- A difference-of-powers row with n+1 terms costs at most (n+1)R^n.
The result is valid at R=0 and does not divide by a radius or by a polynomial. -/
theorem powerDifferenceRow_weightedL1_le
    (rho : Q') (hrho : (0 : Q') ≤ rho) (p q : Poly)
    (R : Q') (hR : (0 : Q') ≤ R)
    (hp : weightedL1 rho p ≤ R) (hq : weightedL1 rho q ≤ R) (n : Nat) :
    weightedL1 rho (powerDifferenceRow p q (n+1)) ≤ Q'.ofNat (n+1)*R^n := by
  induction n with
  | zero =>
      have hz : weightedL1 rho (pmul p []) ≤ (0 : Q') :=
        Q'.le_trans' _ _ _ (weightedL1_pmul_le rho hrho p [])
          (Q'.le_of_eqv (q_mul_zero _))
      have h := Q'.le_trans' _ _ _ (weightedL1_padd_le rho hrho (pmul p []) [1])
        (Q'.add_le_add hz (Q'.le_of_eqv (unit_norm rho)))
      exact Q'.le_trans' _ _ _ h
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (q_zero_add_eqv 1)
          (Q'.eqv_symm (Q'.one_mul_eqv 1))))
  | succ n ih =>
      have hrow : weightedL1 rho (pmul p (powerDifferenceRow p q (n+1))) ≤
          R*(Q'.ofNat (n+1)*R^n) :=
        Q'.le_trans' _ _ _ (weightedL1_pmul_le rho hrho p _)
          (Q'.le_trans' _ _ _
            (Q'.mul_le_mul_of_nonneg_left _ _ (weightedL1 rho p) ih
              (weightedL1_nonnegative rho hrho p))
            (Q'.mul_le_mul_of_nonneg_right _ _ _ hp
              (Q'.mul_nonneg _ _ (by
                rw [Q'.zero_le_iff_num_nonneg]
                exact Int.natCast_nonneg (n+1)) (Q'.pow_nonneg R hR n))))
      have hpower := polynomialPower_weightedL1_le_cap rho hrho q R hR hq (n+1)
      exact Q'.le_trans' _ _ _
        (weightedL1_padd_le rho hrho (pmul p (powerDifferenceRow p q (n+1)))
          (polynomialPower q (n+1)))
        (Q'.le_trans' _ _ _ (Q'.add_le_add hrow hpower)
          (Q'.le_of_eqv (row_step R n)))

end YMGap.Continuum.RegularizedLogPrimitiveNorm

#print axioms YMGap.Continuum.RegularizedLogPrimitiveNorm.reciprocalCoefficients_weightedL1_le
#print axioms YMGap.Continuum.RegularizedLogPrimitiveNorm.primitive_weightedL1_le
#print axioms YMGap.Continuum.RegularizedLogPrimitiveNorm.polynomialPower_weightedL1_le
#print axioms YMGap.Continuum.RegularizedLogPrimitiveNorm.polynomialPower_weightedL1_le_cap
#print axioms YMGap.Continuum.RegularizedLogPrimitiveNorm.powerDifferenceRow_weightedL1_le
