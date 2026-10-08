/-
# The actual bare theta angular prefixes as a constructive real

The N-th approximation is the literal angularSum of the original bare
Gaussian coefficients. Its actual signed squared-mode increments pay the
existing derivative-weighted shell, uniformly for x in [-1,1] at each
named 0<w<1. The cutoff is the checked oneSidedCutoff without an index
shift. Actual finite formal angular jets are pinned separately.

This constructs the angular series, not the derivative of a value limit.
No product-angular limit identification, theta addition formula, curvature
ceiling, Haar/original-action estimate or physical bound is claimed.
-/

import YMGap.Continuum.ThetaOneSidedSeriesCompletion
import YMGap.Continuum.ThetaJointAngularPin

namespace YMGap.Continuum.ThetaBareAngularCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteJacobiAngularComparison (angularSum angularEval angular_seriesPoly)
open YMGap.Continuum.ThetaJointAngularPin (barePolynomial)
open YMGap.Continuum.ThetaOneSidedSeriesCompletion
  (oneSidedCutoff shellPrefix_cauchy shellPrefixCReal)
open YMGap.Continuum.ThetaAngularShellTail (shellTerm)
open YMGap.Continuum.ThetaParityShellWeights (chebT_abs_le_one)
open YMGap.Continuum.ChebTFwdBoundClose (ofNat_nonneg ofNat_mul_eqv ofNat_le_ofNat)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- The literal angular squared-mode increment, with its actual minus sign. -/
def bareAngularTerm (w x : Q') (n : Nat) : Q' :=
  -(2*w^(n*n)*(Q'.ofNat n*Q'.ofNat n)*Cheb.T n x)

/-- The actual increment pays the original Gaussian shell after index zero. -/
theorem bareAngularTerm_shell_abs_le {w x : Q'}
    (hw0 : (0 : Q') < w) (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (n : Nat) (hn : 1 ≤ n) : Q'.abs (bareAngularTerm w x n) ≤ shellTerm w n := by
  let c := 2*w^(n*n)*(Q'.ofNat n*Q'.ofNat n)
  have hp : (0 : Q') ≤ w^(n*n) := Q'.pow_nonneg w (Q'.le_of_lt hw0) _
  have hc : (0 : Q') ≤ c := Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide) hp)
    (Q'.mul_nonneg _ _ (ofNat_nonneg n) (ofNat_nonneg n))
  have ht : Q'.abs (c*Cheb.T n x) ≤ c :=
    Q'.le_trans' _ _ _ (TsumDeriv.Q'.abs_mul_le _ _)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (chebT_abs_le_one n hx0 hx1)
          (Q'.abs_nonneg c))
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _))
          (Q'.le_of_eqv (TsumDeriv.Q'.abs_of_nonneg hc))))
  have hn3 : n*n ≤ n*n*n := by
    have h := Nat.mul_le_mul_left (n*n) hn
    simpa only [Nat.mul_one] using h
  have hcoef : 2*(Q'.ofNat n*Q'.ofNat n) ≤ 16*Q'.ofNat (n*n*n) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv
      (Q'.eqv_symm (Q'.eqv_trans _ _ _ (ofNat_mul_eqv 2 (n*n))
        (Q'.mul_eqv_congr_left 2 _ _ (ofNat_mul_eqv n n)))))
      (Q'.le_trans' _ _ _ (ofNat_le_ofNat (show 2*(n*n) ≤ 16*(n*n*n) by omega))
        (Q'.le_of_eqv (ofNat_mul_eqv 16 (n*n*n))))
  have hregroup : c ≈ (2*(Q'.ofNat n*Q'.ofNat n))*w^(n*n) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.const 2) (.var 0)) (.var 1))
      (.mul (.mul (.const 2) (.var 1)) (.var 0))
      (by decide) (fun
        | 0 => w^(n*n)
        | _ => Q'.ofNat n*Q'.ofNat n)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (TsumDeriv.Q'.abs_neg _))
    (Q'.le_trans' _ _ _ ht (Q'.le_trans' _ _ _ (Q'.le_of_eqv hregroup)
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hcoef hp)))

private theorem bareAngular_succ (w x : Q') (N : Nat) :
    angularSum (fun j => w^(j*j)) x (N+1) ≈
      angularSum (fun j => w^(j*j)) x N + bareAngularTerm w x (N+1) := Q'.eqv_refl _

/-- The named shell cutoff is uniform in the coordinate for the actual
finite angular sums; no positive-density floor is needed. -/
theorem bareAngular_cauchy {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon) (m n : Nat)
    (hm : oneSidedCutoff w epsilon ≤ m) (hn : oneSidedCutoff w epsilon ≤ n) :
    angularSum (fun j => w^(j*j)) x m ≤ angularSum (fun j => w^(j*j)) x n+epsilon ∧
      angularSum (fun j => w^(j*j)) x n ≤ angularSum (fun j => w^(j*j)) x m+epsilon :=
  shellPrefix_cauchy hw0 hw1 (angularSum (fun j => w^(j*j)) x) (bareAngularTerm w x)
    (bareAngular_succ w x) (bareAngularTerm_shell_abs_le hw0 hx0 hx1) epsilon he m n hm hn

/-- Direct completion of the literal original bare angular prefixes. -/
def bareAngularCReal {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) : CReal :=
  shellPrefixCReal hw0 hw1 (angularSum (fun j => w^(j*j)) x) (bareAngularTerm w x)
    (bareAngular_succ w x) (bareAngularTerm_shell_abs_le hw0 hx0 hx1)

@[simp] theorem bareAngularCReal_approx {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (N : Nat) :
    (bareAngularCReal hw0 hw1 hx0 hx1).approx N = angularSum (fun j => w^(j*j)) x N := rfl

/-- Every actual approximation is the formal angular jet of the SAME
finite bare polynomial. This is not differentiation of a completed value. -/
theorem bareAngularCReal_formal_pin {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (N : Nat) :
    (bareAngularCReal hw0 hw1 hx0 hx1).approx N ≈ angularEval (barePolynomial w N) x :=
  Q'.eqv_symm (angular_seriesPoly (fun j => w^(j*j)) x N)

end YMGap.Continuum.ThetaBareAngularCompletion

#print axioms YMGap.Continuum.ThetaBareAngularCompletion.bareAngularTerm
#print axioms YMGap.Continuum.ThetaBareAngularCompletion.bareAngularTerm_shell_abs_le
#print axioms YMGap.Continuum.ThetaBareAngularCompletion.bareAngular_cauchy
#print axioms YMGap.Continuum.ThetaBareAngularCompletion.bareAngularCReal
#print axioms YMGap.Continuum.ThetaBareAngularCompletion.bareAngularCReal_approx
#print axioms YMGap.Continuum.ThetaBareAngularCompletion.bareAngularCReal_formal_pin
