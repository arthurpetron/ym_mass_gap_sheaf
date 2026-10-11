/-
# Supporting lower tangents for the finite logarithm polynomial

The literal finite sum ell_N(t) = sum_(k=1..N) (1-t)^k/k has its
computed supporting LOWER tangent whenever x,m <= 1. No inverse of
either input, positivity of either input, or positive series cutoff is
required. The exact identity p_N(t) = t*ell_N(t) also includes t=0.

The intended consumer integrates this tangent against the original
source-biased weight W*g, at its computed second/first moment ratio.
This scalar producer does not assert a kurtosis bound, a source-relative
interacting estimate, a late-response bound, or a physical mass gap.
-/

import YMGap.Continuum.RegularizedLogPolynomialConcavity

namespace YMGap.Continuum.RegularizedLogPolynomialLowerTangent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RegularizedLogPolynomial (partialSum term)
open YMGap.Continuum.RegularizedLogPolynomialConcavity (power_tangent)
open YMGap.Continuum.BernsteinSequenceWrap (eval_ppow eval1m pow_eqv_congr)

local infix:50 " ≈ " => Q'.eqv

/-- The actual finite sum, with N terms and an empty sum at zero. -/
def ell (t : Q') : Nat → Q'
  | 0 => 0
  | n+1 => ell t n + Q'.invSucc n*(1-t)^(n+1)

/-- The computed derivative of ell; coefficients are retained exactly. -/
def slope (m : Q') : Nat → Q'
  | 0 => 0
  | n+1 => slope m n - Q'.invSucc n*(Q'.ofNat (n+1)*(1-m)^n)

private theorem tangent_term (n : Nat) (x m : Q') (hx : x ≤ 1)
    (hm : m ≤ 1) :
    Q'.invSucc n*(1-m)^(n+1) +
      (-(Q'.invSucc n*(Q'.ofNat (n+1)*(1-m)^n)))*(x-m) ≤
        Q'.invSucc n*(1-x)^(n+1) := by
  have hp := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.invSucc n)
    (power_tangent n (1-x) (1-m)
      (Q'.sub_nonneg_of_le hx) (Q'.sub_nonneg_of_le hm))
    (Q'.invSucc_nonneg n)
  have hleft :
      Q'.invSucc n*(1-m)^(n+1) +
        (-(Q'.invSucc n*(Q'.ofNat (n+1)*(1-m)^n)))*(x-m) ≈
      Q'.invSucc n*((1-m)^(n+1) +
        Q'.ofNat (n+1)*(1-m)^n*((1-x)-(1-m))) :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1))
        (.mul (.neg (.mul (.var 0) (.var 2)))
          (.add (.var 3) (.neg (.var 4)))))
      (.mul (.var 0)
        (.add (.var 1) (.mul (.var 2)
          (.add (.add (.const 1) (.neg (.var 3)))
            (.neg (.add (.const 1) (.neg (.var 4))))))))
      (by decide)
      (fun | 0 => Q'.invSucc n
           | 1 => (1-m)^(n+1)
           | 2 => Q'.ofNat (n+1)*(1-m)^n
           | 3 => x
           | _ => m)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hp

/-- The supporting lower tangent is global on the half-line x,m <= 1.
In particular both closed endpoints of [0,1] and N=0 are included. -/
theorem lower_tangent (N : Nat) (x m : Q') (hx : x ≤ 1) (hm : m ≤ 1) :
    ell m N+slope m N*(x-m) ≤ ell x N := by
  induction N with
  | zero =>
      change (0 : Q')+0*(x-m) ≤ 0
      exact Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.const 0) (.mul (.const 0) (.var 0)))
        (.const 0) (by decide) (fun _ => x-m))
  | succ n ih =>
      have h := Q'.add_le_add ih (tangent_term n x m hx hm)
      have hleft :
          ell m (n+1)+slope m (n+1)*(x-m) ≈
          (ell m n+slope m n*(x-m)) +
            (Q'.invSucc n*(1-m)^(n+1) +
              (-(Q'.invSucc n*(Q'.ofNat (n+1)*(1-m)^n)))*(x-m)) := by
        change (ell m n+Q'.invSucc n*(1-m)^(n+1)) +
          (slope m n-Q'.invSucc n*(Q'.ofNat (n+1)*(1-m)^n))*(x-m) ≈ _
        exact poly_identity_of_normal_eq
          (.add (.add (.var 0) (.var 1))
            (.mul (.add (.var 2) (.neg (.var 3))) (.var 4)))
          (.add (.add (.var 0) (.mul (.var 2) (.var 4)))
            (.add (.var 1) (.mul (.neg (.var 3)) (.var 4))))
          (by decide)
          (fun | 0 => ell m n
               | 1 => Q'.invSucc n*(1-m)^(n+1)
               | 2 => slope m n
               | 3 => Q'.invSucc n*(Q'.ofNat (n+1)*(1-m)^n)
               | _ => x-m)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) h

/-- Exact regularized-entropy identity without division by t. -/
theorem partial_pin (t : Q') (N : Nat) : partialSum t N ≈ t*ell t N := by
  induction N with
  | zero => exact Q'.eqv_symm (Q'.mul_zero_eqv t)
  | succ n ih =>
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' ih (Q'.eqv_refl _)) ?_
      change t*ell t n+Q'.invSucc n*(t*(1-t)^(n+1)) ≈
        t*(ell t n+Q'.invSucc n*(1-t)^(n+1))
      exact poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.var 1))
          (.mul (.var 2) (.mul (.var 0) (.var 3))))
        (.mul (.var 0) (.add (.var 1) (.mul (.var 2) (.var 3))))
        (by decide)
        (fun | 0 => t
             | 1 => ell t n
             | 2 => Q'.invSucc n
             | _ => (1-t)^(n+1))

private def termPolynomial (n : Nat) : QPoly.Poly :=
  QPoly.pscale (Q'.invSucc n) (ppow [1,-1] (n+1))

/-- The finite polynomial with exactly the same rational coefficients as ell. -/
def polynomial : Nat → QPoly.Poly
  | 0 => []
  | n+1 => QPoly.padd (polynomial n) (termPolynomial n)

private theorem termPolynomial_eval (n : Nat) (t : Q') :
    QPoly.eval (termPolynomial n) t ≈ Q'.invSucc n*(1-t)^(n+1) :=
  Q'.eqv_trans _ _ _ (QPoly.eval_pscale _ _ _)
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ (eval_ppow _ _ _) (pow_eqv_congr (eval1m t) _)))

/-- Evaluation pins the actual finite polynomial, including its zero cutoff. -/
theorem polynomial_eval (N : Nat) (t : Q') :
    QPoly.eval (polynomial N) t ≈ ell t N := by
  induction N with
  | zero => exact Q'.eqv_refl _
  | succ n ih =>
      exact Q'.eqv_trans _ _ _ (QPoly.eval_padd _ _ _)
        (Q'.add_eqv_congr' ih (termPolynomial_eval n t))

end YMGap.Continuum.RegularizedLogPolynomialLowerTangent

#print axioms YMGap.Continuum.RegularizedLogPolynomialLowerTangent.ell
#print axioms YMGap.Continuum.RegularizedLogPolynomialLowerTangent.slope
#print axioms YMGap.Continuum.RegularizedLogPolynomialLowerTangent.lower_tangent
#print axioms YMGap.Continuum.RegularizedLogPolynomialLowerTangent.partial_pin
#print axioms YMGap.Continuum.RegularizedLogPolynomialLowerTangent.polynomial
#print axioms YMGap.Continuum.RegularizedLogPolynomialLowerTangent.polynomial_eval
