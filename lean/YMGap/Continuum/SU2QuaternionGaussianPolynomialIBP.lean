/-
# Polynomial Gaussian integration by parts

The monomial recurrence is lifted here to a genuine polynomial functional.
For a coefficient list `p`, `gaussianExpectation p` is the exact standard
Gaussian moment sum.  The main theorem is the algebraic integration-by-parts
identity

  E[x p(x)] = E[p'(x)].

No representing measure, limits, or choice principles enter the proof.
-/

import YMGap.Continuum.SU2QuaternionGaussianMomentRecurrence
import YMGap.Constructive.QPoly

namespace YMGap.Continuum.SU2QuaternionGaussianPolynomialIBP

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.SU2QuaternionHaarGaussianRadialFactor
open YMGap.Continuum.SU2QuaternionGaussianMomentRecurrence

local infix:50 " ≈ " => Q'.eqv

set_option maxHeartbeats 300000
set_option maxRecDepth 10000

/-- The standard one-coordinate Gaussian moment extracted from the exact
four-coordinate product formula. -/
def gaussianMoment1 (n : Nat) : Q' := gaussianMoment4 n 0 0 0

theorem gaussianMoment1_shift (n : Nat) :
    gaussianMoment1 (n + 2) ≈
      Q'.ofNat (n + 1) * gaussianMoment1 n :=
  gaussianMoment4_shift0 n 0 0 0

theorem gaussianMoment1_one : gaussianMoment1 1 ≈ 0 := by
  decide

/-- Moment evaluation beginning at exponent `n`. -/
def gaussianExpectationFrom : Nat → Poly → Q'
  | _, [] => 0
  | n, c :: cs =>
      c * gaussianMoment1 n + gaussianExpectationFrom (n + 1) cs

/-- Exact Gaussian expectation of a univariate rational polynomial. -/
def gaussianExpectation (p : Poly) : Q' := gaussianExpectationFrom 0 p

/-- Multiply the successive coefficients by `s,s+1,...`. -/
def scaleFrom : Nat → Poly → Poly
  | _, [] => []
  | s, c :: cs => (Q'.ofNat s * c) :: scaleFrom (s + 1) cs

/-- Formal derivative on low-to-high coefficient lists. -/
def pderiv : Poly → Poly
  | [] => []
  | _ :: cs => scaleFrom 1 cs

/-- Exact additivity of the shifted Gaussian moment functional. -/
theorem gaussianExpectationFrom_padd : ∀ (n : Nat) (p q : Poly),
    gaussianExpectationFrom n (padd p q) ≈
      gaussianExpectationFrom n p + gaussianExpectationFrom n q
  | _, [], q => Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | _, _ :: _, [] => Q'.eqv_symm (QPoly.q_add_zero_eqv _)
  | n, c :: cs, d :: ds => by
      have hhead :
          (c + d) * gaussianMoment1 n ≈
            c * gaussianMoment1 n + d * gaussianMoment1 n :=
        QPoly.q_add_mul c d (gaussianMoment1 n)
      have htail := gaussianExpectationFrom_padd (n + 1) cs ds
      refine Q'.eqv_trans _
        ((c * gaussianMoment1 n + d * gaussianMoment1 n) +
          (gaussianExpectationFrom (n + 1) cs +
            gaussianExpectationFrom (n + 1) ds)) _
        (QPoly.q_add_congr hhead htail) ?_
      exact QPoly.q_interchange
        (c * gaussianMoment1 n) (d * gaussianMoment1 n)
        (gaussianExpectationFrom (n + 1) cs)
        (gaussianExpectationFrom (n + 1) ds)

/-- Exact rational homogeneity of the shifted Gaussian moment functional. -/
theorem gaussianExpectationFrom_pscale (a : Q') : ∀ (n : Nat) (p : Poly),
    gaussianExpectationFrom n (pscale a p) ≈
      a * gaussianExpectationFrom n p
  | _, [] => Q'.eqv_symm (QPoly.q_mul_zero a)
  | n, c :: cs => by
      have hhead :
          (a * c) * gaussianMoment1 n ≈
            a * (c * gaussianMoment1 n) :=
        Q'.mul_assoc_eqv a c (gaussianMoment1 n)
      have htail := gaussianExpectationFrom_pscale a (n + 1) cs
      refine Q'.eqv_trans _
        (a * (c * gaussianMoment1 n) +
          a * gaussianExpectationFrom (n + 1) cs) _
        (QPoly.q_add_congr hhead htail) ?_
      exact Q'.eqv_symm
        (Q'.mul_add_eqv a (c * gaussianMoment1 n)
          (gaussianExpectationFrom (n + 1) cs))

theorem gaussianExpectation_padd (p q : Poly) :
    gaussianExpectation (padd p q) ≈
      gaussianExpectation p + gaussianExpectation q :=
  gaussianExpectationFrom_padd 0 p q

theorem gaussianExpectation_pscale (a : Q') (p : Poly) :
    gaussianExpectation (pscale a p) ≈
      a * gaussianExpectation p :=
  gaussianExpectationFrom_pscale a 0 p

/-- The coefficientwise lift of the monomial moment recurrence. -/
theorem gaussianExpectationFrom_shift : ∀ (s : Nat) (p : Poly),
    gaussianExpectationFrom (s + 2) p ≈
      gaussianExpectationFrom s (scaleFrom (s + 1) p)
  | _, [] => Q'.eqv_refl 0
  | s, c :: cs => by
      have hhead :
          c * gaussianMoment1 (s + 2) ≈
            (Q'.ofNat (s + 1) * c) * gaussianMoment1 s := by
        refine Q'.eqv_trans _
          (c * (Q'.ofNat (s + 1) * gaussianMoment1 s)) _
          (Q'.mul_eqv_congr_left c _ _ (gaussianMoment1_shift s)) ?_
        refine Q'.eqv_trans _
          ((c * Q'.ofNat (s + 1)) * gaussianMoment1 s) _
          (Q'.eqv_symm (Q'.mul_assoc_eqv c (Q'.ofNat (s + 1))
            (gaussianMoment1 s))) ?_
        exact Q'.mul_eqv_congr_right _ _ (gaussianMoment1 s)
          (Q'.mul_comm_eqv c (Q'.ofNat (s + 1)))
      have htail :
          gaussianExpectationFrom (s + 3) cs ≈
            gaussianExpectationFrom (s + 1) (scaleFrom (s + 2) cs) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          gaussianExpectationFrom_shift (s + 1) cs
      exact QPoly.q_add_congr hhead htail

/-- **Exact polynomial Gaussian integration by parts.**  Prefixing a zero
coefficient multiplies by `x`; its expectation equals that of the formal
derivative. -/
theorem gaussianExpectation_mulX_eq_deriv (p : Poly) :
    gaussianExpectation (0 :: p) ≈ gaussianExpectation (pderiv p) := by
  cases p with
  | nil =>
      unfold gaussianExpectation gaussianExpectationFrom pderiv
      exact QPoly.q_add_zero_eqv 0
  | cons c cs =>
      have hzeroHead :
          (0 : Q') * gaussianMoment1 0 ≈ 0 := QPoly.q_zero_mul _
      have hoddHead : c * gaussianMoment1 1 ≈ 0 :=
        Q'.eqv_trans _ (c * 0) _
          (Q'.mul_eqv_congr_left c _ _ gaussianMoment1_one)
          (QPoly.q_mul_zero c)
      have hdrop :
          (0 : Q') * gaussianMoment1 0 +
              (c * gaussianMoment1 1 + gaussianExpectationFrom 2 cs) ≈
            gaussianExpectationFrom 2 cs := by
        refine Q'.eqv_trans _
          (0 + (0 + gaussianExpectationFrom 2 cs)) _
          (QPoly.q_add_congr hzeroHead
            (QPoly.q_add_congr hoddHead (Q'.eqv_refl _))) ?_
        exact Q'.eqv_trans _ (0 + gaussianExpectationFrom 2 cs) _
          (QPoly.q_zero_add_eqv _)
          (QPoly.q_zero_add_eqv _)
      unfold gaussianExpectation pderiv
      refine Q'.eqv_trans _ (gaussianExpectationFrom 2 cs) _ hdrop ?_
      simpa using gaussianExpectationFrom_shift 0 cs

end YMGap.Continuum.SU2QuaternionGaussianPolynomialIBP

#print axioms YMGap.Continuum.SU2QuaternionGaussianPolynomialIBP.gaussianExpectationFrom_shift
#print axioms YMGap.Continuum.SU2QuaternionGaussianPolynomialIBP.gaussianExpectation_mulX_eq_deriv
#print axioms YMGap.Continuum.SU2QuaternionGaussianPolynomialIBP.gaussianExpectation_padd
#print axioms YMGap.Continuum.SU2QuaternionGaussianPolynomialIBP.gaussianExpectation_pscale
