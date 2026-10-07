/-
# Actual finite Chebyshev polynomials and their first two formal jets

The first-kind coefficient polynomial has the literal two-step recurrence.
Its formal first derivative evaluates to the existing Lcoef, and its second
derivative evaluates to n*Uderiv_(n-1). The existing second-kind chebPoly is
reused. Constructive coefficient reflection pins the first derivative before
differentiating it again; no same-jet premise is supplied.

Consumer: finite joint theta endpoint/curvature identities. All orders,
including zero, and every rational scalar are covered. No infinite derivative
interchange, theta addition identity, angular frame, or curvature estimate is
claimed.
-/

import YMGap.Constructive.QPolyCoefficientEvaluation
import YMGap.Continuum.SU2ClassPolynomialExtensionalReflection
import YMGap.Continuum.ChebTFwdRatioClose
import YMGap.Continuum.ChebUDClosure
import YMGap.Continuum.HeatKernelNodeQuad
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.ChebyshevFormalJets

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyCoefficient
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Continuum.SU2ClassPolynomialAlgebra (chi0 chi1 chebPoly eval_chebPoly eval_chi0 eval_chi1)
open YMGap.Continuum.ChebTFwdRatioClose (Lcoef Lcoef_rec)
open YMGap.Continuum.ChebOrthoWeightedFTC (Uderiv)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- Actual first-kind coefficient polynomial: 1, x, 2*x*T_(n+1)-T_n. -/
def Tpoly : Nat → Poly
  | 0 => [1]
  | 1 => [0,1]
  | n+2 => psub (pmul chi1 (Tpoly (n+1))) (Tpoly n)

/-- The existing scalar second jet, with the zero order made explicit. -/
def H : Nat → Q' → Q'
  | 0, _ => 0
  | n+1, x => Q'.ofNat (n+1)*Uderiv n x

private theorem add_congr {a b c d : Q'} (hab : a ≈ b) (hcd : c ≈ d) :
    a+c ≈ b+d := QPoly.q_add_congr hab hcd

private theorem mul_congr {a b c d : Q'} (hab : a ≈ b) (hcd : c ≈ d) :
    a*c ≈ b*d := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hab)
      (Q'.mul_eqv_congr_left _ _ _ hcd)

private theorem eval_constant (c x : Q') : eval [c] x ≈ c :=
  poly_identity_of_normal_eq (.add (.var 0) (.mul (.var 1) (.const 0))) (.var 0)
    (by decide) (fun
      | 0 => c
      | _ => x)

private theorem eval_coordinate (x : Q') : eval [0,1] x ≈ x :=
  poly_identity_of_normal_eq
    (.add (.const 0) (.mul (.var 0) (.add (.const 1) (.mul (.var 0) (.const 0)))))
    (.var 0) (by decide) (fun _ => x)

/-- The coefficient recurrence evaluates to the ORIGINAL scalar T_n. -/
theorem eval_Tpoly : ∀ n x, eval (Tpoly n) x ≈ Cheb.T n x
  | 0, x => eval_constant 1 x
  | 1, x => eval_coordinate x
  | n+2, x => Q'.eqv_trans _ _ _ (eval_psub _ _ x)
      (add_congr
        (Q'.eqv_trans _ _ _ (eval_pmul _ _ x)
          (mul_congr (eval_chi1 x) (eval_Tpoly (n+1) x)))
        (Q'.neg_eqv_congr _ _ (eval_Tpoly n x)))

private theorem derivative_sub_coeff (p q : Poly) :
    CoeffEqv (pderiv (psub p q)) (psub (pderiv p) (pderiv q)) :=
  (pderiv_padd p (pneg q)).trans
    ((CoeffEqv.refl (pderiv p)).padd (pderiv_pscale (-1) q))

private theorem eval_derivative_sub (p q : Poly) (x : Q') :
    eval (pderiv (psub p q)) x ≈ eval (pderiv p) x + -(eval (pderiv q) x) :=
  Q'.eqv_trans _ _ _
    (QPolyCoefficientEvaluation.coefficient_eval (derivative_sub_coeff p q) x)
    (eval_psub _ _ x)

private theorem eval_derivative_product (p q : Poly) (x : Q') :
    eval (pderiv (pmul p q)) x ≈
      eval (pderiv p) x*eval q x + eval p x*eval (pderiv q) x :=
  Q'.eqv_trans _ _ _
    (QPolyCoefficientEvaluation.coefficient_eval (pderiv_pmul p q) x)
    (Q'.eqv_trans _ _ _ (eval_padd _ _ x)
      (add_congr (eval_pmul _ _ x) (eval_pmul _ _ x)))

private theorem eval_derivative_chi1 (x : Q') : eval (pderiv chi1) x ≈ (2 : Q') :=
  Q'.eqv_trans _ _ _ (eval_constant (1*2) x)
    (Q'.one_mul_eqv 2)

private theorem derivative_recurrence (p q : Poly) (x : Q') :
    eval (pderiv (psub (pmul chi1 p) q)) x ≈
      ((2*x)*eval (pderiv p) x + -(eval (pderiv q) x)) + 2*eval p x := by
  have he := Q'.eqv_trans _ _ _ (eval_derivative_sub (pmul chi1 p) q x)
    (add_congr
      (Q'.eqv_trans _ _ _ (eval_derivative_product chi1 p x)
        (add_congr (mul_congr (eval_derivative_chi1 x) (Q'.eqv_refl _))
          (mul_congr (eval_chi1 x) (Q'.eqv_refl _))))
      (Q'.eqv_refl _))
  exact Q'.eqv_trans _ _ _ he (poly_identity_of_normal_eq
    (.add (.add (.mul (.const 2) (.var 0)) (.mul (.mul (.const 2) (.var 1)) (.var 2)))
      (.neg (.var 3)))
    (.add (.add (.mul (.mul (.const 2) (.var 1)) (.var 2)) (.neg (.var 3)))
      (.mul (.const 2) (.var 0)))
    (by decide) (fun
      | 0 => eval p x
      | 1 => x
      | 2 => eval (pderiv p) x
      | _ => eval (pderiv q) x))

private theorem Lcoef_recurrence_two (n : Nat) (x : Q') :
    Lcoef x (n+2) ≈ ((2*x)*Lcoef x (n+1) + -(Lcoef x n)) + 2*Cheb.T (n+1) x :=
  Q'.eqv_trans _ _ _ (Lcoef_rec x n)
    (add_congr
      (add_congr (mul_congr
        (mul_congr (by decide : (1 : Q')+1 ≈ 2) (Q'.eqv_refl x)) (Q'.eqv_refl _))
        (Q'.eqv_refl _))
      (mul_congr (by decide : (1 : Q')+1 ≈ 2) (Q'.eqv_refl _)))

/-- The ACTUAL first formal derivative, not a new recursive jet. -/
theorem eval_Tpoly_derivative : ∀ n x, eval (pderiv (Tpoly n)) x ≈ Lcoef x n
  | 0, _ => Q'.eqv_refl 0
  | 1, x => eval_constant (1*1) x
  | n+2, x => Q'.eqv_trans _ _ _ (derivative_recurrence (Tpoly (n+1)) (Tpoly n) x)
      (Q'.eqv_trans _ _ _
        (add_congr
          (add_congr (Q'.mul_eqv_congr_left (2*x) _ _ (eval_Tpoly_derivative (n+1) x))
            (Q'.neg_eqv_congr _ _ (eval_Tpoly_derivative n x)))
          (Q'.mul_eqv_congr_left 2 _ _ (eval_Tpoly (n+1) x)))
        (Q'.eqv_symm (Lcoef_recurrence_two n x)))

/-- The existing second-kind polynomial's formal derivative agrees with
the ORIGINAL Uderiv recurrence at every rational scalar. -/
theorem eval_chebPoly_derivative : ∀ n x, eval (pderiv (chebPoly n)) x ≈ Uderiv n x
  | 0, _ => Q'.eqv_refl 0
  | 1, x => eval_derivative_chi1 x
  | n+2, x => Q'.eqv_trans _ _ _ (derivative_recurrence (chebPoly (n+1)) (chebPoly n) x)
      (Q'.eqv_trans _ _ _
        (add_congr
          (add_congr (Q'.mul_eqv_congr_left (2*x) _ _ (eval_chebPoly_derivative (n+1) x))
            (Q'.neg_eqv_congr _ _ (eval_chebPoly_derivative n x)))
          (Q'.mul_eqv_congr_left 2 _ _ (eval_chebPoly (n+1) x)))
        (Q'.add_comm_eqv _ _))

private theorem zero_coefficient_of_members : ∀ (p : Poly),
    (∀ c, c ∈ p → c ≈ 0) → ∀ i, coeff p i ≈ 0
  | [], _, _ => Q'.eqv_refl 0
  | c::cs, h, 0 => h c List.mem_cons_self
  | c::cs, h, i+1 => zero_coefficient_of_members cs
      (fun a ha => h a (List.mem_cons_of_mem c ha)) i

/-- Constructive reflection into padded coefficients, so extensional finite
identities may be transported through actual formal derivatives. -/
theorem coefficients_of_eval_eqv (p q : Poly)
    (h : ∀ x, eval p x ≈ eval q x) : CoeffEqv p q := by
  have hz : ∀ c, c ∈ psub p q → c ≈ 0 :=
    SU2ClassPolynomialExtensionalReflection.coeffZero_of_evalZero (psub p q) (fun x =>
      Q'.eqv_trans _ _ _ (eval_psub p q x)
        (Q'.eqv_trans _ _ _ (add_congr (h x) (Q'.eqv_refl _))
          (Q'.add_neg_self_eqv (eval q x))))
  intro i
  have he : coeff p i + (-1)*coeff q i ≈ 0 := Q'.eqv_trans _ _ _
    (Q'.eqv_symm (coeff_psub p q i)) (zero_coefficient_of_members _ hz i)
  have hn : (-1)*coeff q i ≈ -(coeff q i) := Q'.eqv_trans _ _ _
    (Q'.neg_mul_eqv 1 (coeff q i)) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))
  exact QPoly.q_eqv_of_sub_zero (Q'.eqv_trans _ _ _
    (Q'.eqv_symm (add_congr (Q'.eqv_refl (coeff p i)) hn)) he)

/-- Padded coefficient pin; this is what authorizes the second formal
differentiation, rather than differentiating a supplied scalar equality. -/
theorem derivative_coeff_pin (n : Nat) :
    CoeffEqv (pderiv (Tpoly (n+1))) (pscale (Q'.ofNat (n+1)) (chebPoly n)) :=
  coefficients_of_eval_eqv _ _ (fun x => Q'.eqv_trans _ _ _ (eval_Tpoly_derivative (n+1) x)
    (Q'.eqv_symm (Q'.eqv_trans _ _ _ (eval_pscale _ _ x)
      (Q'.mul_eqv_congr_left _ _ _ (eval_chebPoly n x)))))

/-- The ACTUAL second formal derivative is the original scalar H_n. -/
theorem eval_Tpoly_second_derivative : ∀ n x,
    eval (pderiv (pderiv (Tpoly n))) x ≈ H n x
  | 0, _ => Q'.eqv_refl 0
  | n+1, x => Q'.eqv_trans _ _ _
      (QPolyCoefficientEvaluation.coefficient_eval (derivative_coeff_pin n).pderiv x)
      (Q'.eqv_trans _ _ _
        (QPolyCoefficientEvaluation.coefficient_eval
          (pderiv_pscale (Q'.ofNat (n+1)) (chebPoly n)) x)
        (Q'.eqv_trans _ _ _ (eval_pscale (Q'.ofNat (n+1)) (pderiv (chebPoly n)) x)
          (Q'.mul_eqv_congr_left _ _ _ (eval_chebPoly_derivative n x))))

/-- Genuine endpoint first jet, including the constant order. -/
theorem first_derivative_at_one (n : Nat) :
    eval (pderiv (Tpoly n)) 1 ≈ Q'.ofNat n*Q'.ofNat n := by
  cases n with
  | zero => exact Q'.eqv_symm (Q'.zero_mul_eqv 0)
  | succ n =>
      exact Q'.eqv_trans _ _ _ (eval_Tpoly_derivative (n+1) 1)
        (Q'.mul_eqv_congr_left _ _ _ (HeatKernelNodeQuad.U_at_one n))

private theorem scalar_angular_ode : ∀ n x,
    (1 + -(x*x))*H n x + -(x*Lcoef x n) ≈
      -(Q'.ofNat n*Q'.ofNat n*Cheb.T n x)
  | 0, x => poly_identity_of_normal_eq
      (.add (.mul (.add (.const 1) (.neg (.mul (.var 0) (.var 0)))) (.const 0))
        (.neg (.mul (.var 0) (.const 0))))
      (.neg (.mul (.mul (.const 0) (.const 0)) (.const 1)))
      (by decide) (fun _ => x)
  | n+1, x => by
      have hUD := ChebUDClosure.UD_all n x
      have hs : (1 + -(x*x))*H (n+1) x + -(x*Lcoef x (n+1)) ≈
          Q'.ofNat (n+1)*((1 + -(x*x))*Uderiv n x) +
            -(x*(Q'.ofNat (n+1)*Cheb.U n x)) :=
        poly_identity_of_normal_eq
          (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
            (.neg (.mul (.var 3) (.mul (.var 1) (.var 4)))))
          (.add (.mul (.var 1) (.mul (.var 0) (.var 2)))
            (.neg (.mul (.var 3) (.mul (.var 1) (.var 4)))))
          (by decide) (fun
            | 0 => 1 + -(x*x)
            | 1 => Q'.ofNat (n+1)
            | 2 => Uderiv n x
            | 3 => x
            | _ => Cheb.U n x)
      exact Q'.eqv_trans _ _ _ hs (Q'.eqv_trans _ _ _
        (add_congr (Q'.mul_eqv_congr_left _ _ _ hUD) (Q'.eqv_refl _))
        (poly_identity_of_normal_eq
          (.add (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.neg (.mul (.var 0) (.var 3)))))
            (.neg (.mul (.var 1) (.mul (.var 0) (.var 2)))))
          (.neg (.mul (.mul (.var 0) (.var 0)) (.var 3)))
          (by decide) (fun
            | 0 => Q'.ofNat (n+1)
            | 1 => x
            | 2 => Cheb.U n x
            | _ => Cheb.T (n+1) x)))

/-- Angular ODE pinned to the actual first and second QPoly derivatives,
at every rational scalar. No abstract differentiation operator is assumed. -/
theorem formal_angular_ode (n : Nat) (x : Q') :
    (1 + -(x*x))*eval (pderiv (pderiv (Tpoly n))) x +
      -(x*eval (pderiv (Tpoly n)) x) ≈
        -(Q'.ofNat n*Q'.ofNat n*eval (Tpoly n) x) :=
  Q'.eqv_trans _ _ _
    (add_congr (Q'.mul_eqv_congr_left _ _ _ (eval_Tpoly_second_derivative n x))
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ (eval_Tpoly_derivative n x))))
    (Q'.eqv_trans _ _ _ (scalar_angular_ode n x)
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (eval_Tpoly n x)))))

end YMGap.Continuum.ChebyshevFormalJets

#print axioms YMGap.Continuum.ChebyshevFormalJets.Tpoly
#print axioms YMGap.Continuum.ChebyshevFormalJets.H
#print axioms YMGap.Continuum.ChebyshevFormalJets.eval_Tpoly
#print axioms YMGap.Continuum.ChebyshevFormalJets.eval_Tpoly_derivative
#print axioms YMGap.Continuum.ChebyshevFormalJets.eval_chebPoly_derivative
#print axioms YMGap.Continuum.ChebyshevFormalJets.coefficients_of_eval_eqv
#print axioms YMGap.Continuum.ChebyshevFormalJets.derivative_coeff_pin
#print axioms YMGap.Continuum.ChebyshevFormalJets.eval_Tpoly_second_derivative
#print axioms YMGap.Continuum.ChebyshevFormalJets.first_derivative_at_one
#print axioms YMGap.Continuum.ChebyshevFormalJets.formal_angular_ode
