/-
# Actual formal jets under unit-slope affine translation

Horner composition with [c,1] is differentiated using the actual finite
coefficient derivative and its Leibniz law. Coefficient reflection then pins
the first derivative before a second differentiation. No chain-rule premise
or independent recursive jet is supplied.

Consumer: the SAME shifted Jacobi product and unshifted finite Chebyshev
series, including both formal jets. This is finite polynomial algebra only.
-/

import YMGap.Continuum.QPolyRatPolySubstitutionAlgebra
import YMGap.Continuum.ChebyshevFormalJets

namespace YMGap.Continuum.QPolyAffineJetTranslation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyCoefficientEvaluation (coefficient_eval)
open YMGap.Continuum.QPolyRatPolySubstitutionAlgebra (compose eval_compose)
open YMGap.Continuum.ChebyshevFormalJets (coefficients_of_eval_eqv)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- The existing finite Horner composition, with unit slope. -/
def translate (c : Q') (p : Poly) : Poly := compose [c,1] p

private theorem add_congr {a b c d : Q'} (hab : a ≈ b) (hcd : c ≈ d) :
    a+c ≈ b+d := QPoly.q_add_congr hab hcd

private theorem mul_congr {a b c d : Q'} (hab : a ≈ b) (hcd : c ≈ d) :
    a*c ≈ b*d := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hab)
      (Q'.mul_eqv_congr_left _ _ _ hcd)

private theorem eval_arg_congr {x y : Q'} (h : x ≈ y) : ∀ p : Poly,
    eval p x ≈ eval p y
  | [] => Q'.eqv_refl 0
  | c::p => add_congr (Q'.eqv_refl c) (mul_congr h (eval_arg_congr h p))

private theorem eval_constant (c x : Q') : eval [c] x ≈ c :=
  poly_identity_of_normal_eq (.add (.var 0) (.mul (.var 1) (.const 0))) (.var 0)
    (by decide) (fun
      | 0 => c
      | _ => x)

private theorem eval_affine (c x : Q') : eval [c,1] x ≈ c+x :=
  poly_identity_of_normal_eq
    (.add (.var 0) (.mul (.var 1) (.add (.const 1) (.mul (.var 1) (.const 0)))))
    (.add (.var 0) (.var 1)) (by decide) (fun
      | 0 => c
      | _ => x)

private theorem eval_affine_derivative (c x : Q') :
    eval (pderiv [c,1]) x ≈ 1 :=
  Q'.eqv_trans _ _ _ (eval_constant (1*1) x) (Q'.one_mul_eqv 1)

private theorem eval_coordinate (x : Q') : eval [0,1] x ≈ x :=
  Q'.eqv_trans _ _ _ (eval_affine 0 x) (QPoly.q_zero_add_eqv x)

private theorem eval_derivative_add (p q : Poly) (x : Q') :
    eval (pderiv (padd p q)) x ≈ eval (pderiv p) x + eval (pderiv q) x :=
  Q'.eqv_trans _ _ _ (coefficient_eval (pderiv_padd p q) x)
    (eval_padd (pderiv p) (pderiv q) x)

private theorem eval_derivative_product (p q : Poly) (x : Q') :
    eval (pderiv (pmul p q)) x ≈
      eval (pderiv p) x*eval q x + eval p x*eval (pderiv q) x :=
  Q'.eqv_trans _ _ _ (coefficient_eval (pderiv_pmul p q) x)
    (Q'.eqv_trans _ _ _ (eval_padd _ _ x)
      (add_congr (eval_pmul _ _ x) (eval_pmul _ _ x)))

private theorem horner_coeff_pin (c : Q') (p : Poly) :
    CoeffEqv (c::p) (padd [c] (pmul [0,1] p)) :=
  coefficients_of_eval_eqv _ _ (fun x => Q'.eqv_symm (Q'.eqv_trans _ _ _
    (eval_padd [c] (pmul [0,1] p) x)
    (add_congr (eval_constant c x)
      (Q'.eqv_trans _ _ _ (eval_pmul [0,1] p x)
        (mul_congr (eval_coordinate x) (Q'.eqv_refl _))))))

private theorem eval_derivative_horner (c : Q') (p : Poly) (x : Q') :
    eval (pderiv (c::p)) x ≈ eval p x + x*eval (pderiv p) x := by
  have he : eval (pderiv (c::p)) x ≈
      0 + (1*eval p x + x*eval (pderiv p) x) :=
    Q'.eqv_trans _ _ _ (coefficient_eval (horner_coeff_pin c p).pderiv x)
      (Q'.eqv_trans _ _ _ (eval_derivative_add [c] (pmul [0,1] p) x)
        (add_congr (Q'.eqv_refl 0)
          (Q'.eqv_trans _ _ _ (eval_derivative_product [0,1] p x)
            (add_congr (mul_congr (eval_affine_derivative 0 x) (Q'.eqv_refl _))
              (mul_congr (eval_coordinate x) (Q'.eqv_refl _))))))
  exact Q'.eqv_trans _ _ _ he (Q'.eqv_trans _ _ _ (QPoly.q_zero_add_eqv _)
    (add_congr (Q'.one_mul_eqv _) (Q'.eqv_refl _)))

/-- The actual composed polynomial evaluates at c+x, including trailing zeros. -/
theorem eval_translate (c : Q') (p : Poly) (x : Q') :
    eval (translate c p) x ≈ eval p (c+x) :=
  Q'.eqv_trans _ _ _ (eval_compose [c,1] x p)
    (eval_arg_congr (eval_affine c x) p)

/-- Unit-slope chain rule derived from the finite Horner/Leibniz recursion. -/
theorem eval_translate_derivative (c : Q') : ∀ (p : Poly) (x : Q'),
    eval (pderiv (translate c p)) x ≈ eval (pderiv p) (c+x)
  | [], _ => Q'.eqv_refl 0
  | a::p, x => by
      have he : eval (pderiv (translate c (a::p))) x ≈
          0 + (1*eval p (c+x) + (c+x)*eval (pderiv p) (c+x)) :=
        Q'.eqv_trans _ _ _ (eval_derivative_add [a] (pmul [c,1] (translate c p)) x)
          (add_congr (Q'.eqv_refl 0)
            (Q'.eqv_trans _ _ _ (eval_derivative_product [c,1] (translate c p) x)
              (add_congr
                (mul_congr (eval_affine_derivative c x) (eval_translate c p x))
                (mul_congr (eval_affine c x) (eval_translate_derivative c p x)))))
      exact Q'.eqv_trans _ _ _ he (Q'.eqv_trans _ _ _ (QPoly.q_zero_add_eqv _)
        (Q'.eqv_trans _ _ _ (add_congr (Q'.one_mul_eqv _) (Q'.eqv_refl _))
          (Q'.eqv_symm (eval_derivative_horner a p (c+x)))))

/-- Padded coefficient equality of the actual translated first derivatives. -/
theorem derivative_coeff_pin (c : Q') (p : Poly) :
    CoeffEqv (pderiv (translate c p)) (translate c (pderiv p)) :=
  coefficients_of_eval_eqv _ _ (fun x => Q'.eqv_trans _ _ _
    (eval_translate_derivative c p x) (Q'.eqv_symm (eval_translate c (pderiv p) x)))

/-- Second formal differentiation follows from the actual first coefficient pin. -/
theorem second_derivative_coeff_pin (c : Q') (p : Poly) :
    CoeffEqv (pderiv (pderiv (translate c p))) (translate c (pderiv (pderiv p))) :=
  (derivative_coeff_pin c p).pderiv.trans (derivative_coeff_pin c (pderiv p))

/-- Both evaluated second jets belong to the same actual finite polynomial. -/
theorem eval_translate_second_derivative (c : Q') (p : Poly) (x : Q') :
    eval (pderiv (pderiv (translate c p))) x ≈ eval (pderiv (pderiv p)) (c+x) :=
  Q'.eqv_trans _ _ _ (coefficient_eval (second_derivative_coeff_pin c p) x)
    (eval_translate c (pderiv (pderiv p)) x)

end YMGap.Continuum.QPolyAffineJetTranslation

#print axioms YMGap.Continuum.QPolyAffineJetTranslation.translate
#print axioms YMGap.Continuum.QPolyAffineJetTranslation.eval_translate
#print axioms YMGap.Continuum.QPolyAffineJetTranslation.eval_translate_derivative
#print axioms YMGap.Continuum.QPolyAffineJetTranslation.derivative_coeff_pin
#print axioms YMGap.Continuum.QPolyAffineJetTranslation.second_derivative_coeff_pin
#print axioms YMGap.Continuum.QPolyAffineJetTranslation.eval_translate_second_derivative
