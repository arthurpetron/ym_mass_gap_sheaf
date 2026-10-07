/-
# Actual finite Jacobi formal jets and the radial moment cancellation

The first three formal derivatives of the actual Jacobi product are evaluated
at 1+x and pinned to its first three finite logarithmic-derivative moments.
The actual inverse-nome/half-normalized heat and both of its formal derivatives
are then pinned to the checked radial-mixture numerator.

The final scalar nonnegativity consumes an explicit PRODUCT cost ceiling;
this module does not produce that analytic ceiling. Empty prefixes are retained.
No intrinsic angular, Haar-certificate, original-action, Poisson, OS or physical
scaling conclusion is asserted.
-/

import YMGap.Continuum.JacobiHeatTransverseCurvature
import YMGap.Continuum.JacobiHeatRadialMixtureCancellation
import YMGap.Constructive.QPolyCoefficientEvaluation

namespace YMGap.Continuum.JacobiHeatRadialMomentJets

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyCoefficient
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.JTPFullProductDerivativeNormalization
open YMGap.Continuum.JacobiShiftedPositiveCoefficients
open YMGap.Continuum.JacobiHeatRadialMixtureCancellation

local infix:50 " ≈ " => Q'.eqv

private theorem add_congr {a b c d : Q'} (h : a ≈ b) (g : c ≈ d) : a+c ≈ b+d :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right a b c h) (Q'.add_eqv_congr_left b c d g)

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (g : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a b c h) (Q'.mul_eqv_congr_left b c d g)

private theorem neg_congr {a b : Q'} (h : a ≈ b) : -a ≈ -b := Q'.neg_eqv_congr _ _ h

private theorem formal_eval_congr (y : Q') (p q : Poly)
    (h : QPolyFormalDerivative.CoeffEqv p q) : QPoly.eval p y ≈ QPoly.eval q y :=
  QPolyCoefficientEvaluation.coefficient_eval h y

private theorem singleton_mul_scale (b : Q') (p : Poly) :
    QPolyFormalDerivative.CoeffEqv (pmul p [b]) (pscale b p) := by
  apply (coeffEqv_pmul_comm p [b]).trans
  intro i
  have hz : coeff [(0 : Q')] i ≈ 0 := by
    cases i <;> exact Q'.eqv_refl 0
  exact Q'.eqv_trans _ _ _ (coeff_padd i (pscale b p) [(0 : Q')])
    (Q'.eqv_trans _ _ _ (add_congr (Q'.eqv_refl _) hz) (QPoly.q_add_zero_eqv _))

private theorem affine_derivative_coeff (p : Poly) (a b : Q') :
    QPolyFormalDerivative.CoeffEqv (pderiv (pmul p [a,b]))
      (padd (pmul (pderiv p) [a,b]) (pscale b p)) := by
  have hf : QPolyFormalDerivative.CoeffEqv (pderiv [a,b]) [b] := by
    intro i
    cases i with
    | zero => exact Q'.one_mul_eqv b
    | succ i => exact Q'.eqv_refl 0
  exact (pderiv_pmul p [a,b]).trans
    ((QPolyFormalDerivative.CoeffEqv.refl _).padd
      (((QPolyFormalDerivative.CoeffEqv.refl p).pmul hf).trans (singleton_mul_scale b p)))

private theorem eval_derivative_add (p q : Poly) (y : Q') :
    QPoly.eval (pderiv (padd p q)) y ≈ QPoly.eval (pderiv p) y+QPoly.eval (pderiv q) y :=
  Q'.eqv_trans _ _ _ (formal_eval_congr y _ _ (pderiv_padd p q)) (eval_padd _ _ y)

private theorem eval_derivative_scale (a : Q') (p : Poly) (y : Q') :
    QPoly.eval (pderiv (pscale a p)) y ≈ a*QPoly.eval (pderiv p) y :=
  Q'.eqv_trans _ _ _ (formal_eval_congr y _ _ (pderiv_pscale a p)) (eval_pscale a _ y)

private theorem eval_second_add (p q : Poly) (y : Q') :
    QPoly.eval (pderiv (pderiv (padd p q))) y ≈
      QPoly.eval (pderiv (pderiv p)) y+QPoly.eval (pderiv (pderiv q)) y :=
  Q'.eqv_trans _ _ _ (formal_eval_congr y _ _ (pderiv_padd p q).pderiv)
    (eval_derivative_add (pderiv p) (pderiv q) y)

private theorem eval_second_scale (a : Q') (p : Poly) (y : Q') :
    QPoly.eval (pderiv (pderiv (pscale a p))) y ≈ a*QPoly.eval (pderiv (pderiv p)) y :=
  Q'.eqv_trans _ _ _ (formal_eval_congr y _ _ (pderiv_pscale a p).pderiv)
    (eval_derivative_scale a (pderiv p) y)

private theorem affine_first (p : Poly) (a b y : Q') :
    QPoly.eval (pderiv (pmul p [a,b])) y ≈
      QPoly.eval (pderiv p) y*QPoly.eval [a,b] y+QPoly.eval p y*b :=
  Q'.eqv_trans _ _ _ (formal_eval_congr y _ _ (affine_derivative_coeff p a b))
    (Q'.eqv_trans _ _ _ (eval_padd _ _ y)
      (add_congr (eval_pmul _ _ y)
        (Q'.eqv_trans _ _ _ (eval_pscale b p y) (Q'.mul_comm_eqv _ _))))

private theorem affine_second (p : Poly) (a b y : Q') :
    QPoly.eval (pderiv (pderiv (pmul p [a,b]))) y ≈
      QPoly.eval (pderiv (pderiv p)) y*QPoly.eval [a,b] y+
        (2*QPoly.eval (pderiv p) y)*b := by
  have h := Q'.eqv_trans _ _ _
    (formal_eval_congr y _ _ (affine_derivative_coeff p a b).pderiv)
    (Q'.eqv_trans _ _ _ (eval_derivative_add (pmul (pderiv p) [a,b]) (pscale b p) y)
      (add_congr (affine_first (pderiv p) a b y) (eval_derivative_scale b p y)))
  exact Q'.eqv_trans _ _ _ h (poly_identity_of_normal_eq
    (.add (.add (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))) (.mul (.var 3) (.var 2)))
    (.add (.mul (.var 0) (.var 1)) (.mul (.mul (.const 2) (.var 2)) (.var 3)))
    (by decide) (fun
      | 0 => QPoly.eval (pderiv (pderiv p)) y
      | 1 => QPoly.eval [a,b] y
      | 2 => QPoly.eval (pderiv p) y
      | _ => b))

private theorem affine_third (p : Poly) (a b y : Q') :
    QPoly.eval (pderiv (pderiv (pderiv (pmul p [a,b])))) y ≈
      QPoly.eval (pderiv (pderiv (pderiv p))) y*QPoly.eval [a,b] y+
        (3*QPoly.eval (pderiv (pderiv p)) y)*b := by
  have h := Q'.eqv_trans _ _ _
    (formal_eval_congr y _ _ (affine_derivative_coeff p a b).pderiv.pderiv)
    (Q'.eqv_trans _ _ _ (eval_second_add (pmul (pderiv p) [a,b]) (pscale b p) y)
      (add_congr (affine_second (pderiv p) a b y) (eval_second_scale b p y)))
  exact Q'.eqv_trans _ _ _ h (poly_identity_of_normal_eq
    (.add (.add (.mul (.var 0) (.var 1)) (.mul (.mul (.const 2) (.var 2)) (.var 3)))
      (.mul (.var 3) (.var 2)))
    (.add (.mul (.var 0) (.var 1)) (.mul (.mul (.const 3) (.var 2)) (.var 3)))
    (by decide) (fun
      | 0 => QPoly.eval (pderiv (pderiv (pderiv p))) y
      | 1 => QPoly.eval [a,b] y
      | 2 => QPoly.eval (pderiv (pderiv p)) y
      | _ => b))

/-- Coefficient-level pin of the actual Leibniz polynomial to P'. -/
theorem product_derivative_coeff_pin (w : Q') : ∀ N,
    QPolyFormalDerivative.CoeffEqv (pderiv (product w N)) (derivative w N)
  | 0 => QPolyFormalDerivative.CoeffEqv.refl []
  | N+1 => (affine_derivative_coeff (product w N) (base w N) (gFacDx w N)).trans
      (((product_derivative_coeff_pin w N).pmul (QPolyFormalDerivative.CoeffEqv.refl (factor w N))).padd
        (QPolyFormalDerivative.CoeffEqv.refl (pscale (gFacDx w N) (product w N))))

def firstMoment (w x : Q') (N : Nat) : Q' := M1 (HKConv.sTerm w x) N
def secondMoment (w x : Q') (N : Nat) : Q' := M2 (HKConv.sTerm w x) N
def thirdMoment (w x : Q') (N : Nat) : Q' := M3 (HKConv.sTerm w x) N

/-- Actual first formal product derivative, including the empty prefix. -/
theorem product_first_moment_pin {w x : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hx : (-1 : Q') ≤ x) (N : Nat) :
    QPoly.eval (pderiv (product w N)) (1+x) ≈ ThetaConv.Ppart w x N*firstMoment w x N :=
  Q'.eqv_trans _ _ _ (formal_eval_congr (1+x) _ _ (product_derivative_coeff_pin w N))
    (Q'.eqv_trans _ _ _ (eval_derivative w x N) (fullProdDx_eqv_Ppart_mul_Spart hw0 hw1 hx N))

/-- Actual second formal product derivative with the diagonal moment retained. -/
theorem product_second_moment_pin {w x : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hx : (-1 : Q') ≤ x) : ∀ N,
    QPoly.eval (pderiv (pderiv (product w N))) (1+x) ≈
      ThetaConv.Ppart w x N*(firstMoment w x N*firstMoment w x N + -(secondMoment w x N))
  | 0 => by change (0 : Q') ≈ 1*(0*0 + -0); decide
  | N+1 => by
      have hrec := affine_second (product w N) (base w N) (gFacDx w N) (1+x)
      have hsub := add_congr
        (mul_congr (product_second_moment_pin hw0 hw1 hx N) (eval_factor w x N))
        (mul_congr (mul_congr (Q'.eqv_refl (2 : Q')) (product_first_moment_pin hw0 hw1 hx N))
          (Q'.eqv_symm (gFac_mul_sTerm_eqv_gFacDx hw0 hw1 hx N)))
      exact Q'.eqv_trans _ _ _ hrec (Q'.eqv_trans _ _ _ hsub
        (poly_identity_of_normal_eq
          (.add (.mul (.mul (.var 0) (.add (.mul (.var 1) (.var 1)) (.neg (.var 2)))) (.var 3))
            (.mul (.mul (.const 2) (.mul (.var 0) (.var 1))) (.mul (.var 3) (.var 4))))
          (.mul (.mul (.var 0) (.var 3))
            (.add (.mul (.add (.var 1) (.var 4)) (.add (.var 1) (.var 4)))
              (.neg (.add (.var 2) (.mul (.var 4) (.var 4))))))
          (by decide) (fun
            | 0 => ThetaConv.Ppart w x N
            | 1 => firstMoment w x N
            | 2 => secondMoment w x N
            | 3 => ThetaConv.gFac w x N
            | _ => HKConv.sTerm w x N)))

/-- Actual third formal derivative, with both repeated-index corrections. -/
theorem product_third_moment_pin {w x : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hx : (-1 : Q') ≤ x) : ∀ N,
    QPoly.eval (pderiv (pderiv (pderiv (product w N)))) (1+x) ≈
      ThetaConv.Ppart w x N*((firstMoment w x N*firstMoment w x N)*firstMoment w x N +
        -((3*firstMoment w x N)*secondMoment w x N) + 2*thirdMoment w x N)
  | 0 => by change (0 : Q') ≈ 1*((0*0)*0 + -((3*0)*0) + 2*0); decide
  | N+1 => by
      have hrec := affine_third (product w N) (base w N) (gFacDx w N) (1+x)
      have hsub := add_congr
        (mul_congr (product_third_moment_pin hw0 hw1 hx N) (eval_factor w x N))
        (mul_congr (mul_congr (Q'.eqv_refl (3 : Q')) (product_second_moment_pin hw0 hw1 hx N))
          (Q'.eqv_symm (gFac_mul_sTerm_eqv_gFacDx hw0 hw1 hx N)))
      let a : PolyExpr := .var 1
      let b : PolyExpr := .var 2
      let c : PolyExpr := .var 3
      let r : PolyExpr := .var 5
      let cubic (s t u : PolyExpr) : PolyExpr :=
        .add (.add (.mul (.mul s s) s) (.neg (.mul (.mul (.const 3) s) t))) (.mul (.const 2) u)
      exact Q'.eqv_trans _ _ _ hrec (Q'.eqv_trans _ _ _ hsub
        (poly_identity_of_normal_eq
          (.add (.mul (.mul (.var 0) (cubic a b c)) (.var 4))
            (.mul (.mul (.const 3) (.mul (.var 0) (.add (.mul a a) (.neg b)))) (.mul (.var 4) r)))
          (.mul (.mul (.var 0) (.var 4))
            (cubic (.add a r) (.add b (.mul r r)) (.add c (.mul (.mul r r) r))))
          (by decide) (fun
            | 0 => ThetaConv.Ppart w x N
            | 1 => firstMoment w x N
            | 2 => secondMoment w x N
            | 3 => thirdMoment w x N
            | 4 => ThetaConv.gFac w x N
            | _ => HKConv.sTerm w x N)))

def normalizedProduct (w x : Q') (N : Nat) : Q' :=
  (SU2PointwiseHeatPositiveCompletion.inverseNome w*HalfPow.half)*ThetaConv.Ppart w x N

private theorem normalized_mul (a P s : Q') : a*(P*s) ≈ (a*P)*s :=
  Q'.eqv_symm (Q'.mul_assoc_eqv a P s)

/-- Literal inverse-nome/half-normalized heat value. -/
theorem heat_eval_moment_pin {w x : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hx : (-1 : Q') ≤ x) (N : Nat) :
    QPoly.eval (heat w N) (1+x) ≈ normalizedProduct w x N*firstMoment w x N :=
  Q'.eqv_trans _ _ _
    (eval_pscale (SU2PointwiseHeatPositiveCompletion.inverseNome w*HalfPow.half) (derivative w N) (1+x))
    (Q'.eqv_trans _ _ _ (mul_congr
      (Q'.eqv_refl (SU2PointwiseHeatPositiveCompletion.inverseNome w*HalfPow.half))
      (Q'.eqv_trans _ _ _ (eval_derivative w x N) (fullProdDx_eqv_Ppart_mul_Spart hw0 hw1 hx N)))
      (normalized_mul (SU2PointwiseHeatPositiveCompletion.inverseNome w*HalfPow.half)
        (ThetaConv.Ppart w x N) (firstMoment w x N)))

/-- Literal formal derivative of normalized heat, not a free jet. -/
theorem heat_first_moment_pin {w x : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hx : (-1 : Q') ≤ x) (N : Nat) :
    QPoly.eval (pderiv (heat w N)) (1+x) ≈
      normalizedProduct w x N*(firstMoment w x N*firstMoment w x N + -(secondMoment w x N)) :=
  Q'.eqv_trans _ _ _
    (eval_derivative_scale (SU2PointwiseHeatPositiveCompletion.inverseNome w*HalfPow.half) (derivative w N) (1+x))
    (Q'.eqv_trans _ _ _ (mul_congr
      (Q'.eqv_refl (SU2PointwiseHeatPositiveCompletion.inverseNome w*HalfPow.half))
      (Q'.eqv_trans _ _ _ (formal_eval_congr (1+x) (pderiv (derivative w N))
        (pderiv (pderiv (product w N))) ((product_derivative_coeff_pin w N).pderiv.symm))
        (product_second_moment_pin hw0 hw1 hx N)))
      (normalized_mul (SU2PointwiseHeatPositiveCompletion.inverseNome w*HalfPow.half)
        (ThetaConv.Ppart w x N)
        (firstMoment w x N*firstMoment w x N + -(secondMoment w x N))))

/-- Literal second formal derivative of normalized heat. -/
theorem heat_second_moment_pin {w x : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hx : (-1 : Q') ≤ x) (N : Nat) :
    QPoly.eval (pderiv (pderiv (heat w N))) (1+x) ≈
      normalizedProduct w x N*((firstMoment w x N*firstMoment w x N)*firstMoment w x N +
        -((3*firstMoment w x N)*secondMoment w x N) + 2*thirdMoment w x N) :=
  Q'.eqv_trans _ _ _
    (eval_second_scale (SU2PointwiseHeatPositiveCompletion.inverseNome w*HalfPow.half) (derivative w N) (1+x))
    (Q'.eqv_trans _ _ _ (mul_congr
      (Q'.eqv_refl (SU2PointwiseHeatPositiveCompletion.inverseNome w*HalfPow.half))
      (Q'.eqv_trans _ _ _ (formal_eval_congr (1+x) (pderiv (pderiv (derivative w N)))
        (pderiv (pderiv (pderiv (product w N)))) ((product_derivative_coeff_pin w N).pderiv.pderiv.symm))
        (product_third_moment_pin hw0 hw1 hx N)))
      (normalized_mul (SU2PointwiseHeatPositiveCompletion.inverseNome w*HalfPow.half)
        (ThetaConv.Ppart w x N) ((firstMoment w x N*firstMoment w x N)*firstMoment w x N +
          -((3*firstMoment w x N)*secondMoment w x N) + 2*thirdMoment w x N)))

def heatRadialExpression (w x C : Q') (N : Nat) : Q' :=
  let h := QPoly.eval (heat w N) (1+x)
  let hx := QPoly.eval (pderiv (heat w N)) (1+x)
  let hxx := QPoly.eval (pderiv (pderiv (heat w N))) (1+x)
  C*(h*h)+radialA x*(h*hxx + -(hx*hx)) + -(x*(h*hx))

/-- Exact radial expression of the actual normalized heat jets. -/
theorem heat_radial_moment_pin {w x : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hx : (-1 : Q') ≤ x) (C : Q') (N : Nat) :
    heatRadialExpression w x C N ≈
      (normalizedProduct w x N*normalizedProduct w x N)*
        (C*(firstMoment w x N*firstMoment w x N)+radialNumerator (HKConv.sTerm w x) N x) := by
  have h := heat_eval_moment_pin hw0 hw1 hx N
  have h1 := heat_first_moment_pin hw0 hw1 hx N
  have h2 := heat_second_moment_pin hw0 hw1 hx N
  have hsub := add_congr
    (add_congr (mul_congr (Q'.eqv_refl C) (mul_congr h h))
      (mul_congr (Q'.eqv_refl (radialA x)) (add_congr (mul_congr h h2) (neg_congr (mul_congr h1 h1)))))
    (neg_congr (mul_congr (Q'.eqv_refl x) (mul_congr h h1)))
  let a : PolyExpr := .var 0
  let s : PolyExpr := .var 1
  let t : PolyExpr := .var 2
  let u : PolyExpr := .var 3
  let hh : PolyExpr := .mul a s
  let hd : PolyExpr := .mul a (.add (.mul s s) (.neg t))
  let hdd : PolyExpr := .mul a
    (.add (.add (.mul (.mul s s) s) (.neg (.mul (.mul (.const 3) s) t))) (.mul (.const 2) u))
  let numerator : PolyExpr :=
    .add (.mul (.var 5) (.add (.add (.mul (.mul (.const 2) s) u) (.neg (.mul t t)))
      (.neg (.mul (.mul s s) t))))
      (.mul (.var 6) (.add (.mul s t) (.neg (.mul (.mul s s) s))))
  exact Q'.eqv_trans _ _ _ hsub (poly_identity_of_normal_eq
    (.add (.add (.mul (.var 4) (.mul hh hh))
      (.mul (.var 5) (.add (.mul hh hdd) (.neg (.mul hd hd)))))
      (.neg (.mul (.var 6) (.mul hh hd))))
    (.mul (.mul a a) (.add (.mul (.var 4) (.mul s s)) numerator))
    (by decide) (fun
      | 0 => normalizedProduct w x N
      | 1 => firstMoment w x N
      | 2 => secondMoment w x N
      | 3 => thirdMoment w x N
      | 4 => C
      | 5 => radialA x
      | _ => x))

/-- Scalar consumer of the explicit PRODUCT ceiling. This is not a producer
of that ceiling or an original-Haar certificate. No density is inverted. -/
theorem heat_radial_nonnegative_of_productCost {w x : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hx : (-1 : Q') ≤ x) (C : Q') (N : Nat)
    (hC : (0 : Q') ≤ C) (hxx : x*x ≤ (1 : Q'))
    (hD : productRadialCost (HKConv.sTerm w x) N x ≤ C) :
    (0 : Q') ≤ heatRadialExpression w x C N := by
  have hpayment := radialMixture_payment_nonneg (HKConv.sTerm w x) N x C
    (fun i _ => HKConv.sTerm_nonneg hw0 hw1 hx i) hC (Q'.sub_nonneg_of_le hxx) hD
  exact Q'.le_trans' _ _ _
    (Q'.mul_nonneg _ _ (SumOfSquares.q_mul_self_nonneg (normalizedProduct w x N)) hpayment)
    (Q'.ge_of_eqv (heat_radial_moment_pin hw0 hw1 hx C N))

end YMGap.Continuum.JacobiHeatRadialMomentJets

#print axioms YMGap.Continuum.JacobiHeatRadialMomentJets.product_derivative_coeff_pin
#print axioms YMGap.Continuum.JacobiHeatRadialMomentJets.product_first_moment_pin
#print axioms YMGap.Continuum.JacobiHeatRadialMomentJets.product_second_moment_pin
#print axioms YMGap.Continuum.JacobiHeatRadialMomentJets.product_third_moment_pin
#print axioms YMGap.Continuum.JacobiHeatRadialMomentJets.heat_eval_moment_pin
#print axioms YMGap.Continuum.JacobiHeatRadialMomentJets.heat_first_moment_pin
#print axioms YMGap.Continuum.JacobiHeatRadialMomentJets.heat_second_moment_pin
#print axioms YMGap.Continuum.JacobiHeatRadialMomentJets.heat_radial_moment_pin
#print axioms YMGap.Continuum.JacobiHeatRadialMomentJets.heat_radial_nonnegative_of_productCost
