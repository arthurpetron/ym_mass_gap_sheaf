/-
# Log concavity of the ACTUAL finite normalized Jacobi heat

Appending an affine factor with nonnegative slope preserves three positive
polynomial discriminants. Their coefficient pins use the actual first three
formal derivatives of the existing Jacobi product. The last discriminant is
the log-concavity numerator of its derivative, hence of the correctly
inverse-nome/half-normalized heat. All prefixes, including zero and one,
are retained. No heat floor or reciprocal density is used.

This is a scalar substituted Haar certificate, not an intrinsic angular,
original unweighted-prefix, conditional-score, OS or scaling theorem.
-/

import YMGap.Continuum.JacobiHeatRadialMomentJets
import YMGap.Continuum.ChebyshevFormalJets

namespace YMGap.Continuum.JacobiHeatLogConcavity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyCoefficientEvaluation (coefficient_eval)
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QPolyHaarPositiveSubstitution
open YMGap.Continuum.QPolyRatPolySubstitutionAlgebra
open YMGap.Continuum.JTPFullProductDerivativeNormalization (gFacDx)
open YMGap.Continuum.JacobiShiftedPositiveCoefficients
open YMGap.Continuum.JacobiHeatRadialMomentJets (product_derivative_coeff_pin)
open YMGap.Continuum.ChebyshevFormalJets (coefficients_of_eval_eqv)

local infix:50 " ≈ " => Q'.eqv

private theorem add_congr {a b c d : Q'} (h : a ≈ b) (g : c ≈ d) : a+c ≈ b+d :=
  QPoly.q_add_congr h g

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (g : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ g)

private theorem neg_congr {a b : Q'} (h : a ≈ b) : -a ≈ -b :=
  Q'.neg_eqv_congr _ _ h

private theorem singleton_mul_scale (b : Q') (p : Poly) :
    CoeffEqv (pmul p [b]) (pscale b p) := by
  apply (coeffEqv_pmul_comm p [b]).trans
  intro i
  have hz : QPolyCoefficient.coeff [(0 : Q')] i ≈ 0 := by
    cases i <;> exact Q'.eqv_refl 0
  exact Q'.eqv_trans _ _ _ (QPolyCoefficient.coeff_padd i (pscale b p) [(0 : Q')])
    (Q'.eqv_trans _ _ _ (add_congr (Q'.eqv_refl _) hz) (QPoly.q_add_zero_eqv _))

private theorem affine_derivative_coeff (p : Poly) (a b : Q') :
    CoeffEqv (pderiv (pmul p [a,b]))
      (padd (pmul (pderiv p) [a,b]) (pscale b p)) := by
  have hf : CoeffEqv (pderiv [a,b]) [b] := by
    intro i
    cases i with
    | zero => exact Q'.one_mul_eqv b
    | succ i => exact Q'.eqv_refl 0
  exact (pderiv_pmul p [a,b]).trans
    ((CoeffEqv.refl _).padd
      (((CoeffEqv.refl p).pmul hf).trans (singleton_mul_scale b p)))

private theorem eval_derivative_add (p q : Poly) (y : Q') :
    eval (pderiv (padd p q)) y ≈ eval (pderiv p) y+eval (pderiv q) y :=
  Q'.eqv_trans _ _ _ (coefficient_eval (pderiv_padd p q) y) (eval_padd _ _ y)

private theorem eval_derivative_scale (a : Q') (p : Poly) (y : Q') :
    eval (pderiv (pscale a p)) y ≈ a*eval (pderiv p) y :=
  Q'.eqv_trans _ _ _ (coefficient_eval (pderiv_pscale a p) y) (eval_pscale a _ y)

private theorem eval_second_add (p q : Poly) (y : Q') :
    eval (pderiv (pderiv (padd p q))) y ≈
      eval (pderiv (pderiv p)) y+eval (pderiv (pderiv q)) y :=
  Q'.eqv_trans _ _ _ (coefficient_eval (pderiv_padd p q).pderiv y)
    (eval_derivative_add (pderiv p) (pderiv q) y)

private theorem eval_second_scale (a : Q') (p : Poly) (y : Q') :
    eval (pderiv (pderiv (pscale a p))) y ≈ a*eval (pderiv (pderiv p)) y :=
  Q'.eqv_trans _ _ _ (coefficient_eval (pderiv_pscale a p).pderiv y)
    (eval_derivative_scale a (pderiv p) y)

private theorem affine_first (p : Poly) (a b y : Q') :
    eval (pderiv (pmul p [a,b])) y ≈
      eval (pderiv p) y*eval [a,b] y+eval p y*b :=
  Q'.eqv_trans _ _ _ (coefficient_eval (affine_derivative_coeff p a b) y)
    (Q'.eqv_trans _ _ _ (eval_padd _ _ y)
      (add_congr (eval_pmul _ _ y)
        (Q'.eqv_trans _ _ _ (eval_pscale b p y) (Q'.mul_comm_eqv _ _))))

private theorem affine_second (p : Poly) (a b y : Q') :
    eval (pderiv (pderiv (pmul p [a,b]))) y ≈
      eval (pderiv (pderiv p)) y*eval [a,b] y+(2*eval (pderiv p) y)*b := by
  have h := Q'.eqv_trans _ _ _
    (coefficient_eval (affine_derivative_coeff p a b).pderiv y)
    (Q'.eqv_trans _ _ _ (eval_derivative_add (pmul (pderiv p) [a,b]) (pscale b p) y)
      (add_congr (affine_first (pderiv p) a b y) (eval_derivative_scale b p y)))
  exact Q'.eqv_trans _ _ _ h (poly_identity_of_normal_eq
    (.add (.add (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))) (.mul (.var 3) (.var 2)))
    (.add (.mul (.var 0) (.var 1)) (.mul (.mul (.const 2) (.var 2)) (.var 3)))
    (by decide) (fun
      | 0 => eval (pderiv (pderiv p)) y
      | 1 => eval [a,b] y
      | 2 => eval (pderiv p) y
      | _ => b))

private theorem affine_third (p : Poly) (a b y : Q') :
    eval (pderiv (pderiv (pderiv (pmul p [a,b])))) y ≈
      eval (pderiv (pderiv (pderiv p))) y*eval [a,b] y+
        (3*eval (pderiv (pderiv p)) y)*b := by
  have h := Q'.eqv_trans _ _ _
    (coefficient_eval (affine_derivative_coeff p a b).pderiv.pderiv y)
    (Q'.eqv_trans _ _ _ (eval_second_add (pmul (pderiv p) [a,b]) (pscale b p) y)
      (add_congr (affine_second (pderiv p) a b y) (eval_second_scale b p y)))
  exact Q'.eqv_trans _ _ _ h (poly_identity_of_normal_eq
    (.add (.add (.mul (.var 0) (.var 1)) (.mul (.mul (.const 2) (.var 2)) (.var 3)))
      (.mul (.var 3) (.var 2)))
    (.add (.mul (.var 0) (.var 1)) (.mul (.mul (.const 3) (.var 2)) (.var 3)))
    (by decide) (fun
      | 0 => eval (pderiv (pderiv (pderiv p))) y
      | 1 => eval [a,b] y
      | 2 => eval (pderiv (pderiv p)) y
      | _ => b))

private def difference (p q r s : Poly) : Poly := psub (pmul p q) (pmul r s)

private theorem eval_difference (p q r s : Poly) (y : Q') :
    eval (difference p q r s) y ≈ eval p y*eval q y+ -(eval r y*eval s y) :=
  Q'.eqv_trans _ _ _ (eval_psub _ _ y)
    (add_congr (eval_pmul _ _ y) (neg_congr (eval_pmul _ _ y)))

/-- Positive recurrence representative for P'^2-P*P''. -/
def productLogDiscriminant (w : Q') : Nat → Poly
  | 0 => []
  | N+1 => padd
      (pmul (pmul (factor w N) (factor w N)) (productLogDiscriminant w N))
      (pscale (gFacDx w N*gFacDx w N) (pmul (product w N) (product w N)))

/-- Positive recurrence representative for P'*P''-P*P'''. -/
def productMixedDiscriminant (w : Q') : Nat → Poly
  | 0 => []
  | N+1 => padd
      (padd (pmul (pmul (factor w N) (factor w N)) (productMixedDiscriminant w N))
        (pscale (2*gFacDx w N) (pmul (factor w N) (productLogDiscriminant w N))))
      (pscale (2*(gFacDx w N*gFacDx w N)) (pmul (product w N) (derivative w N)))

/-- Positive recurrence representative for P''^2-P'*P'''. -/
def derivativeLogDiscriminant (w : Q') : Nat → Poly
  | 0 => []
  | N+1 => padd
      (padd (pmul (pmul (factor w N) (factor w N)) (derivativeLogDiscriminant w N))
        (pscale (gFacDx w N) (pmul (factor w N) (productMixedDiscriminant w N))))
      (pscale (gFacDx w N*gFacDx w N)
        (padd (pmul (derivative w N) (derivative w N)) (pscale 3 (productLogDiscriminant w N))))

private theorem eval_V_succ (w y : Q') (N : Nat) :
    eval (productLogDiscriminant w (N+1)) y ≈
      (eval (factor w N) y*eval (factor w N) y)*eval (productLogDiscriminant w N) y+
        (gFacDx w N*gFacDx w N)*(eval (product w N) y*eval (product w N) y) :=
  Q'.eqv_trans _ _ _ (eval_padd _ _ y)
    (add_congr (Q'.eqv_trans _ _ _ (eval_pmul _ _ y)
      (mul_congr (eval_pmul _ _ y) (Q'.eqv_refl _)))
      (Q'.eqv_trans _ _ _ (eval_pscale _ _ y) (mul_congr (Q'.eqv_refl _) (eval_pmul _ _ y))))

private theorem eval_W_succ (w y : Q') (N : Nat) :
    eval (productMixedDiscriminant w (N+1)) y ≈
      ((eval (factor w N) y*eval (factor w N) y)*eval (productMixedDiscriminant w N) y+
        (2*gFacDx w N)*(eval (factor w N) y*eval (productLogDiscriminant w N) y))+
        (2*(gFacDx w N*gFacDx w N))*(eval (product w N) y*eval (derivative w N) y) :=
  Q'.eqv_trans _ _ _ (eval_padd _ _ y)
    (add_congr (Q'.eqv_trans _ _ _ (eval_padd _ _ y)
      (add_congr (Q'.eqv_trans _ _ _ (eval_pmul _ _ y)
        (mul_congr (eval_pmul _ _ y) (Q'.eqv_refl _)))
        (Q'.eqv_trans _ _ _ (eval_pscale _ _ y) (mul_congr (Q'.eqv_refl _) (eval_pmul _ _ y)))))
      (Q'.eqv_trans _ _ _ (eval_pscale _ _ y) (mul_congr (Q'.eqv_refl _) (eval_pmul _ _ y))))

private theorem eval_D_succ (w y : Q') (N : Nat) :
    eval (derivativeLogDiscriminant w (N+1)) y ≈
      ((eval (factor w N) y*eval (factor w N) y)*eval (derivativeLogDiscriminant w N) y+
        gFacDx w N*(eval (factor w N) y*eval (productMixedDiscriminant w N) y))+
        (gFacDx w N*gFacDx w N)*
          (eval (derivative w N) y*eval (derivative w N) y+3*eval (productLogDiscriminant w N) y) :=
  Q'.eqv_trans _ _ _ (eval_padd _ _ y)
    (add_congr (Q'.eqv_trans _ _ _ (eval_padd _ _ y)
      (add_congr (Q'.eqv_trans _ _ _ (eval_pmul _ _ y)
        (mul_congr (eval_pmul _ _ y) (Q'.eqv_refl _)))
        (Q'.eqv_trans _ _ _ (eval_pscale _ _ y) (mul_congr (Q'.eqv_refl _) (eval_pmul _ _ y)))))
      (Q'.eqv_trans _ _ _ (eval_pscale _ _ y)
        (mul_congr (Q'.eqv_refl _) (Q'.eqv_trans _ _ _ (eval_padd _ _ y)
          (add_congr (eval_pmul _ _ y) (eval_pscale _ _ y))))))

private def vExpr (P H J : PolyExpr) : PolyExpr := .add (.mul H H) (.neg (.mul P J))
private def wExpr (P H J K : PolyExpr) : PolyExpr := .add (.mul H J) (.neg (.mul P K))
private def dExpr (H J K : PolyExpr) : PolyExpr := .add (.mul J J) (.neg (.mul H K))

/-- The positive recurrence polynomials equal the ACTUAL formal-jet
discriminants, coefficientwise and at every prefix. No jet is supplied. -/
theorem product_discriminants_formal_pin (w : Q') : ∀ N,
    let P := product w N
    let H := pderiv P
    let J := pderiv H
    let K := pderiv J
    CoeffEqv (productLogDiscriminant w N) (difference H H P J) ∧
      CoeffEqv (productMixedDiscriminant w N) (difference H J P K) ∧
      CoeffEqv (derivativeLogDiscriminant w N) (difference J J H K)
  | 0 => by
      constructor
      · intro i; cases i <;> exact Q'.eqv_refl 0
      · constructor <;> intro i <;> cases i <;> exact Q'.eqv_refl 0
  | N+1 => by
      let P := product w N
      let H := pderiv P
      let J := pderiv H
      let K := pderiv J
      let F := factor w N
      let beta := gFacDx w N
      have ih := product_discriminants_formal_pin w N
      have hP (y : Q') : eval (product w (N+1)) y ≈ eval P y*eval F y := eval_pmul P F y
      have hH (y : Q') : eval (pderiv (product w (N+1))) y ≈
          eval H y*eval F y+eval P y*beta := affine_first P (base w N) beta y
      have hJ (y : Q') : eval (pderiv (pderiv (product w (N+1)))) y ≈
          eval J y*eval F y+(2*eval H y)*beta := affine_second P (base w N) beta y
      have hK (y : Q') : eval (pderiv (pderiv (pderiv (product w (N+1))))) y ≈
          eval K y*eval F y+(3*eval J y)*beta := affine_third P (base w N) beta y
      have hd (y : Q') : eval (derivative w N) y ≈ eval H y :=
        coefficient_eval (product_derivative_coeff_pin w N).symm y
      let p : PolyExpr := .var 0
      let h : PolyExpr := .var 1
      let j : PolyExpr := .var 2
      let k : PolyExpr := .var 3
      let f : PolyExpr := .var 4
      let b : PolyExpr := .var 5
      let pp : PolyExpr := .mul p f
      let hh : PolyExpr := .add (.mul h f) (.mul p b)
      let jj : PolyExpr := .add (.mul j f) (.mul (.mul (.const 2) h) b)
      let kk : PolyExpr := .add (.mul k f) (.mul (.mul (.const 3) j) b)
      let env (y : Q') : Nat → Q' := fun
        | 0 => eval P y
        | 1 => eval H y
        | 2 => eval J y
        | 3 => eval K y
        | 4 => eval F y
        | _ => beta
      have hv (y : Q') : eval (productLogDiscriminant w N) y ≈
          eval H y*eval H y+ -(eval P y*eval J y) :=
        Q'.eqv_trans _ _ _ (coefficient_eval ih.1 y) (eval_difference H H P J y)
      have hw (y : Q') : eval (productMixedDiscriminant w N) y ≈
          eval H y*eval J y+ -(eval P y*eval K y) :=
        Q'.eqv_trans _ _ _ (coefficient_eval ih.2.1 y) (eval_difference H J P K y)
      have he (y : Q') : eval (derivativeLogDiscriminant w N) y ≈
          eval J y*eval J y+ -(eval H y*eval K y) :=
        Q'.eqv_trans _ _ _ (coefficient_eval ih.2.2 y) (eval_difference J J H K y)
      constructor
      · apply coefficients_of_eval_eqv
        intro y
        have hr := Q'.eqv_trans _ _ _ (eval_V_succ w y N)
          (add_congr (mul_congr (Q'.eqv_refl _) (hv y)) (Q'.eqv_refl _))
        have ha := poly_identity_of_normal_eq
          (.add (.mul (.mul f f) (vExpr p h j)) (.mul (.mul b b) (.mul p p)))
          (vExpr pp hh jj) (by decide) (env y)
        have ht := Q'.eqv_trans _ _ _
          (eval_difference (pderiv (product w (N+1))) (pderiv (product w (N+1)))
            (product w (N+1)) (pderiv (pderiv (product w (N+1)))) y)
          (add_congr (mul_congr (hH y) (hH y)) (neg_congr (mul_congr (hP y) (hJ y))))
        exact Q'.eqv_trans _ _ _ (Q'.eqv_trans _ _ _ hr ha) (Q'.eqv_symm ht)
      · constructor
        · apply coefficients_of_eval_eqv
          intro y
          have hr := Q'.eqv_trans _ _ _ (eval_W_succ w y N)
            (add_congr (add_congr (mul_congr (Q'.eqv_refl _) (hw y))
              (mul_congr (Q'.eqv_refl _) (mul_congr (Q'.eqv_refl _) (hv y))))
              (mul_congr (Q'.eqv_refl _) (mul_congr (Q'.eqv_refl _) (hd y))))
          have ha := poly_identity_of_normal_eq
            (.add (.add (.mul (.mul f f) (wExpr p h j k))
              (.mul (.mul (.const 2) b) (.mul f (vExpr p h j))))
              (.mul (.mul (.const 2) (.mul b b)) (.mul p h)))
            (wExpr pp hh jj kk) (by decide) (env y)
          have ht := Q'.eqv_trans _ _ _
            (eval_difference (pderiv (product w (N+1))) (pderiv (pderiv (product w (N+1))))
              (product w (N+1)) (pderiv (pderiv (pderiv (product w (N+1))))) y)
            (add_congr (mul_congr (hH y) (hJ y)) (neg_congr (mul_congr (hP y) (hK y))))
          exact Q'.eqv_trans _ _ _ (Q'.eqv_trans _ _ _ hr ha) (Q'.eqv_symm ht)
        · apply coefficients_of_eval_eqv
          intro y
          have hr := Q'.eqv_trans _ _ _ (eval_D_succ w y N)
            (add_congr (add_congr (mul_congr (Q'.eqv_refl _) (he y))
              (mul_congr (Q'.eqv_refl _) (mul_congr (Q'.eqv_refl _) (hw y))))
              (mul_congr (Q'.eqv_refl _) (add_congr (mul_congr (hd y) (hd y))
                (mul_congr (Q'.eqv_refl _) (hv y)))))
          have ha := poly_identity_of_normal_eq
            (.add (.add (.mul (.mul f f) (dExpr h j k)) (.mul b (.mul f (wExpr p h j k))))
              (.mul (.mul b b) (.add (.mul h h) (.mul (.const 3) (vExpr p h j)))))
            (dExpr hh jj kk) (by decide) (env y)
          have ht := Q'.eqv_trans _ _ _
            (eval_difference (pderiv (pderiv (product w (N+1)))) (pderiv (pderiv (product w (N+1))))
              (pderiv (product w (N+1))) (pderiv (pderiv (pderiv (product w (N+1))))) y)
            (add_congr (mul_congr (hJ y) (hJ y)) (neg_congr (mul_congr (hH y) (hK y))))
          exact Q'.eqv_trans _ _ _ (Q'.eqv_trans _ _ _ hr ha) (Q'.eqv_symm ht)

/-- All three recurrence representatives have nonnegative coefficients,
including the zero-polynomial initial discriminants. -/
theorem discriminants_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    ∀ N, nonnegCoeffs (productLogDiscriminant w N) ∧
      nonnegCoeffs (productMixedDiscriminant w N) ∧
      nonnegCoeffs (derivativeLogDiscriminant w N)
  | 0 => ⟨rfl,rfl,rfl⟩
  | N+1 => by
      have ih := discriminants_nonnegative hw0 hw1 N
      have hF := factor_nonnegative hw0 hw1 N
      have hP := product_nonnegative hw0 hw1 N
      have hH := derivative_nonnegative hw0 hw1 N
      have hb := Q'.le_of_lt (slope_pos hw0 hw1 N)
      have hbb := Q'.mul_nonneg _ _ hb hb
      have htwo := Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2) hb
      have htwobb := Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2) hbb
      constructor
      · exact nonnegCoeffsB_padd _ _
          (nonnegCoeffs_pmul (nonnegCoeffs_pmul hF hF) ih.1)
          (nonnegCoeffsB_pscale hbb _ (nonnegCoeffs_pmul hP hP))
      · constructor
        · exact nonnegCoeffsB_padd _ _
            (nonnegCoeffsB_padd _ _ (nonnegCoeffs_pmul (nonnegCoeffs_pmul hF hF) ih.2.1)
              (nonnegCoeffsB_pscale htwo _ (nonnegCoeffs_pmul hF ih.1)))
            (nonnegCoeffsB_pscale htwobb _ (nonnegCoeffs_pmul hP hH))
        · exact nonnegCoeffsB_padd _ _
            (nonnegCoeffsB_padd _ _ (nonnegCoeffs_pmul (nonnegCoeffs_pmul hF hF) ih.2.2)
              (nonnegCoeffsB_pscale hb _ (nonnegCoeffs_pmul hF ih.2.1)))
            (nonnegCoeffsB_pscale hbb _ (nonnegCoeffsB_padd _ _ (nonnegCoeffs_pmul hH hH)
              (nonnegCoeffsB_pscale (by decide : (0 : Q') ≤ 3) _ ih.1)))

private theorem subst_formalCoeffEqv (z : RatPoly) (p q : Poly)
    (h : CoeffEqv p q) : RatPolyCoeffEqv (subst z p) (subst z q) :=
  subst_polyEqv z (fun x => coefficient_eval h x)

private theorem subst_difference (z : RatPoly) (p q r s : Poly) :
    RatPolyCoeffEqv (subst z (difference p q r s))
      (polyAdd (polyMul (subst z p) (subst z q))
        (polyNeg (polyMul (subst z r) (subst z s)))) :=
  (subst_padd z (pmul p q) (pneg (pmul r s))).trans
    ((subst_pmul z p q).add
      ((subst_pscale z (-1) (pmul r s)).trans
        ((neg_smul (subst z (pmul r s))).symm.trans
          (RatPolyCoeffEqv.neg (subst_pmul z r s)))))

private theorem mul_scales (a b : Q') (p q : RatPoly) :
    RatPolyCoeffEqv (polyMul (polySmul a p) (polySmul b q))
      (polySmul (a*b) (polyMul p q)) :=
  (RatPolyCoeffEqv.polyMul_smul_left a p (polySmul b q)).trans
    (((RatPolyCoeffEqv.polyMul_smul_right b p q).smul a).trans
      (RatPolyCoeffEqv.smul_assoc a b (polyMul p q)))

private theorem neg_scale (a : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polyNeg (polySmul a p)) (polySmul a (polyNeg p)) :=
  (neg_smul (polySmul a p)).trans
    ((RatPolyCoeffEqv.smul_assoc (-1) a p).trans
      ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv (-1) a) p).trans
        ((RatPolyCoeffEqv.smul_assoc a (-1) p).symm.trans ((neg_smul p).symm.smul a))))

/-- Literal formal first/second derivative discriminant of the normalized
finite heat is certified on the SAME original Haar carrier. -/
def heat_logConcavity_certificate {blocks : Nat} {X : RatPoly} {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (HX : Interval blocks X 1) (N : Nat) :
    let h := subst (polyAdd polyOne X) (heat w N)
    let hx := subst (polyAdd polyOne X) (pderiv (heat w N))
    let hxx := subst (polyAdd polyOne X) (pderiv (pderiv (heat w N)))
    Certificate blocks (polyAdd (polyMul hx hx) (polyNeg (polyMul h hxx))) := by
  let z := polyAdd polyOne X
  let a := SU2PointwiseHeatPositiveCompletion.inverseNome w*HalfPow.half
  let P := product w N
  let H := pderiv P
  let J := pderiv H
  let K := pderiv J
  let Z : Certificate blocks z :=
    .ofCoeff ((RatPolyCoeffEqv.one_smul polyOne).symm.add (.refl X)) HX.lower
  let D := certificate Z (derivativeLogDiscriminant w N)
    (discriminants_nonnegative hw0 hw1 N).2.2
  have hd := (product_discriminants_formal_pin w N).2.2
  have hD : Certificate blocks
      (polyAdd (polyMul (subst z J) (subst z J))
        (polyNeg (polyMul (subst z H) (subst z K)))) :=
    .ofCoeff ((subst_formalCoeffEqv z _ _ hd).trans (subst_difference z J J H K)).symm D
  have hh : RatPolyCoeffEqv (subst z (heat w N)) (polySmul a (subst z H)) :=
    (subst_pscale z a (derivative w N)).trans
      ((subst_formalCoeffEqv z _ _ (product_derivative_coeff_pin w N).symm).smul a)
  have hx : RatPolyCoeffEqv (subst z (pderiv (heat w N))) (polySmul a (subst z J)) :=
    (subst_formalCoeffEqv z _ _ (pderiv_pscale a (derivative w N))).trans
      ((subst_pscale z a (pderiv (derivative w N))).trans
        ((subst_formalCoeffEqv z _ _ (product_derivative_coeff_pin w N).pderiv.symm).smul a))
  have hxx : RatPolyCoeffEqv (subst z (pderiv (pderiv (heat w N)))) (polySmul a (subst z K)) :=
    (subst_formalCoeffEqv z _ _ (pderiv_pscale a (derivative w N)).pderiv).trans
      ((subst_formalCoeffEqv z _ _ (pderiv_pscale a (pderiv (derivative w N)))).trans
        ((subst_pscale z a (pderiv (pderiv (derivative w N)))).trans
          ((subst_formalCoeffEqv z _ _ (product_derivative_coeff_pin w N).pderiv.pderiv.symm).smul a)))
  have halg : RatPolyCoeffEqv
      (polyAdd (polyMul (polySmul a (subst z J)) (polySmul a (subst z J)))
        (polyNeg (polyMul (polySmul a (subst z H)) (polySmul a (subst z K)))))
      (polySmul (a*a) (polyAdd (polyMul (subst z J) (subst z J))
        (polyNeg (polyMul (subst z H) (subst z K))))) := by
    have hl := mul_scales a a (subst z J) (subst z J)
    have hr := mul_scales a a (subst z H) (subst z K)
    exact (hl.add (RatPolyCoeffEqv.neg hr)).trans
      (((RatPolyCoeffEqv.refl _).add (neg_scale (a*a) (polyMul (subst z H) (subst z K)))).trans
        (RatPolyCoeffEqv.smul_add _ _ _).symm)
  exact .ofCoeff (((hx.mul hx).add (RatPolyCoeffEqv.neg (hh.mul hxx))).trans halg)
    (.smul (a*a) (SumOfSquares.q_mul_self_nonneg a) hD)

end YMGap.Continuum.JacobiHeatLogConcavity

#print axioms YMGap.Continuum.JacobiHeatLogConcavity.product_discriminants_formal_pin
#print axioms YMGap.Continuum.JacobiHeatLogConcavity.discriminants_nonnegative
#print axioms YMGap.Continuum.JacobiHeatLogConcavity.heat_logConcavity_certificate
