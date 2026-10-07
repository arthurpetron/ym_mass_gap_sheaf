/-
# Actual combined angular jet of the finite Jacobi product

The finite Euler-normalized Jacobi equality is reflected into padded
coefficient equality BEFORE differentiation. The shifted positive-coefficient
product and its actual formal derivatives are retained. Combining its second
and first jets multiplies each Chebyshev mode by -n^2, so the already-proved
quadratic Gaussian majorant pays the WHOLE angular comparison.

The cutoff is explicit and uniform in x on [-1,1] at a named 0<w<1.
It is not uniform as w approaches one. No completed addition identity,
radial ceiling, Haar certificate, or interacting/physical gap is asserted.
-/

import YMGap.Continuum.QPolyAffineJetTranslation
import YMGap.Continuum.JacobiShiftedPositiveCoefficients
import YMGap.Continuum.FiniteJacobiDerivativeComparison
import YMGap.Continuum.JacobiHeatRadialMomentJets

namespace YMGap.Continuum.FiniteJacobiAngularComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.RationalTail
open YMGap.Continuum.ChebyshevFormalJets
open YMGap.Continuum.QPolyAffineJetTranslation
open YMGap.Continuum.FiniteJacobiSeriesComparison
open YMGap.Continuum.FiniteJacobiDerivativeComparison
open YMGap.Continuum.FiniteJacobiCoefficients (amp)
open YMGap.Continuum.FiniteJacobiWeightConvergence (lossScale)
open YMGap.Continuum.GaussQBinomEulerQuotient (centeredWeight)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem add_congr {a b c d : Q'} (h : a ≈ b) (g : c ≈ d) : a+c ≈ b+d :=
  QPoly.q_add_congr h g

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (g : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ g)

private theorem neg_num_cast (a : Q') : (-a).num = -a.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero]; ac_rfl))

/-- Literal first/second formal polynomial jets, combined without division. -/
def angularEval (p : Poly) (x : Q') : Q' :=
  (1 + -(x*x))*eval (pderiv (pderiv p)) x + -(x*eval (pderiv p) x)

/-- Actual finite symmetric polynomial, including its constant term. -/
def seriesPoly (a : Nat → Q') : Nat → Poly
  | 0 => [a 0]
  | N+1 => padd (seriesPoly a N) (pscale (2*a (N+1)) (Tpoly (N+1)))

/-- The angular series retains -n^2 on every nonconstant mode. -/
def angularSum (a : Nat → Q') (x : Q') : Nat → Q'
  | 0 => 0
  | N+1 => angularSum a x N +
      -(2*a (N+1)*(Q'.ofNat (N+1)*Q'.ofNat (N+1))*Cheb.T (N+1) x)

theorem eval_seriesPoly (a : Nat → Q') (x : Q') : ∀ N,
    eval (seriesPoly a N) x ≈ FiniteSymmetricChebyshev.sum a x N
  | 0 => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.mul_zero_eqv x)) (QPoly.q_add_zero_eqv _)
  | N+1 => Q'.eqv_trans _ _ _ (eval_padd _ _ x)
      (add_congr (eval_seriesPoly a x N)
        (Q'.eqv_trans _ _ _ (eval_pscale _ _ x)
          (Q'.mul_eqv_congr_left _ _ _ (eval_Tpoly (N+1) x))))

private theorem angular_congr {p q : Poly} (h : CoeffEqv p q) (x : Q') :
    angularEval p x ≈ angularEval q x :=
  add_congr
    (Q'.mul_eqv_congr_left _ _ _ (QPolyCoefficientEvaluation.coefficient_eval h.pderiv.pderiv x))
    (Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_left _ _ _ (QPolyCoefficientEvaluation.coefficient_eval h.pderiv x)))

private theorem angular_add (p q : Poly) (x : Q') :
    angularEval (padd p q) x ≈ angularEval p x + angularEval q x := by
  have h1 := Q'.eqv_trans _ _ _
    (QPolyCoefficientEvaluation.coefficient_eval (pderiv_padd p q) x) (eval_padd _ _ x)
  have h2 := Q'.eqv_trans _ _ _
    (QPolyCoefficientEvaluation.coefficient_eval (pderiv_padd p q).pderiv x)
    (Q'.eqv_trans _ _ _
      (QPolyCoefficientEvaluation.coefficient_eval (pderiv_padd (pderiv p) (pderiv q)) x)
      (eval_padd _ _ x))
  exact Q'.eqv_trans _ _ _
    (add_congr (Q'.mul_eqv_congr_left _ _ _ h2)
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ h1))) (by
        unfold angularEval
        ring_qeqv)

private theorem angular_scale (c : Q') (p : Poly) (x : Q') :
    angularEval (pscale c p) x ≈ c*angularEval p x := by
  have h1 := Q'.eqv_trans _ _ _
    (QPolyCoefficientEvaluation.coefficient_eval (pderiv_pscale c p) x) (eval_pscale _ _ x)
  have h2 := Q'.eqv_trans _ _ _
    (QPolyCoefficientEvaluation.coefficient_eval (pderiv_pscale c p).pderiv x)
    (Q'.eqv_trans _ _ _
      (QPolyCoefficientEvaluation.coefficient_eval (pderiv_pscale c (pderiv p)) x)
      (eval_pscale _ _ x))
  exact Q'.eqv_trans _ _ _
    (add_congr (Q'.mul_eqv_congr_left _ _ _ h2)
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ h1))) (by
        unfold angularEval
        ring_qeqv)

/-- Actual angular differentiation of the whole finite coefficient list. -/
theorem angular_seriesPoly (a : Nat → Q') (x : Q') : ∀ N,
    angularEval (seriesPoly a N) x ≈ angularSum a x N
  | 0 => poly_identity_of_normal_eq
      (.add (.mul (.add (.const 1) (.neg (.mul (.var 0) (.var 0)))) (.const 0))
        (.neg (.mul (.var 0) (.const 0)))) (.const 0) (by decide) (fun _ => x)
  | N+1 => by
      have ht := Q'.eqv_trans _ _ _ (formal_angular_ode (N+1) x)
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_left _ _ _ (eval_Tpoly (N+1) x)))
      exact Q'.eqv_trans _ _ _ (angular_add _ _ x)
        (Q'.eqv_trans _ _ _
          (add_congr (angular_seriesPoly a x N)
            (Q'.eqv_trans _ _ _ (angular_scale (2*a (N+1)) _ x)
              (Q'.mul_eqv_congr_left _ _ _ ht))) (by
                change (angularSum a x N + (2*a (N+1))*
                  (-(Q'.ofNat (N+1)*Q'.ofNat (N+1)*Cheb.T (N+1) x))) ≈
                    angularSum a x N +
                      -(2*a (N+1)*(Q'.ofNat (N+1)*Q'.ofNat (N+1))*Cheb.T (N+1) x)
                ring_qeqv))

/-- The already-used shifted Jacobi product's ACTUAL combined jets. -/
def productAngularJet (w x : Q') (N : Nat) : Q' :=
  (1 + -(x*x))*eval (pderiv (pderiv (JacobiShiftedPositiveCoefficients.product w N))) (1+x) +
    -(x*eval (pderiv (JacobiShiftedPositiveCoefficients.product w N)) (1+x))

/-- Actual all-point finite Jacobi equality reflected into coefficients. -/
theorem product_series_coeff_pin {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (N : Nat) :
    CoeffEqv (translate 1 (JacobiShiftedPositiveCoefficients.product w N))
      (seriesPoly (fun j => w^(j*j)*centeredWeight (w*w) N j) N) :=
  coefficients_of_eval_eqv _ _ (fun x => Q'.eqv_trans _ _ _ (eval_translate _ _ x)
    (Q'.eqv_trans _ _ _ (JacobiShiftedPositiveCoefficients.eval_product w x N)
      (Q'.eqv_trans _ _ _ (FiniteJacobiIdentity.Ppart_eq_finiteJacobi hw0 hw1 x N)
        (Q'.eqv_symm (eval_seriesPoly _ x N)))))

/-- No supplied second-jet pin: the ORIGINAL polynomial is differentiated
only after its padded coefficients have been identified. -/
theorem productAngularJet_pin {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (x : Q') (N : Nat) :
    productAngularJet w x N ≈
      angularSum (fun j => w^(j*j)*centeredWeight (w*w) N j) x N := by
  have ht : angularEval (translate 1 (JacobiShiftedPositiveCoefficients.product w N)) x ≈
      productAngularJet w x N :=
    add_congr (Q'.mul_eqv_congr_left _ _ _ (eval_translate_second_derivative _ _ x))
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ (eval_translate_derivative _ _ x)))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm ht)
    (Q'.eqv_trans _ _ _ (angular_congr (product_series_coeff_pin hw0 hw1 N) x)
      (angular_seriesPoly _ x N))

private theorem angularSum_congr (a b : Nat → Q') (x : Q') (N : Nat)
    (h : ∀ j, a j ≈ b j) : angularSum a x N ≈ angularSum b x N := by
  induction N with
  | zero => exact Q'.eqv_refl 0
  | succ N ih =>
      exact add_congr ih
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_right _ _ _
            (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_left _ _ _ (h (N+1))))))

private theorem angularSum_sub (a b : Nat → Q') (x : Q') : ∀ N,
    angularSum a x N + -angularSum b x N ≈ angularSum (fun j => a j + -b j) x N
  | 0 => by
      change (0 : Q') + -0 ≈ 0
      decide
  | N+1 => Q'.eqv_trans _ _ _ (by
      rw [angularSum, angularSum]
      show _ ≈ (angularSum a x N + -angularSum b x N) +
        -(2*(a (N+1) + -b (N+1))*(Q'.ofNat (N+1)*Q'.ofNat (N+1))*Cheb.T (N+1) x)
      ring_qeqv) (add_congr (angularSum_sub a b x N) (Q'.eqv_refl _))

/-- Exact signed angular error, retaining the finite coefficient deficit. -/
theorem productAngularJet_sub_bare_pin {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (x : Q') (N : Nat) :
    productAngularJet w x N + -angularSum (fun j => w^(j*j)) x N ≈
      angularSum (coefficientError w N) x N :=
  Q'.eqv_trans _ _ _ (add_congr (productAngularJet_pin hw0 hw1 x N) (Q'.eqv_refl _))
    (Q'.eqv_trans _ _ _ (angularSum_sub _ _ x N)
      (angularSum_congr _ _ x N (fun j => by
        unfold coefficientError
        ring_qeqv)))

private theorem abs_mul_bound {a b A B : Q'} (ha : Q'.abs a ≤ A) (hb : Q'.abs b ≤ B) :
    Q'.abs (a*b) ≤ A*B :=
  Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le a b)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ ha (Q'.abs_nonneg _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hb
        (Q'.le_trans' _ _ _ (Q'.abs_nonneg _) ha)))

private theorem angular_error_term_le {w x : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x)
    (N r : Nat) (hr : r+1 ≤ N) :
    Q'.abs (-(2*coefficientError w N (r+1)*(Q'.ofNat (r+1)*Q'.ofNat (r+1))*Cheb.T (r+1) x)) ≤
      (2*errorAmplitude w N*shiftedGaussianScale w)*w^r := by
  have hs := Q'.mul_nonneg _ _ (JTPIdentity.ofNat_nonneg (r+1)) (JTPIdentity.ofNat_nonneg (r+1))
  have hT := ChebU.Tabs_le_one r x hx1 hxm1
  have h := abs_mul_bound
    (abs_mul_bound
      (abs_mul_bound (by decide : Q'.abs (2 : Q') ≤ 2)
        (coefficientError_succ_le_gaussian hw0 hw1 N r hr))
      (Q'.le_of_eqv (Q'.eqv_of_eq (ExpNeg.abs_of_nonneg hs))))
    (Q'.abs_le hT.1 hT.2)
  have he : (2*(errorAmplitude w N*w^(r*r)))*(Q'.ofNat (r+1)*Q'.ofNat (r+1))*1 ≈
      (2*errorAmplitude w N)*((Q'.ofNat (r+1)*Q'.ofNat (r+1))*w^(r*r)) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) ?_
    ring_qeqv
  have hfinal := Q'.le_trans' _ _ _ h
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (shiftedGaussian_le hw0 hw1 r)
          (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2)
            (errorAmplitude_nonnegative (Q'.le_of_lt hw0) N)))
        (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' _)) hfinal

private theorem angularSum_abs_le_sum (a : Nat → Q') (w K x : Q') (M : Nat)
    (h : ∀ r, r < M →
      Q'.abs (-(2*a (r+1)*(Q'.ofNat (r+1)*Q'.ofNat (r+1))*Cheb.T (r+1) x)) ≤ K*w^r) :
    Q'.abs (angularSum a x M) ≤ K*finSum (fun r => w^r) M := by
  induction M with
  | zero => exact Q'.ge_of_eqv (Q'.mul_zero_eqv K)
  | succ M ih =>
      exact Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _)
        (Q'.le_trans' _ _ _
          (Q'.add_le_add (ih (fun r hr => h r (by omega))) (h M (by omega)))
          (Q'.ge_of_eqv (Q'.mul_add_eqv _ _ _)))

/-- Whole ACTUAL combined jet comparison, with explicit nome dependence. -/
theorem productAngularJet_sub_bare_le {w x : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x) (N : Nat) :
    Q'.abs (productAngularJet w x N + -angularSum (fun j => w^(j*j)) x N) ≤
      derivativeScale w*amp w N := by
  have hs := angularSum_abs_le_sum (coefficientError w N) w
    (2*errorAmplitude w N*shiftedGaussianScale w) x N
    (fun r hr => angular_error_term_le hw0 hw1 hx1 hxm1 N r (by omega))
  have hK := Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2)
      (errorAmplitude_nonnegative (Q'.le_of_lt hw0) N))
    (shiftedGaussianScale_nonnegative hw0 hw1)
  have he : (2*errorAmplitude w N*shiftedGaussianScale w)*HKConv.divPos 1 (1 + -w) ≈
      derivativeScale w*amp w N := by
    unfold derivativeScale errorAmplitude
    ring_qeqv
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr (productAngularJet_sub_bare_pin hw0 hw1 x N)))
    (Q'.le_trans' _ _ _ hs
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (HKConvGen.geom_series_le_base hw0 hw1 N) hK)
        (Q'.le_of_eqv he)))

/-- Existing constructive cutoff reused for the actual angular comparison;
the constant mode/empty prefix and both interval endpoints are included. -/
theorem productAngularJet_sub_bare_close {w x : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x)
    {ε : Q'} (hε : (0 : Q') < ε) (N : Nat) (hN : derivativeCutoff w ε ≤ N) :
    Q'.abs (productAngularJet w x N + -angularSum (fun j => w^(j*j)) x N) ≤ ε :=
  Q'.le_trans' _ _ _ (productAngularJet_sub_bare_le hw0 hw1 hx1 hxm1 N)
    (derivative_bound_le hw0 hw1 hε N hN)

/-- The finite numerator needed by the joint theta endpoint-jet join.
Both derivatives and the multiplier are the ORIGINAL product, without
positive-density division or a replacement curvature sequence. -/
def productRadialNumerator (w x : Q') (N : Nat) : Q' :=
  (1 + -(x*x))*
      (eval (pderiv (JacobiShiftedPositiveCoefficients.product w N)) (1+x)*
        eval (pderiv (JacobiShiftedPositiveCoefficients.product w N)) (1+x)) +
    -(ThetaConv.Ppart w x N*productAngularJet w x N)

/-- Exact SAME-product radial cost behind the combined first/second jets.
The joint scalar endpoint frequency jet has twice this numerator; this
lemma does not assert that still-unproved convolution/limit identification. -/
theorem productRadialNumerator_pin {w x : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hxm1 : (-1 : Q') ≤ x) (N : Nat) :
    productRadialNumerator w x N ≈
      (ThetaConv.Ppart w x N*ThetaConv.Ppart w x N)*
        JacobiHeatRadialMixtureCancellation.productRadialCost (HKConv.sTerm w x) N x := by
  have h1 := JacobiHeatRadialMomentJets.product_first_moment_pin hw0 hw1 hxm1 N
  have h2 := JacobiHeatRadialMomentJets.product_second_moment_pin hw0 hw1 hxm1 N
  have ha : productAngularJet w x N ≈
      (1 + -(x*x))*(ThetaConv.Ppart w x N*
        (JacobiHeatRadialMomentJets.firstMoment w x N*JacobiHeatRadialMomentJets.firstMoment w x N +
          -(JacobiHeatRadialMomentJets.secondMoment w x N))) +
      -(x*(ThetaConv.Ppart w x N*JacobiHeatRadialMomentJets.firstMoment w x N)) :=
    add_congr (Q'.mul_eqv_congr_left _ _ _ h2)
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ h1))
  exact Q'.eqv_trans _ _ _
    (add_congr (Q'.mul_eqv_congr_left _ _ _ (mul_congr h1 h1))
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ ha)))
    (poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
        (.neg (.mul (.var 1)
          (.add (.mul (.var 0) (.mul (.var 1) (.add (.mul (.var 2) (.var 2)) (.neg (.var 3)))))
            (.neg (.mul (.var 4) (.mul (.var 1) (.var 2))))))))
      (.mul (.mul (.var 1) (.var 1))
        (.add (.mul (.var 0) (.var 3)) (.mul (.var 4) (.var 2))))
      (by decide) (fun
        | 0 => 1 + -(x*x)
        | 1 => ThetaConv.Ppart w x N
        | 2 => JacobiHeatRadialMomentJets.firstMoment w x N
        | 3 => JacobiHeatRadialMomentJets.secondMoment w x N
        | _ => x))

end YMGap.Continuum.FiniteJacobiAngularComparison

#print axioms YMGap.Continuum.FiniteJacobiAngularComparison.angularEval
#print axioms YMGap.Continuum.FiniteJacobiAngularComparison.seriesPoly
#print axioms YMGap.Continuum.FiniteJacobiAngularComparison.angularSum
#print axioms YMGap.Continuum.FiniteJacobiAngularComparison.eval_seriesPoly
#print axioms YMGap.Continuum.FiniteJacobiAngularComparison.angular_seriesPoly
#print axioms YMGap.Continuum.FiniteJacobiAngularComparison.productAngularJet
#print axioms YMGap.Continuum.FiniteJacobiAngularComparison.product_series_coeff_pin
#print axioms YMGap.Continuum.FiniteJacobiAngularComparison.productAngularJet_pin
#print axioms YMGap.Continuum.FiniteJacobiAngularComparison.productAngularJet_sub_bare_pin
#print axioms YMGap.Continuum.FiniteJacobiAngularComparison.productAngularJet_sub_bare_le
#print axioms YMGap.Continuum.FiniteJacobiAngularComparison.productAngularJet_sub_bare_close
#print axioms YMGap.Continuum.FiniteJacobiAngularComparison.productRadialNumerator
#print axioms YMGap.Continuum.FiniteJacobiAngularComparison.productRadialNumerator_pin
