/-
# Sharp polynomial operator bounds on the ORIGINAL cyclic polynomial sector

If |p|<=M on rational [0,1], then ||p(T2)q(T2)v||^2<=M^2||q(T2)v||^2
for EVERY polynomial q. The factor is independent of q, not merely a
probe-vector norm estimate. The proof multiplies the pointwise squared
inequality by q^2 and uses the already-constructed positive original
moment functional. Differences give the corresponding distance bound.
No spectral decomposition or operator-norm hypothesis is supplied.

These are bounds on actual original cyclic polynomial vectors at fixed
SU(2) nome/spacing. Extending to their limits and full continuous operator
calculus remains subsequent work; no beta/spacing-uniform gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator

namespace YMGap.Continuum.BF4ExactSlabThermodynamicCyclicOperatorBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments (polynomialVector)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialProbeNorm (probe_norm_square)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference (vector_sub)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator

theorem square_le_of_abs_le (a M : Q') (hM : (0 : Q')≤M) (h : Q'.abs a≤M) : a*a≤M*M :=
  Q'.mul_le_of_bounds hM hM
    (Q'.le_trans' _ _ _ (Q'.neg_le_neg h) (ExpNeg.neg_abs_le a))
    (Q'.le_trans' _ _ _ (Q'.le_abs_self a) h)
    (Q'.le_trans' _ _ _ (Q'.neg_le_neg h) (ExpNeg.neg_abs_le a))
    (Q'.le_trans' _ _ _ (Q'.le_abs_self a) h)

theorem eval_product_square (p q : QPoly.Poly) (t : Q') :
    Q'.eqv (QPoly.eval (QPoly.pmul (QPoly.pmul p q) (QPoly.pmul p q)) t)
      ((QPoly.eval p t*QPoly.eval p t)*(QPoly.eval q t*QPoly.eval q t)) := by
  have e := QPoly.eval_pmul p q t
  apply Q'.eqv_trans _ _ _ (QPoly.eval_pmul _ _ t)
  apply Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ e)
  apply Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ e)
  exact RingNormaliser.poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
    (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (by decide)
    (fun | 0 => QPoly.eval p t | _ => QPoly.eval q t)

theorem eval_scaled_square (M : Q') (q : QPoly.Poly) (t : Q') :
    Q'.eqv (QPoly.eval (QPoly.pscale (M*M) (QPoly.pmul q q)) t)
      ((M*M)*(QPoly.eval q t*QPoly.eval q t)) :=
  Q'.eqv_trans _ _ _ (QPoly.eval_pscale _ _ t)
    (Q'.mul_eqv_congr_left _ _ _ (QPoly.eval_pmul q q t))

/-- Uniform in the cyclic vector q(T2)v, with no coefficient-size loss. -/
theorem cyclic_norm_bound (p q : QPoly.Poly) (M : Q') (hM : (0 : Q')≤M)
    (hp : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.abs (QPoly.eval p t)≤M) :
    RCle (completedInner (polynomialOperator p (polynomialOperator q unitProbe.val))
      (polynomialOperator p (polynomialOperator q unitProbe.val)))
      (RCscale (M*M) (completedInner (polynomialOperator q unitProbe.val) (polynomialOperator q unitProbe.val))) := by
  rw [← operator_mul]
  unfold polynomialOperator
  rw [probe_norm_square,probe_norm_square,← functional_scale]
  apply functional_mono
  intro t ht h1
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (eval_product_square p q t))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (square_le_of_abs_le _ M hM (hp t ht h1))
        (SumOfSquares.q_mul_self_nonneg _))
      (Q'.ge_of_eqv (eval_scaled_square M q t)))

/-- The operator bound is relative to the SAME original distance between cyclic vectors. -/
theorem cyclic_distance_bound (p q r : QPoly.Poly) (M : Q') (hM : (0 : Q')≤M)
    (hp : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.abs (QPoly.eval p t)≤M) :
    RCle (completedDist (polynomialOperator p (polynomialOperator q unitProbe.val))
      (polynomialOperator p (polynomialOperator r unitProbe.val)))
      (RCscale (M*M) (completedDist (polynomialOperator q unitProbe.val) (polynomialOperator r unitProbe.val))) := by
  unfold polynomialOperator completedDist
  rw [← vector_base_sub,← vector_sub]
  exact cyclic_norm_bound p (QPoly.psub q r) M hM hp

end YMGap.Continuum.BF4ExactSlabThermodynamicCyclicOperatorBound

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicOperatorBound.square_le_of_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicOperatorBound.eval_product_square
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicOperatorBound.eval_scaled_square
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicOperatorBound.cyclic_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicOperatorBound.cyclic_distance_bound
