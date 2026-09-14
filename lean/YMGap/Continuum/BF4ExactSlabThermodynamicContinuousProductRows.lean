/-
# Polynomial-product limits equal ORIGINAL continuous-action composition

The nth Bernstein polynomial is bounded by F.bound on [0,1], uniformly
in degree. Its sharp relative cyclic bound controls the image of the
G-input approximation. Thus the polynomial products have a computed
convergence rate to the actual composition, without a coefficient loss.
Their Cauchy representatives, modulus and same-composition pin are retained.

No product-symbol continuity package, diagonal model or image-Cauchy
premise is supplied. This is fixed-nome/spacing original cyclic calculus,
not full-carrier spectral or physical-scale/continuum Yang--Mills closure.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicContinuousLinear

namespace YMGap.Continuum.BF4ExactSlabThermodynamicContinuousProductRows

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.BernsteinSequenceWrap
open YMGap.Continuum.BernsteinStageData
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialRowAction
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinLimitPairing (bernsteinPoly_abs_bound)
open YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousAction
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousCyclicClosure
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousLinear
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

theorem polynomial_distance_bound (p : QPoly.Poly) (X Y : CyclicPresentation)
    (M : Q') (hM : (0 : Q')≤M)
    (hp : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.abs (QPoly.eval p t)≤M) :
    RCle (completedDist (polynomialOperator p (state X)) (polynomialOperator p (state Y)))
      (RCscale (M*M) (completedDist (state X) (state Y))) := by
  have h := polynomial_norm_bound (subPresentation X Y) p M hM hp
  rw [state_subPresentation] at h
  unfold polynomialOperator at h
  rw [vector_base_sub] at h
  exact h

theorem bernstein_input_close (F : CtsMod) (n : Nat) (X Y : CyclicPresentation)
    (epsilon : Q') (he : (0 : Q')<epsilon)
    (h : RCle (completedDist (state X) (state Y)) (rat (inputTolerance F epsilon))) :
    RCle (completedDist (polynomialOperator (bernsteinPoly F n) (state X))
      (polynomialOperator (bernsteinPoly F n) (state Y))) (rat epsilon) :=
  RCle_trans (polynomial_distance_bound _ X Y F.bound (bound_nonneg F) (bernsteinPoly_abs_bound F n))
    (RCle_trans (RCscale_mono (SumOfSquares.q_mul_self_nonneg F.bound) h)
      (leEv_le_ofQ'_of_approx_le (fun _ => linearTolerance_budget _ (SumOfSquares.q_mul_self_nonneg F.bound) he)))

def productPolynomial (F G : CtsMod) (n : Nat) : QPoly.Poly :=
  QPoly.pmul (bernsteinPoly F n) (bernsteinPoly G n)

def productModulus (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (X : CyclicPresentation) (epsilon : Q') : Nat :=
  max (symbolModulus G W X (inputTolerance F (quarter epsilon)))
    (symbolModulus F V (actionPresentation G W X) (quarter epsilon))

theorem product_bound (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (X : CyclicPresentation)
    (epsilon : Q') (he : (0 : Q')<epsilon) (n : Nat) (hn : productModulus F V G W X epsilon≤n) :
    RCle (completedDist (polynomialOperator (productPolynomial F G n) (state X))
      (symbolAction F V (actionPresentation G W X))) (rat epsilon) := by
  have hd := quarter_pos he
  have hleft := bernstein_input_close F n (polynomialPresentation (bernsteinPoly G n) X)
    (actionPresentation G W X) (quarter epsilon) hd (by
      rw [state_polynomialPresentation,state_actionPresentation]
      exact symbolAction_bound G W X _ (inputTolerance_pos F hd) n (Nat.le_trans (Nat.le_max_left _ _) hn))
  rw [state_polynomialPresentation,state_actionPresentation] at hleft
  have hright := symbolAction_bound F V (actionPresentation G W X) _ hd n (Nat.le_trans (Nat.le_max_right _ _) hn)
  rw [state_actionPresentation] at hright
  rw [productPolynomial,operator_mul]
  exact completedDist_two_segment _ _ _ epsilon hleft hright

def productRows (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (X : CyclicPresentation) : CauchyRows where
  row := fun n => actionRepresentative (productPolynomial F G n) X.rows
  modulus := fun epsilon => productModulus F V G W X (quarter epsilon)
  isCauchy := by
    intro epsilon he m n hm hn
    rw [actionRepresentative_pin,actionRepresentative_pin]
    have hleft := product_bound F V G W X _ (quarter_pos he) m hm
    have hright := product_bound F V G W X _ (quarter_pos he) n hn
    rw [completedDist_symm] at hright
    exact completedDist_two_segment _ _ _ epsilon hleft hright

theorem productRows_pin (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (X : CyclicPresentation) (n : Nat) :
    rowPoint (productRows F V G W X) n=polynomialOperator (productPolynomial F G n) (state X) :=
  actionRepresentative_pin _ _

def productAction (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (X : CyclicPresentation) : Completion :=
  rowLimit (productRows F V G W X)

theorem productAction_eq_composition (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (X : CyclicPresentation) :
    productAction F V G W X=symbolAction F V (actionPresentation G W X) := by
  apply rowLimit_eq_of_bound _ _ (productModulus F V G W X)
  intro epsilon he n hn
  rw [productRows_pin]
  exact product_bound F V G W X epsilon he n hn

def productCertificate (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (X : CyclicPresentation) :
    Σ' Y : seminorm.Cauchy,
      {rate : Q' → Nat // Quotient.mk seminorm.completionSetoid Y=symbolAction F V (actionPresentation G W X) ∧
        ∀ epsilon : Q',(0 : Q')<epsilon → ∀ n,rate epsilon≤n →
          RCle (completedDist (polynomialOperator (productPolynomial F G n) (state X))
            (Quotient.mk seminorm.completionSetoid Y)) (rat epsilon)} := by
  refine ⟨diagonalCauchy (productRows F V G W X),⟨productModulus F V G W X,⟨productAction_eq_composition F V G W X,?_⟩⟩⟩
  intro epsilon he n hn
  change RCle (completedDist _ (productAction F V G W X)) _
  rw [productAction_eq_composition]
  exact product_bound F V G W X epsilon he n hn

end YMGap.Continuum.BF4ExactSlabThermodynamicContinuousProductRows

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousProductRows.polynomial_distance_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousProductRows.bernstein_input_close
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousProductRows.productPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousProductRows.productModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousProductRows.product_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousProductRows.productRows
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousProductRows.productRows_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousProductRows.productAction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousProductRows.productAction_eq_composition
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousProductRows.productCertificate
