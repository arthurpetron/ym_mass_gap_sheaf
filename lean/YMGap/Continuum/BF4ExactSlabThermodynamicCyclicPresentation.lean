/-
# Represented ORIGINAL cyclic vectors and explicit polynomial comparison

A presentation retains existing original Cauchy rows, their polynomial
coefficients and the proved pointwise pin. Its state is in the existing
completion, not a new carrier. Polynomial and Bernstein-symbol instances
are constructed below; this is representation data, not a new spectral
or physical analytic input. No arbitrary quotient representative is chosen.

The computed norm ceiling and scalar tolerance turn uniform polynomial
comparison on [0,1] into comparison on this SAME represented cyclic vector.
All physical nome and spacing parameters remain fixed.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLimitBound

namespace YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.BernsteinSequenceWrap
open YMGap.Continuum.BernsteinStageData
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference (vector_sub)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialCarrierLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLimitBound (cyclicLimit_norm_bound)
open YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinLimitPairing (bernsteinRow_pin)
open YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation (normCap normCap_nonnegative norm_le_cap)

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

structure CyclicPresentation where
  rows : CauchyRows
  polynomial : Nat → QPoly.Poly
  point_pin : ∀ n,rowPoint rows n=polynomialOperator (polynomial n) unitProbe.val

def state (X : CyclicPresentation) : Completion := rowLimit X.rows

def ofSymbol (F : CtsMod) (V : MonotoneOmegaVanishing F) : CyclicPresentation :=
  ⟨bernsteinRows F V,bernsteinPoly F,bernsteinRow_pin F V⟩

theorem state_ofSymbol (F : CtsMod) (V : MonotoneOmegaVanishing F) :
    state (ofSymbol F V)=continuousProbe F V := rfl

def ofPolynomial (p : QPoly.Poly) : CyclicPresentation :=
  ⟨polynomialRows (fun _ => p) (fun _ => 0) (constant_uniform p),fun _ => p,
    polynomialRows_pin (fun _ => p) (fun _ => 0) (constant_uniform p)⟩

theorem state_ofPolynomial (p : QPoly.Poly) : state (ofPolynomial p)=polynomialOperator p unitProbe.val :=
  polynomialLimit_constant p

def stateNormCap (X : CyclicPresentation) : Q' := normCap (diagonalCauchy X.rows)

theorem stateNormCap_nonnegative (X : CyclicPresentation) : (0 : Q')≤stateNormCap X := normCap_nonnegative _

theorem state_norm_le_cap (X : CyclicPresentation) :
    RCle (completedInner (state X) (state X)) (rat (stateNormCap X)) := norm_le_cap _

theorem polynomial_norm_bound (X : CyclicPresentation) (p : QPoly.Poly) (M : Q') (hM : (0 : Q')≤M)
    (hp : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.abs (QPoly.eval p t)≤M) :
    RCle (completedInner (polynomialOperator p (state X)) (polynomialOperator p (state X)))
      (RCscale (M*M) (completedInner (state X) (state X))) :=
  cyclicLimit_norm_bound p X.rows X.polynomial X.point_pin M hM hp

theorem polynomial_difference_bound (X : CyclicPresentation) (p q : QPoly.Poly)
    (M : Q') (hM : (0 : Q')≤M)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.abs (QPoly.eval p t + -QPoly.eval q t)≤M) :
    RCle (completedDist (polynomialOperator p (state X)) (polynomialOperator q (state X)))
      (RCscale (M*M) (completedInner (state X) (state X))) := by
  unfold completedDist polynomialOperator
  rw [← vector_sub]
  exact polynomial_norm_bound X (QPoly.psub p q) M hM (fun t ht h1 =>
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (QPoly.eval_psub p q t))) (h t ht h1))

def approximationTolerance (X : CyclicPresentation) (epsilon : Q') : Q' :=
  squareTolerance (linearTolerance (stateNormCap X) (stateNormCap_nonnegative X) epsilon)

theorem approximationTolerance_pos (X : CyclicPresentation) {epsilon : Q'} (he : (0 : Q')<epsilon) :
    (0 : Q')<approximationTolerance X epsilon :=
  squareTolerance_pos _ (linearTolerance_pos _ _ he)

theorem approximationTolerance_budget (X : CyclicPresentation) {epsilon : Q'} (he : (0 : Q')<epsilon) :
    (approximationTolerance X epsilon*approximationTolerance X epsilon)*stateNormCap X≤epsilon :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
    (squareTolerance_budget _ (linearTolerance_pos _ _ he)) (stateNormCap_nonnegative X))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (linearTolerance_budget _ (stateNormCap_nonnegative X) he))

theorem polynomial_close (X : CyclicPresentation) (p q : QPoly.Poly)
    (epsilon : Q') (he : (0 : Q')<epsilon)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 →
      QPoly.eval p t≤QPoly.eval q t+approximationTolerance X epsilon ∧
      QPoly.eval q t≤QPoly.eval p t+approximationTolerance X epsilon) :
    RCle (completedDist (polynomialOperator p (state X)) (polynomialOperator q (state X))) (rat epsilon) := by
  let M := approximationTolerance X epsilon
  have hb := polynomial_difference_bound X p q M (Q'.le_of_lt (approximationTolerance_pos X he))
    (fun t ht h1 => abs_sub_le_of_bounds (h t ht h1).1 (h t ht h1).2)
  exact RCle_trans hb (RCle_trans
    (RCscale_mono (SumOfSquares.q_mul_self_nonneg M) (state_norm_le_cap X))
    (leEv_le_ofQ'_of_approx_le (fun _ => approximationTolerance_budget X he)))

end YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation.CyclicPresentation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation.state
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation.ofSymbol
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation.state_ofSymbol
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation.ofPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation.state_ofPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation.stateNormCap
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation.stateNormCap_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation.state_norm_le_cap
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation.polynomial_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation.polynomial_difference_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation.approximationTolerance
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation.approximationTolerance_pos
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation.approximationTolerance_budget
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation.polynomial_close
