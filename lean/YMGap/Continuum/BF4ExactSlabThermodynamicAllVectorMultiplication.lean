/-
# Multiplication on the FULL ORIGINAL completed carrier

Products of Bernstein polynomials converge, at a computed rate, directly
to the composition of the constructed original continuous operators.
The degree-independent polynomial bound controls the moving inner input.
Comparing these products with the Bernstein sequence of the constructed
product symbol proves multiplication on every original completed state.

No intermediate spectral carrier, cyclic-density or image-limit premise
is supplied. Nested action representatives retain all computational data.
The same operators commute and their products have the expected original
pairings and square forms. These are fixed SU(2) nome/spacing laws, not
physical-scale uniformity, continuum reconstruction or the Clay theorem.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousLinear
import YMGap.Continuum.BF4ExactSlabThermodynamicProductSymbol

namespace YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorMultiplication

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.BernsteinSequenceWrap
open YMGap.Continuum.BernsteinStageData
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity (linearTolerance_budget)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinLimitPairing (bernsteinPoly_abs_bound)
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousProductRows (productPolynomial)
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousMultiplication (multiplicationModulus product_symbol_close)
open YMGap.Continuum.BF4ExactSlabThermodynamicProductSymbol (productSymbol productVanishing)
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialBound (polynomial_distance_bound)
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousLinear
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)
local notation "point" X => Quotient.mk seminorm.completionSetoid X

/-- The input tolerance is independent of Bernstein degree and of the two original states. -/
theorem bernstein_input_close (F : CtsMod) (n : Nat) (x y : Completion)
    (epsilon : Q') (he : (0 : Q')<epsilon)
    (h : RCle (completedDist x y) (rat (inputTolerance F epsilon))) :
    RCle (completedDist (polynomialOperator (bernsteinPoly F n) x)
      (polynomialOperator (bernsteinPoly F n) y)) (rat epsilon) :=
  RCle_trans (polynomial_distance_bound x y _ F.bound (bound_nonneg F) (bernsteinPoly_abs_bound F n))
    (RCle_trans (RCscale_mono (SumOfSquares.q_mul_self_nonneg F.bound) h)
      (leEv_le_ofQ'_of_approx_le (fun _ => linearTolerance_budget _ (SumOfSquares.q_mul_self_nonneg F.bound) he)))

def productModulus (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (X : seminorm.Cauchy) (epsilon : Q') : Nat :=
  max (actionModulus G W X (inputTolerance F (quarter epsilon)))
    (actionModulus F V (actionRepresentative G W X) (quarter epsilon))

theorem product_bound (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (X : seminorm.Cauchy)
    (epsilon : Q') (he : (0 : Q')<epsilon) (n : Nat) (hn : productModulus F V G W X epsilon≤n) :
    RCle (completedDist (polynomialOperator (productPolynomial F G n) (point X))
      (continuousAction F V (continuousAction G W (point X)))) (rat epsilon) := by
  have hd := quarter_pos he
  have hleft := bernstein_input_close F n (polynomialOperator (bernsteinPoly G n) (point X))
    (continuousAction G W (point X)) (quarter epsilon) hd
    (continuousAction_bound G W X _ (inputTolerance_pos F hd) n (Nat.le_trans (Nat.le_max_left _ _) hn))
  have hright := continuousAction_bound F V (actionRepresentative G W X) _ hd n
    (Nat.le_trans (Nat.le_max_right _ _) hn)
  rw [actionRepresentative_pin] at hright
  rw [productPolynomial,operator_mul]
  exact completedDist_two_segment _ _ _ epsilon hleft hright

/-- Original output data and a direct polynomial-product convergence rate. -/
def compositionCertificate (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (X : seminorm.Cauchy) :
    Σ' Y : seminorm.Cauchy,
      {rate : Q' → Nat // (point Y)=continuousAction F V (continuousAction G W (point X)) ∧
        ∀ epsilon : Q',(0 : Q')<epsilon → ∀ n,rate epsilon≤n →
          RCle (completedDist (polynomialOperator (productPolynomial F G n) (point X)) (point Y)) (rat epsilon)} := by
  refine ⟨actionRepresentative F V (actionRepresentative G W X),⟨productModulus F V G W X,?_,?_⟩⟩
  · rw [actionRepresentative_pin,actionRepresentative_pin]
  · intro epsilon he n hn
    rw [actionRepresentative_pin,actionRepresentative_pin]
    exact product_bound F V G W X epsilon he n hn

def multiplicationActionModulus (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (H : CtsMod) (U : MonotoneOmegaVanishing H)
    (X : seminorm.Cauchy) (epsilon : Q') : Nat :=
  max (multiplicationModulus F V G W H U (approximationTolerance X (quarter epsilon)))
    (productModulus F V G W X (quarter epsilon))

theorem multiplication_bound (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (H : CtsMod) (U : MonotoneOmegaVanishing H)
    (hH : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.eqv (H.f t) (F.f t*G.f t)) (X : seminorm.Cauchy)
    (epsilon : Q') (he : (0 : Q')<epsilon) (n : Nat)
    (hn : multiplicationActionModulus F V G W H U X epsilon≤n) :
    RCle (completedDist (polynomialOperator (bernsteinPoly H n) (point X))
      (continuousAction F V (continuousAction G W (point X)))) (rat epsilon) := by
  have hd := quarter_pos he
  have hleft := polynomial_close X (productPolynomial F G n) (bernsteinPoly H n) _ hd
    (product_symbol_close F V G W H U hH _ (approximationTolerance_pos X hd) n
      (Nat.le_trans (Nat.le_max_left _ _) hn))
  rw [completedDist_symm] at hleft
  exact completedDist_two_segment _ _ _ epsilon hleft
    (product_bound F V G W X _ hd n (Nat.le_trans (Nat.le_max_right _ _) hn))

/-- A symbol agreeing with the product acts as composition on EVERY original vector. -/
theorem continuousAction_mul (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (H : CtsMod) (U : MonotoneOmegaVanishing H)
    (hH : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.eqv (H.f t) (F.f t*G.f t)) (x : Completion) :
    continuousAction H U x=continuousAction F V (continuousAction G W x) := by
  refine Quotient.inductionOn x ?_
  intro X
  apply rowLimit_eq_of_bound (symbolRows H U X) _ (multiplicationActionModulus F V G W H U X)
  intro epsilon he n hn
  rw [symbolRows_pin]
  exact multiplication_bound F V G W H U hH X epsilon he n hn

/-- Product continuity data are constructed, not an extra hypothesis. -/
theorem productSymbol_composition (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (x : Completion) :
    continuousAction (productSymbol F V G W) (productVanishing F V G W) x=
      continuousAction F V (continuousAction G W x) :=
  continuousAction_mul F V G W _ _ (fun t _ _ => Q'.eqv_refl (F.f t*G.f t)) x

theorem continuousAction_comm (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (x : Completion) :
    continuousAction F V (continuousAction G W x)=continuousAction G W (continuousAction F V x) := by
  rw [← productSymbol_composition,← productSymbol_composition]
  exact continuousAction_symbol_congr _ _ _ _ (fun t _ _ => Q'.mul_comm_eqv (F.f t) (G.f t)) x

theorem productSymbol_pairing (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (x y : Completion) :
    completedInner (continuousAction (productSymbol F V G W) (productVanishing F V G W) x) y=
      completedInner (continuousAction G W x) (continuousAction F V y) := by
  rw [productSymbol_composition,continuousAction_symmetric]

theorem productSquare_form_identity (F : CtsMod) (V : MonotoneOmegaVanishing F) (x : Completion) :
    completedInner (continuousAction (productSymbol F V F V) (productVanishing F V F V) x) x=
      completedInner (continuousAction F V x) (continuousAction F V x) := productSymbol_pairing F V F V x x

end YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorMultiplication

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorMultiplication.bernstein_input_close
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorMultiplication.productModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorMultiplication.product_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorMultiplication.compositionCertificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorMultiplication.multiplicationActionModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorMultiplication.multiplication_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorMultiplication.continuousAction_mul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorMultiplication.productSymbol_composition
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorMultiplication.continuousAction_comm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorMultiplication.productSymbol_pairing
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorMultiplication.productSquare_form_identity
