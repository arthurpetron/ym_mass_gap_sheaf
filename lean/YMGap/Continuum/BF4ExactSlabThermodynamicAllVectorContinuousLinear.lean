/-
# Bounded symmetric continuous operators on the FULL ORIGINAL carrier

The constructed action respects symbol equivalence on rational [0,1],
independently of bounds and modulus data, and recovers the original
polynomial operators. Rational linearity and symmetry pass through the
explicit original row limits. The sharp norm bound gives the full-carrier
squared-distance bound with computed tolerance epsilon/(F.bound^2+1).

Quotient induction here proves propositions; output representatives and
rates are already constructed from supplied input data. No density of a
single cyclic probe, image-Cauchy premise or spectral surrogate is used.
These fixed-nome/spacing operator laws are not continuum or physical-scale
uniformity and do not close the Clay target.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction
import YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear
import YMGap.Continuum.BF4ExactSlabThermodynamicSymbolCompatibility
import YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder

namespace YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousLinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.BernsteinSequenceWrap
open YMGap.Continuum.BernsteinStageData
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity (linearTolerance linearTolerance_pos linearTolerance_budget)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialRowAction (operatorRows operatorRows_pin operator_rowLimit)
open YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear (addRows addRows_pin rowLimit_add)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier
open YMGap.Continuum.BF4ExactSlabThermodynamicSymbolCompatibility
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)
local notation "point" X => Quotient.mk seminorm.completionSetoid X

/-- Only the symbol's rational values on [0,1] matter, not its representation data. -/
theorem continuousAction_symbol_congr (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G)
    (hfg : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.eqv (F.f t) (G.f t)) (x : Completion) :
    continuousAction F V x=continuousAction G W x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply rowLimits_eq_of_close (symbolRows F V X) (symbolRows G W X)
    (fun epsilon => comparisonModulus F V G W (approximationTolerance X epsilon))
  intro epsilon he n hn
  rw [symbolRows_pin,symbolRows_pin]
  exact polynomial_close X _ _ epsilon he
    (same_symbol_bernstein_close F V G W hfg _ (approximationTolerance_pos X he) n hn)

theorem continuousAction_modulus_independent (F : CtsMod) (V W : MonotoneOmegaVanishing F) (x : Completion) :
    continuousAction F V x=continuousAction F W x :=
  continuousAction_symbol_congr F V F W (fun t _ _ => Q'.eqv_refl (F.f t)) x

/-- Polynomial recovery pins the action to the SAME pre-existing original operator. -/
theorem continuousAction_eq_polynomial (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (p : QPoly.Poly) (hp : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.eqv (F.f t) (QPoly.eval p t))
    (x : Completion) : continuousAction F V x=polynomialOperator p x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply rowLimit_eq_of_bound (symbolRows F V X) _
    (fun epsilon => (symbolErrorModulus F V).stage (approximationTolerance X epsilon))
  intro epsilon he n hn
  rw [symbolRows_pin]
  apply polynomial_close X _ _ epsilon he
  intro t ht h1
  have h := bernstein_symbol_bound F V _ (approximationTolerance_pos X he) n hn t ht h1
  exact ⟨Q'.le_trans' _ _ _ h.1 (Q'.add_le_add_right _ _ _ (Q'.le_of_eqv (hp t ht h1))),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (hp t ht h1)) h.2⟩

theorem continuousAction_add (F : CtsMod) (V : MonotoneOmegaVanishing F) (x y : Completion) :
    continuousAction F V (completedAdd x y)=completedAdd (continuousAction F V x) (continuousAction F V y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  have h : representedAction F V (addition.mapCauchy X Y)=
      rowLimit (addRows (symbolRows F V X) (symbolRows F V Y)) := by
    apply rowLimit_independent
    intro n
    rw [symbolRows_pin,addRows_pin,symbolRows_pin,symbolRows_pin]
    exact vector_base_add (point X) (point Y) (bernsteinPoly F n) 0
  exact h.trans (rowLimit_add _ _)

theorem continuousAction_smul (F : CtsMod) (V : MonotoneOmegaVanishing F) (c : Q') (x : Completion) :
    continuousAction F V (completedSmul c x)=completedSmul c (continuousAction F V x) := by
  refine Quotient.inductionOn x ?_
  intro X
  have h : representedAction F V ((scalarContinuous c).mapCauchy X)=
      rowLimit (operatorRows [c] (symbolRows F V X)) := by
    apply rowLimit_independent
    intro n
    rw [symbolRows_pin,operatorRows_pin,symbolRows_pin,operator_constant]
    exact vector_base_smul c (point X) (bernsteinPoly F n) 0
  exact h.trans ((operator_rowLimit _ _).trans (operator_constant _ _))

theorem continuousAction_sub (F : CtsMod) (V : MonotoneOmegaVanishing F) (x y : Completion) :
    continuousAction F V (completedSub x y)=completedSub (continuousAction F V x) (continuousAction F V y) := by
  unfold completedSub completedNeg
  rw [continuousAction_add,continuousAction_smul]

theorem continuousAction_distance_bound (F : CtsMod) (V : MonotoneOmegaVanishing F) (x y : Completion) :
    RCle (completedDist (continuousAction F V x) (continuousAction F V y))
      (RCscale (F.bound*F.bound) (completedDist x y)) := by
  have h := continuousAction_norm_bound F V (completedSub x y)
  rw [continuousAction_sub] at h
  exact h

def inputTolerance (F : CtsMod) (epsilon : Q') : Q' :=
  linearTolerance (F.bound*F.bound) (SumOfSquares.q_mul_self_nonneg F.bound) epsilon

theorem inputTolerance_pos (F : CtsMod) {epsilon : Q'} (he : (0 : Q')<epsilon) :
    (0 : Q')<inputTolerance F epsilon := linearTolerance_pos _ _ he

theorem continuousAction_close (F : CtsMod) (V : MonotoneOmegaVanishing F) (x y : Completion)
    (epsilon : Q') (he : (0 : Q')<epsilon)
    (h : RCle (completedDist x y) (rat (inputTolerance F epsilon))) :
    RCle (completedDist (continuousAction F V x) (continuousAction F V y)) (rat epsilon) :=
  RCle_trans (continuousAction_distance_bound F V x y) (RCle_trans
    (RCscale_mono (SumOfSquares.q_mul_self_nonneg F.bound) h)
    (leEv_le_ofQ'_of_approx_le (fun _ => linearTolerance_budget _ (SumOfSquares.q_mul_self_nonneg F.bound) he)))

/-- The computed input tolerance controls the operator simultaneously on ALL original vectors. -/
def continuityCertificate (F : CtsMod) (V : MonotoneOmegaVanishing F) :
    {delta : Q' → Q' // (∀ epsilon : Q',(0 : Q')<epsilon → (0 : Q')<delta epsilon) ∧
      ∀ epsilon : Q',(0 : Q')<epsilon → ∀ x y : Completion,
        RCle (completedDist x y) (rat (delta epsilon)) →
        RCle (completedDist (continuousAction F V x) (continuousAction F V y)) (rat epsilon)} :=
  ⟨inputTolerance F,⟨fun _ he => inputTolerance_pos F he,
    fun epsilon he x y => continuousAction_close F V x y epsilon he⟩⟩

theorem continuousAction_symmetric (F : CtsMod) (V : MonotoneOmegaVanishing F) (x y : Completion) :
    completedInner (continuousAction F V x) y=completedInner x (continuousAction F V y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  have h := rowLimit_pairing_eq (symbolRows F V X) (constantRows Y)
    (constantRows X) (symbolRows F V Y) (by
      intro n
      rw [symbolRows_pin,symbolRows_pin,constantRows_pin,constantRows_pin]
      exact operator_symmetric _ _ _)
  rw [rowLimit_constant,rowLimit_constant] at h
  exact h

end YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousLinear

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousLinear.continuousAction_symbol_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousLinear.continuousAction_modulus_independent
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousLinear.continuousAction_eq_polynomial
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousLinear.continuousAction_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousLinear.continuousAction_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousLinear.continuousAction_sub
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousLinear.continuousAction_distance_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousLinear.inputTolerance
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousLinear.inputTolerance_pos
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousLinear.continuousAction_close
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousLinear.continuityCertificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousLinear.continuousAction_symmetric
