/-
# Uniform polynomial sequences act on the FULL ORIGINAL carrier

The input is polynomial data with a uniform rational [0,1] Cauchy rate,
not a rational-valued limiting symbol. Original represented completeness
constructs the output and its squared-distance rate. Representative
independence descends the action to the entire original completion.
Uniformly asymptotic sequences give the same operator, independently of
their rate data. Constants recover the original polynomial operators;
Bernstein sequences recover the already constructed continuous action.

This permits limits whose scalar values are not rational. It does not
construct a square-root sequence, identify geometric half time, assert
time injectivity, or change the fixed SU(2) nome/spacing. Physical-scale
uniformity, continuum reconstruction and the Clay target remain open.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousLinear

namespace YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.BernsteinSequenceWrap
open YMGap.Continuum.BernsteinStageData
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference (vectorRepresentative vectorRepresentative_pin)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialCarrierLimit (constant_uniform)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier
open YMGap.Continuum.BF4ExactSlabThermodynamicSymbolCompatibility (rowLimits_eq_of_close)
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction
  (approximationTolerance approximationTolerance_pos polynomial_close continuousAction symbolRows symbolRows_pin)

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)
local notation "point" X => Quotient.mk seminorm.completionSetoid X

/-- Polynomial coefficients and a usable UNIFORM Cauchy rate are retained as data. -/
structure UniformSequence where
  polynomial : Nat → QPoly.Poly
  modulus : Q' → Nat
  cauchy : ∀ epsilon : Q',(0 : Q')<epsilon → ∀ m n,modulus epsilon≤m → modulus epsilon≤n →
    ∀ t : Q',(0 : Q')≤t → t≤1 →
      QPoly.eval (polynomial m) t≤QPoly.eval (polynomial n) t+epsilon ∧
      QPoly.eval (polynomial n) t≤QPoly.eval (polynomial m) t+epsilon

def actionRows (P : UniformSequence) (X : seminorm.Cauchy) : CauchyRows where
  row := fun n => vectorRepresentative X (P.polynomial n) 0
  modulus := fun epsilon => P.modulus (approximationTolerance X epsilon)
  isCauchy := by
    intro epsilon he m n hm hn
    simp only [vectorRepresentative_pin]
    exact polynomial_close X _ _ epsilon he
      (P.cauchy _ (approximationTolerance_pos X he) m n hm hn)

theorem actionRows_pin (P : UniformSequence) (X : seminorm.Cauchy) (n : Nat) :
    rowPoint (actionRows P X) n=polynomialOperator (P.polynomial n) (point X) := vectorRepresentative_pin _ _ _

def representedAction (P : UniformSequence) (X : seminorm.Cauchy) : Completion :=
  rowLimit (actionRows P X)

theorem representedAction_congr (P : UniformSequence) (X Y : seminorm.Cauchy)
    (h : (point X)=(point Y)) : representedAction P X=representedAction P Y := by
  apply rowLimit_independent
  intro n
  rw [actionRows_pin,actionRows_pin,h]

/-- Actual action on every original completed state, with no representative selection. -/
def sequenceAction (P : UniformSequence) : Completion → Completion :=
  Quotient.lift (representedAction P) (fun X Y h => representedAction_congr P X Y (Quotient.sound h))

theorem sequenceAction_mk (P : UniformSequence) (X : seminorm.Cauchy) :
    sequenceAction P (point X)=representedAction P X := rfl

def actionRepresentative (P : UniformSequence) (X : seminorm.Cauchy) : seminorm.Cauchy :=
  diagonalCauchy (actionRows P X)

def actionModulus (P : UniformSequence) (X : seminorm.Cauchy) : Q' → Nat :=
  rowLimitRate (actionRows P X)

theorem actionRepresentative_pin (P : UniformSequence) (X : seminorm.Cauchy) :
    (point (actionRepresentative P X))=sequenceAction P (point X) := rfl

theorem sequenceAction_bound (P : UniformSequence) (X : seminorm.Cauchy)
    (epsilon : Q') (he : (0 : Q')<epsilon) (n : Nat) (hn : actionModulus P X epsilon≤n) :
    RCle (completedDist (polynomialOperator (P.polynomial n) (point X))
      (sequenceAction P (point X))) (rat epsilon) := by
  have h := rowLimit_bound (actionRows P X) epsilon he n hn
  rw [actionRows_pin] at h
  exact h

/-- Supplied original input data yields original output data, its pin and explicit rate. -/
def sequenceActionCertificate (P : UniformSequence) (X : seminorm.Cauchy) :
    Σ' Y : seminorm.Cauchy,
      {rate : Q' → Nat // (point Y)=sequenceAction P (point X) ∧
        ∀ epsilon : Q',(0 : Q')<epsilon → ∀ n,rate epsilon≤n →
          RCle (completedDist (polynomialOperator (P.polynomial n) (point X)) (point Y)) (rat epsilon)} :=
  ⟨actionRepresentative P X,⟨actionModulus P X,⟨rfl,sequenceAction_bound P X⟩⟩⟩

theorem sequenceAction_unique (P : UniformSequence) (X : seminorm.Cauchy)
    (L : Completion) (rate : Q' → Nat)
    (h : ∀ epsilon : Q',(0 : Q')<epsilon → ∀ n,rate epsilon≤n →
      RCle (completedDist (polynomialOperator (P.polynomial n) (point X)) L) (rat epsilon)) :
    sequenceAction P (point X)=L := by
  apply rowLimit_eq_of_bound (actionRows P X) L rate
  intro epsilon he n hn
  rw [actionRows_pin]
  exact h epsilon he n hn

/-- Explicit uniform asymptotic equality, not equality of polynomial presentations, suffices. -/
theorem sequenceAction_congr (P Q : UniformSequence) (rate : Q' → Nat)
    (h : ∀ epsilon : Q',(0 : Q')<epsilon → ∀ n,rate epsilon≤n →
      ∀ t : Q',(0 : Q')≤t → t≤1 →
        QPoly.eval (P.polynomial n) t≤QPoly.eval (Q.polynomial n) t+epsilon ∧
        QPoly.eval (Q.polynomial n) t≤QPoly.eval (P.polynomial n) t+epsilon)
    (x : Completion) : sequenceAction P x=sequenceAction Q x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply rowLimits_eq_of_close (actionRows P X) (actionRows Q X)
    (fun epsilon => rate (approximationTolerance X epsilon))
  intro epsilon he n hn
  rw [actionRows_pin,actionRows_pin]
  exact polynomial_close X _ _ epsilon he
    (h _ (approximationTolerance_pos X he) n hn)

theorem sequenceAction_rate_independent (P Q : UniformSequence)
    (h : ∀ n,P.polynomial n=Q.polynomial n) (x : Completion) :
    sequenceAction P x=sequenceAction Q x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply rowLimit_independent
  intro n
  rw [actionRows_pin,actionRows_pin,h n]

def constantSequence (p : QPoly.Poly) : UniformSequence where
  polynomial := fun _ => p
  modulus := fun _ => 0
  cauchy := constant_uniform p

theorem constantSequence_action (p : QPoly.Poly) (x : Completion) :
    sequenceAction (constantSequence p) x=polynomialOperator p x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply sequenceAction_unique _ X _ (fun _ => 0)
  intro epsilon he n _
  change RCle (completedDist (polynomialOperator p (point X)) (polynomialOperator p (point X))) (rat epsilon)
  rw [(completedDist_zero_iff _ _).mpr rfl]
  exact leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_lt he)

def bernsteinSequence (F : CtsMod) (V : MonotoneOmegaVanishing F) : UniformSequence where
  polynomial := bernsteinPoly F
  modulus := bernsteinModulus F V
  cauchy := bernstein_uniformCauchy F V

/-- The new operator equals, rather than replaces, the existing continuous calculus. -/
theorem bernsteinSequence_action (F : CtsMod) (V : MonotoneOmegaVanishing F) (x : Completion) :
    sequenceAction (bernsteinSequence F V) x=continuousAction F V x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply rowLimit_independent (actionRows (bernsteinSequence F V) X) (symbolRows F V X)
  intro n
  rw [actionRows_pin,symbolRows_pin]
  rfl

end YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction.UniformSequence
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction.actionRows
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction.actionRows_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction.representedAction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction.representedAction_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction.sequenceAction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction.sequenceAction_mk
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction.actionRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction.actionModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction.actionRepresentative_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction.sequenceAction_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction.sequenceActionCertificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction.sequenceAction_unique
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction.sequenceAction_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction.sequenceAction_rate_independent
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction.constantSequence
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction.constantSequence_action
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction.bernsteinSequence
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction.bernsteinSequence_action
