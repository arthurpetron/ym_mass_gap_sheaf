/-
# Constructed continuous action on the FULL ORIGINAL completed carrier

The sharp all-vector polynomial bound constructs Bernstein Cauchy rows
for every supplied original Cauchy representative. Their diagonal gives
the output representative and its convergence rate. Pointwise equality
of polynomial rows proves representative independence, so quotient lift
defines the action on the entire original completion without choosing
representatives. The sharp bound retains the original input norm.

Restriction to the previously constructed cyclic sector is an equality,
not a new model or a density assumption. This is fixed SU(2) nome and
fixed-spacing functional calculus; physical-scale uniformity, continuum
reconstruction and the Clay target remain open.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialBound
import YMGap.Continuum.BF4ExactSlabThermodynamicContinuousAction

namespace YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction

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
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference (vectorRepresentative vectorRepresentative_pin)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity (linearTolerance linearTolerance_pos linearTolerance_budget)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialCarrierLimit (squareTolerance squareTolerance_pos squareTolerance_budget)
open YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation (normCap normCap_nonnegative norm_le_cap)
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorBernsteinMoments (scale_rational)
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialBound
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinLimitPairing (bernsteinPoly_abs_bound)
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousAction (rowLimit_norm_upper)

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)
local notation "point" X => Quotient.mk seminorm.completionSetoid X

/-- Computed from the supplied representative, not selected from its quotient. -/
def approximationTolerance (X : seminorm.Cauchy) (epsilon : Q') : Q' :=
  squareTolerance (linearTolerance (normCap X) (normCap_nonnegative X) epsilon)

theorem approximationTolerance_pos (X : seminorm.Cauchy) {epsilon : Q'} (he : (0 : Q')<epsilon) :
    (0 : Q')<approximationTolerance X epsilon :=
  squareTolerance_pos _ (linearTolerance_pos _ _ he)

theorem approximationTolerance_budget (X : seminorm.Cauchy) {epsilon : Q'} (he : (0 : Q')<epsilon) :
    (approximationTolerance X epsilon*approximationTolerance X epsilon)*normCap X≤epsilon :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
    (squareTolerance_budget _ (linearTolerance_pos _ _ he)) (normCap_nonnegative X))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (linearTolerance_budget _ (normCap_nonnegative X) he))

theorem polynomial_close (X : seminorm.Cauchy) (p q : QPoly.Poly)
    (epsilon : Q') (he : (0 : Q')<epsilon)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 →
      QPoly.eval p t≤QPoly.eval q t+approximationTolerance X epsilon ∧
      QPoly.eval q t≤QPoly.eval p t+approximationTolerance X epsilon) :
    RCle (completedDist (polynomialOperator p (point X)) (polynomialOperator q (point X))) (rat epsilon) := by
  let M := approximationTolerance X epsilon
  have hb := polynomial_difference_bound (point X) p q M (Q'.le_of_lt (approximationTolerance_pos X he))
    (fun t ht h1 => abs_sub_le_of_bounds (h t ht h1).1 (h t ht h1).2)
  have hc := RCscale_mono (SumOfSquares.q_mul_self_nonneg M) (norm_le_cap X)
  rw [scale_rational] at hc
  exact RCle_trans hb (RCle_trans hc
    (leEv_le_ofQ'_of_approx_le (fun _ => approximationTolerance_budget X he)))

def symbolRows (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : seminorm.Cauchy) : CauchyRows where
  row := fun n => vectorRepresentative X (bernsteinPoly F n) 0
  modulus := fun epsilon => bernsteinModulus F V (approximationTolerance X epsilon)
  isCauchy := by
    intro epsilon he m n hm hn
    simp only [vectorRepresentative_pin]
    exact polynomial_close X _ _ epsilon he
      (bernstein_uniformCauchy F V _ (approximationTolerance_pos X he) m n hm hn)

theorem symbolRows_pin (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : seminorm.Cauchy) (n : Nat) :
    rowPoint (symbolRows F V X) n=polynomialOperator (bernsteinPoly F n) (point X) := vectorRepresentative_pin _ _ _

def representedAction (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : seminorm.Cauchy) : Completion :=
  rowLimit (symbolRows F V X)

theorem representedAction_congr (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (X Y : seminorm.Cauchy) (h : (point X)=(point Y)) : representedAction F V X=representedAction F V Y := by
  apply rowLimit_independent
  intro n
  rw [symbolRows_pin,symbolRows_pin,h]

/-- An actual operator on ALL original completed states; no representative choice. -/
def continuousAction (F : CtsMod) (V : MonotoneOmegaVanishing F) : Completion → Completion :=
  Quotient.lift (representedAction F V) (fun X Y h => representedAction_congr F V X Y (Quotient.sound h))

theorem continuousAction_mk (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : seminorm.Cauchy) :
    continuousAction F V (point X)=representedAction F V X := rfl

def actionRepresentative (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : seminorm.Cauchy) : seminorm.Cauchy :=
  diagonalCauchy (symbolRows F V X)

def actionModulus (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : seminorm.Cauchy) : Q' → Nat :=
  rowLimitRate (symbolRows F V X)

theorem actionRepresentative_pin (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : seminorm.Cauchy) :
    (point (actionRepresentative F V X))=continuousAction F V (point X) := rfl

theorem continuousAction_bound (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : seminorm.Cauchy)
    (epsilon : Q') (he : (0 : Q')<epsilon) (n : Nat) (hn : actionModulus F V X epsilon≤n) :
    RCle (completedDist (polynomialOperator (bernsteinPoly F n) (point X))
      (continuousAction F V (point X))) (rat epsilon) := by
  have h := rowLimit_bound (symbolRows F V X) epsilon he n hn
  rw [symbolRows_pin] at h
  exact h

theorem representedAction_norm_bound (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : seminorm.Cauchy) :
    RCle (completedInner (representedAction F V X) (representedAction F V X))
      (RCscale (F.bound*F.bound) (completedInner (point X) (point X))) := by
  apply rowLimit_norm_upper (symbolRows F V X)
  intro n
  rw [symbolRows_pin]
  exact polynomial_norm_bound (point X) _ F.bound (bound_nonneg F) (bernsteinPoly_abs_bound F n)

theorem continuousAction_norm_bound (F : CtsMod) (V : MonotoneOmegaVanishing F) (x : Completion) :
    RCle (completedInner (continuousAction F V x) (continuousAction F V x))
      (RCscale (F.bound*F.bound) (completedInner x x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact representedAction_norm_bound F V X

/-- Supplied input data yields output data with its pin, explicit rate and sharp norm bound. -/
def continuousActionCertificate (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : seminorm.Cauchy) :
    Σ' Y : seminorm.Cauchy,
      {rate : Q' → Nat // (point Y)=continuousAction F V (point X) ∧
        (∀ epsilon : Q',(0 : Q')<epsilon → ∀ n,rate epsilon≤n →
          RCle (completedDist (polynomialOperator (bernsteinPoly F n) (point X)) (point Y)) (rat epsilon)) ∧
        RCle (completedInner (point Y) (point Y))
          (RCscale (F.bound*F.bound) (completedInner (point X) (point X)))} :=
  ⟨actionRepresentative F V X,⟨actionModulus F V X,
    ⟨rfl,continuousAction_bound F V X,continuousAction_norm_bound F V (point X)⟩⟩⟩

/-- The former cyclic action is the restriction of this SAME full-carrier operator. -/
theorem continuousAction_cyclic (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (X : BF4ExactSlabThermodynamicCyclicPresentation.CyclicPresentation) :
    continuousAction F V (BF4ExactSlabThermodynamicCyclicPresentation.state X)=
      BF4ExactSlabThermodynamicContinuousAction.symbolAction F V X := by
  apply rowLimit_independent
  intro n
  rw [symbolRows_pin,BF4ExactSlabThermodynamicContinuousAction.symbolRows_pin]
  rfl

end YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction.approximationTolerance
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction.approximationTolerance_pos
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction.approximationTolerance_budget
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction.polynomial_close
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction.symbolRows
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction.symbolRows_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction.representedAction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction.representedAction_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction.continuousAction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction.continuousAction_mk
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction.actionRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction.actionModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction.actionRepresentative_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction.continuousAction_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction.representedAction_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction.continuousAction_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction.continuousActionCertificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction.continuousAction_cyclic
