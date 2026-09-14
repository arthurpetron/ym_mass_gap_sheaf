/-
# Continuous action stays in the represented ORIGINAL cyclic sector

At stage n the existing polynomial-action modulus selects an input row
whose image is within 1/(n+1) of the nth Bernstein action. The resulting
polynomial product acts on the SAME original normalized probe. These
polynomial-probe rows have an explicit outer Cauchy modulus and converge
to the already constructed original continuous-action value.

The output presentation and its convergence rate are returned as data.
No closure, image-Cauchy or quotient-choice premise is supplied. This
closes represented-sector preservation, not continuous multiplication,
full-carrier spectral realization or the physical-scale/continuum gap.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicContinuousAction

namespace YMGap.Continuum.BF4ExactSlabThermodynamicContinuousCyclicClosure

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
open YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference (probeRepresentative probeRepresentative_pin)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialRowAction (actionModulus action_bound)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier
open YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousAction
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos invSucc_le_of_den)

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

def cyclicIndex (F : CtsMod) (X : CyclicPresentation) (n : Nat) : Nat :=
  actionModulus (bernsteinPoly F n) X.rows (Q'.invSucc n)

def cyclicPolynomial (F : CtsMod) (X : CyclicPresentation) (n : Nat) : QPoly.Poly :=
  QPoly.pmul (bernsteinPoly F n) (X.polynomial (cyclicIndex F X n))

def cyclicRepresentative (F : CtsMod) (X : CyclicPresentation) (n : Nat) : seminorm.Cauchy :=
  probeRepresentative (cyclicPolynomial F X n)

theorem cyclicRepresentative_pin (F : CtsMod) (X : CyclicPresentation) (n : Nat) :
    Quotient.mk seminorm.completionSetoid (cyclicRepresentative F X n)=
      polynomialOperator (cyclicPolynomial F X n) unitProbe.val := probeRepresentative_pin _

theorem cyclicPolynomial_error (F : CtsMod) (X : CyclicPresentation) (n : Nat) :
    RCle (completedDist (polynomialOperator (cyclicPolynomial F X n) unitProbe.val)
      (polynomialOperator (bernsteinPoly F n) (state X))) (rat (Q'.invSucc n)) := by
  rw [cyclicPolynomial,operator_mul,← X.point_pin]
  exact action_bound _ X.rows _ (Q'.invSucc_pos n) _ (Nat.le_refl _)

theorem cyclicPolynomial_close (F : CtsMod) (X : CyclicPresentation)
    (epsilon : Q') (he : (0 : Q')<epsilon) (n : Nat) (hn : epsilon.den≤n) :
    RCle (completedDist (polynomialOperator (cyclicPolynomial F X n) unitProbe.val)
      (polynomialOperator (bernsteinPoly F n) (state X))) (rat epsilon) :=
  RCle_trans (cyclicPolynomial_error F X n)
    (leEv_le_ofQ'_of_approx_le (fun _ => invSucc_le_of_den he hn))

def cyclicModulus (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : CyclicPresentation)
    (epsilon : Q') : Nat :=
  max ((symbolRows F V X).modulus (quarter (quarter epsilon))) (quarter (quarter epsilon)).den

theorem cyclic_bound (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : CyclicPresentation)
    (epsilon : Q') (he : (0 : Q')<epsilon) (m n : Nat)
    (hm : cyclicModulus F V X epsilon≤m) (hn : cyclicModulus F V X epsilon≤n) :
    RCle (completedDist (polynomialOperator (cyclicPolynomial F X m) unitProbe.val)
      (polynomialOperator (cyclicPolynomial F X n) unitProbe.val)) (rat epsilon) := by
  let delta := quarter (quarter epsilon)
  have hd : (0 : Q')<delta := quarter_pos (quarter_pos he)
  have hleft := cyclicPolynomial_close F X delta hd m (Nat.le_trans (Nat.le_max_right _ _) hm)
  have hright := cyclicPolynomial_close F X delta hd n (Nat.le_trans (Nat.le_max_right _ _) hn)
  rw [completedDist_symm] at hright
  have hmiddle := (symbolRows F V X).isCauchy delta hd m n
    (Nat.le_trans (Nat.le_max_left _ _) hm) (Nat.le_trans (Nat.le_max_left _ _) hn)
  change RCle (completedDist (rowPoint (symbolRows F V X) m) (rowPoint (symbolRows F V X) n)) _ at hmiddle
  rw [symbolRows_pin,symbolRows_pin] at hmiddle
  exact completedDist_three_segment _ _ _ _ epsilon he hleft hmiddle hright

def cyclicRows (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : CyclicPresentation) : CauchyRows where
  row := cyclicRepresentative F X
  modulus := cyclicModulus F V X
  isCauchy := by
    intro epsilon he m n hm hn
    rw [cyclicRepresentative_pin,cyclicRepresentative_pin]
    exact cyclic_bound F V X epsilon he m n hm hn

theorem cyclicRows_pin (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : CyclicPresentation) (n : Nat) :
    rowPoint (cyclicRows F V X) n=polynomialOperator (cyclicPolynomial F X n) unitProbe.val :=
  cyclicRepresentative_pin F X n

def actionPresentation (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : CyclicPresentation) : CyclicPresentation :=
  ⟨cyclicRows F V X,cyclicPolynomial F X,cyclicRows_pin F V X⟩

def presentationModulus (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : CyclicPresentation)
    (epsilon : Q') : Nat :=
  max (symbolModulus F V X (quarter epsilon)) (quarter epsilon).den

theorem presentation_bound (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : CyclicPresentation)
    (epsilon : Q') (he : (0 : Q')<epsilon) (n : Nat) (hn : presentationModulus F V X epsilon≤n) :
    RCle (completedDist (polynomialOperator (cyclicPolynomial F X n) unitProbe.val)
      (symbolAction F V X)) (rat epsilon) :=
  completedDist_two_segment _ _ _ epsilon
    (cyclicPolynomial_close F X _ (quarter_pos he) n (Nat.le_trans (Nat.le_max_right _ _) hn))
    (symbolAction_bound F V X _ (quarter_pos he) n (Nat.le_trans (Nat.le_max_left _ _) hn))

/-- The new presentation denotes the SAME already-constructed continuous-action value. -/
theorem state_actionPresentation (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : CyclicPresentation) :
    state (actionPresentation F V X)=symbolAction F V X := by
  apply rowLimit_eq_of_bound (cyclicRows F V X) _ (presentationModulus F V X)
  intro epsilon he n hn
  rw [cyclicRows_pin]
  exact presentation_bound F V X epsilon he n hn

def actionPresentationCertificate (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : CyclicPresentation) :
    Σ' Y : CyclicPresentation,
      {rate : Q' → Nat // state Y=symbolAction F V X ∧
        ∀ epsilon : Q',(0 : Q')<epsilon → ∀ n,rate epsilon≤n →
          RCle (completedDist (polynomialOperator (Y.polynomial n) unitProbe.val) (state Y)) (rat epsilon)} := by
  refine ⟨actionPresentation F V X,⟨presentationModulus F V X,⟨state_actionPresentation F V X,?_⟩⟩⟩
  intro epsilon he n hn
  rw [state_actionPresentation]
  exact presentation_bound F V X epsilon he n hn

end YMGap.Continuum.BF4ExactSlabThermodynamicContinuousCyclicClosure

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousCyclicClosure.cyclicIndex
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousCyclicClosure.cyclicPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousCyclicClosure.cyclicRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousCyclicClosure.cyclicRepresentative_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousCyclicClosure.cyclicPolynomial_error
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousCyclicClosure.cyclicPolynomial_close
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousCyclicClosure.cyclicModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousCyclicClosure.cyclic_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousCyclicClosure.cyclicRows
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousCyclicClosure.cyclicRows_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousCyclicClosure.actionPresentation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousCyclicClosure.presentationModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousCyclicClosure.presentation_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousCyclicClosure.state_actionPresentation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousCyclicClosure.actionPresentationCertificate
