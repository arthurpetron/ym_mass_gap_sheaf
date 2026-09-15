/-
# An actual dense-domain logarithmic candidate on the ORIGINAL completion

The explicit regularized logarithm polynomials construct a bounded positive
symmetric contraction L by the existing original transfer calculus. They
annihilate the original unit and commute with geometric time. The witnessed
domain consists of ORIGINAL states T2 y, with image L y. Injectivity of the
original T2 proves that image is independent of the witness; the computed
range approximation proves this domain dense. Its operator is rational-
linear, symmetric, positive, and annihilates the original vacuum.

These are constructed operators and proved laws, not an assumed generator
bundle. Identification of this candidate with the positive-time derivative,
self-adjoint closure/maximal domain and the physical Hamiltonian is OPEN.
The notation describes the logarithm series; no equality with a separately
defined scalar logarithm is silently used. SU(2), nome 1/1024, fixed spacing;
physical normalization, continuum QFT and the all-group Clay target stay open.
-/

import YMGap.Continuum.RegularizedLogPolynomial
import YMGap.Continuum.BF4ExactSlabThermodynamicFullSpaceZeroContinuity
import YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRootIdentification
import YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUnit

namespace YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RegularizedLogPolynomial
open YMGap.Continuum.BernsteinSequenceWrap (eval01)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection (unitCauchy unitCauchy_pin)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorPolynomialBound
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUnit (polynomial_unit)
open YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction
open YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicUniformRootAction (intervalAction_contraction)
open YMGap.Continuum.BF4ExactSlabThermodynamicGeometricRootIdentification (sequenceAction_time)
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder
open YMGap.Continuum.BF4ExactSlabThermodynamicFullSpaceZeroContinuity

local notation "B" => completedInner
local notation "point" X => Quotient.mk seminorm.completionSetoid X
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

def regularizedAction : Completion → Completion := sequenceAction regularizedSequence

theorem regularized_add (x y : Completion) :
    regularizedAction (completedAdd x y)=completedAdd (regularizedAction x) (regularizedAction y) :=
  sequenceAction_add _ x y

theorem regularized_smul (c : Q') (x : Completion) :
    regularizedAction (completedSmul c x)=completedSmul c (regularizedAction x) := sequenceAction_smul _ c x

theorem regularized_symmetric (x y : Completion) :
    B (regularizedAction x) y=B x (regularizedAction y) := sequenceAction_symmetric _ x y

theorem regularized_nonnegative (x : Completion) : RCnonneg (B (regularizedAction x) x) :=
  sequenceAction_form_nonnegative _ (fun n t ht h1 => (polynomial_bounds n t ht h1).1) x

theorem regularized_contraction (x : Completion) :
    RCle (B (regularizedAction x) (regularizedAction x)) (B x x) :=
  intervalAction_contraction ⟨regularizedSequence, polynomial_bounds⟩ x

theorem regularized_time (lag : Nat) (x : Completion) :
    regularizedAction (completedTime lag x)=completedTime lag (regularizedAction x) := sequenceAction_time _ lag x

/-- Original output representative and squared-distance convergence rate as data. -/
def regularizedCertificate (X : seminorm.Cauchy) := sequenceActionCertificate regularizedSequence X

theorem regularized_unit : regularizedAction completedUnit=completedZero := by
  change sequenceAction regularizedSequence (point unitCauchy)=completedZero
  apply sequenceAction_unique _ unitCauchy _ (fun _ => 0)
  intro epsilon he n _
  have h : polynomialOperator (polynomial n) completedUnit=completedZero :=
    (polynomial_unit _ 0).trans ((completedSmul_congr (polynomial_one n) _).trans (completedSmul_zero _))
  change RCle (completedDist (polynomialOperator (polynomial n) completedUnit) completedZero) (rat epsilon)
  rw [h, (completedDist_zero_iff _ _).mpr rfl]
  exact leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_lt he)

/-- Positivity of t*p_N(t), passed through the SAME original pairing limits. -/
theorem regularized_transfer_nonnegative (x : Completion) :
    RCnonneg (B (regularizedAction x) (twoStepTransfer x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  have h := rowLimit_pairing_nonnegative (actionRows regularizedSequence X) (constantRows (timeCauchy 2 X)) (by
    intro n
    rw [actionRows_pin, constantRows_pin]
    change RCnonneg (B (polynomialOperator (polynomial n) (point X)) (twoStepTransfer (point X)))
    rw [← operator_coordinate, operator_symmetric, ← operator_mul]
    apply polynomialForm_nonnegative
    intro t ht h1
    exact Q'.le_trans' _ _ _ (Q'.mul_nonneg _ _ (polynomial_bounds n t ht h1).1 ht)
      (Q'.ge_of_eqv (Q'.eqv_trans _ _ _ (QPoly.eval_pmul _ _ _)
        (Q'.mul_eqv_congr_left _ _ _ (eval01 t)))))
  rw [rowLimit_constant] at h
  exact h

/-- A witness for an original domain state, not a replacement physical carrier. -/
structure CorePoint where
  preimage : Completion

def CorePoint.state (p : CorePoint) : Completion := twoStepTransfer p.preimage

def CorePoint.image (p : CorePoint) : Completion := regularizedAction p.preimage

theorem CorePoint.state_injective (p q : CorePoint) (h : p.state=q.state) : p=q := by
  have hp := transfer_injective p.preimage q.preimage h
  cases p
  cases q
  cases hp
  rfl

theorem CorePoint.image_welldef (p q : CorePoint) (h : p.state=q.state) : p.image=q.image :=
  congrArg CorePoint.image (p.state_injective q h)

def CorePoint.add (p q : CorePoint) : CorePoint := ⟨completedAdd p.preimage q.preimage⟩

def CorePoint.smul (c : Q') (p : CorePoint) : CorePoint := ⟨completedSmul c p.preimage⟩

theorem CorePoint.add_laws (p q : CorePoint) :
    (p.add q).state=completedAdd p.state q.state ∧ (p.add q).image=completedAdd p.image q.image :=
  ⟨completedTime_add 2 p.preimage q.preimage, regularized_add p.preimage q.preimage⟩

theorem CorePoint.smul_laws (c : Q') (p : CorePoint) :
    (p.smul c).state=completedSmul c p.state ∧ (p.smul c).image=completedSmul c p.image :=
  ⟨completedTime_smul 2 c p.preimage, regularized_smul c p.preimage⟩

theorem CorePoint.symmetric (p q : CorePoint) : B p.image q.state=B p.state q.image := by
  change B (regularizedAction p.preimage) (completedTime 2 q.preimage)=
    B (completedTime 2 p.preimage) (regularizedAction q.preimage)
  rw [regularized_symmetric, regularized_time, completedTime_symmetric]

theorem CorePoint.nonnegative (p : CorePoint) : RCnonneg (B p.image p.state) :=
  regularized_transfer_nonnegative p.preimage

def vacuumPoint : CorePoint := ⟨completedUnit⟩

theorem vacuumPoint_pin : vacuumPoint.state=completedUnit ∧ vacuumPoint.image=completedZero :=
  ⟨twoStepTransfer_unit, regularized_unit⟩

/-- Original approximate preimages compute actual points in this domain. -/
def coreApproximation (X : seminorm.Cauchy) (epsilon : Q') : CorePoint :=
  ⟨point (approximatePreimage X epsilon)⟩

theorem coreApproximation_bound (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    RCle (completedDist (point X) (coreApproximation X epsilon).state) (rat epsilon) :=
  approximatePreimage_bound X epsilon he

def denseDomainData (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' p : CorePoint, RCle (completedDist (point X) p.state) (rat epsilon) :=
  ⟨coreApproximation X epsilon, coreApproximation_bound X epsilon he⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore.regularizedAction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore.regularized_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore.regularized_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore.regularized_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore.regularized_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore.regularized_contraction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore.regularized_time
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore.regularizedCertificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore.regularized_unit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore.regularized_transfer_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore.CorePoint
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore.CorePoint.state
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore.CorePoint.image
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore.CorePoint.state_injective
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore.CorePoint.image_welldef
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore.CorePoint.add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore.CorePoint.smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore.CorePoint.add_laws
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore.CorePoint.smul_laws
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore.CorePoint.symmetric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore.CorePoint.nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore.vacuumPoint
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore.vacuumPoint_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore.coreApproximation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore.coreApproximation_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore.denseDomainData
