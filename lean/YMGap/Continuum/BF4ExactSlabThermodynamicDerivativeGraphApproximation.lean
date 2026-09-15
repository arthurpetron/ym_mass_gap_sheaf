/-
# Constructed two-coordinate approximation of the ORIGINAL derivative graph

GraphPoint carries ORIGINAL states u,v and the equation J u = T2 v.
It is not a new carrier or a supplied analytic generator. Original T2
injectivity makes the image unique. The old differentiated domain embeds.

The finite preimage sum P_n commutes with J and T2. Consequently the old
domain point with preimage P_n u has state T2 P_n u and image T2 P_n v.
The maximum of the TWO existing residual moduli computes a common degree
and controls both coordinates. Explicit geometric rows converge to the
supplied u and v, without choosing representatives from a quotient.

Maximality, self-adjointness and generation are not inferred from this
equation. This module supplies the approximation consumed by those proofs.
Fixed SU(2), nome 1/1024 and T2-time units; physical calibration, continuum
QFT and all-group Clay remain open.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicDifferentiatedCore

namespace YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow (half)
open YMGap.Continuum.RegularLinearGeometricModulus (halfCutoff halfCutoff_spec)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation (completedDist_two_segment)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicResolvent (defect)
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments (defectPower time_defectPower)
open YMGap.Continuum.BF4ExactSlabThermodynamicRangeApproximation
open YMGap.Continuum.BF4ExactSlabThermodynamicFullSpaceZeroContinuity (transfer_injective residualModulus residual_small)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative (derivativeAction)
open YMGap.Continuum.BF4ExactSlabThermodynamicMeshDerivative (derivativeRepresentative derivativeRepresentative_pin)
open YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeLaws
open YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore (CorePoint)
open YMGap.Continuum.BF4ExactSlabThermodynamicDifferentiatedCore (image)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimeAction (half_power_positive)

local notation "point" X => Quotient.mk seminorm.completionSetoid X
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

structure GraphPoint where
  state : Completion
  image : Completion
  equation : derivativeAction state=twoStepTransfer image

theorem GraphPoint.image_unique (p q : GraphPoint) (h : p.state=q.state) : p.image=q.image := by
  apply transfer_injective
  rw [← p.equation,← q.equation,h]

def fromCore (p : CorePoint) : GraphPoint := ⟨p.state,image p,derivative_transfer p.preimage⟩

theorem derivative_zero : derivativeAction completedZero=completedZero := by
  have h := derivative_smul 0 completedZero
  simpa only [completedSmul_zero] using h

theorem derivative_sub (x y : Completion) :
    derivativeAction (completedSub x y)=completedSub (derivativeAction x) (derivativeAction y) := by
  unfold completedSub completedNeg
  rw [derivative_add,derivative_smul]

theorem derivative_defect (x : Completion) : derivativeAction (defect x)=defect (derivativeAction x) := by
  unfold defect
  rw [derivative_sub,derivative_transfer]

theorem derivative_defectPower (n : Nat) (x : Completion) :
    derivativeAction (defectPower n x)=defectPower n (derivativeAction x) := by
  induction n with
  | zero => rfl
  | succ n ih => change derivativeAction (defect (defectPower n x))=defect (defectPower n (derivativeAction x)); rw [derivative_defect,ih]

theorem derivative_partialPreimage (n : Nat) (x : Completion) :
    derivativeAction (partialPreimage n x)=partialPreimage n (derivativeAction x) := by
  induction n with
  | zero => exact derivative_zero
  | succ n ih => rw [partialPreimage,derivative_add,ih,derivative_defectPower]; rfl

theorem partialPreimage_transfer (n : Nat) (x : Completion) :
    partialPreimage n (twoStepTransfer x)=twoStepTransfer (partialPreimage n x) := by
  induction n with
  | zero => exact (completedTime_zeroState 2).symm
  | succ n ih =>
      change completedAdd (partialPreimage n (twoStepTransfer x)) (defectPower n (twoStepTransfer x))=
        completedTime 2 (completedAdd (partialPreimage n x) (defectPower n x))
      rw [completedTime_add,ih,time_defectPower]
      rfl

/-- One computed degree for the state AND image residuals. -/
def graphDegree (U V : seminorm.Cauchy) (epsilon : Q') : Nat :=
  max (residualModulus U epsilon) (residualModulus V epsilon)

def preimage (U V : seminorm.Cauchy) (epsilon : Q') : seminorm.Cauchy :=
  partialPreimageCauchy (graphDegree U V epsilon) U

def approximant (U V : seminorm.Cauchy) (epsilon : Q') : CorePoint := ⟨point (preimage U V epsilon)⟩

theorem approximant_image (U V : seminorm.Cauchy)
    (h : derivativeAction (point U)=twoStepTransfer (point V)) (epsilon : Q') :
    image (approximant U V epsilon)=twoStepTransfer (partialPreimage (graphDegree U V epsilon) (point V)) := by
  change derivativeAction (point (partialPreimageCauchy (graphDegree U V epsilon) U))=_
  rw [partialPreimageCauchy_pin,derivative_partialPreimage,h,partialPreimage_transfer]

theorem state_error (U V : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q')<epsilon) :
    RCle (completedDist (approximant U V epsilon).state (point U)) (rat epsilon) := by
  rw [completedDist_symm]
  change RCle (completedDist (point U) (twoStepTransfer (point (partialPreimageCauchy (graphDegree U V epsilon) U)))) _
  rw [partialPreimageCauchy_pin,partialPreimage_distance]
  exact residual_small U epsilon he _ (Nat.le_max_left _ _)

theorem image_error (U V : seminorm.Cauchy)
    (h : derivativeAction (point U)=twoStepTransfer (point V)) (epsilon : Q') (he : (0 : Q')<epsilon) :
    RCle (completedDist (image (approximant U V epsilon)) (point V)) (rat epsilon) := by
  rw [approximant_image U V h,completedDist_symm,partialPreimage_distance]
  exact residual_small V epsilon he _ (Nat.le_max_right _ _)

def approximationData (U V : seminorm.Cauchy)
    (h : derivativeAction (point U)=twoStepTransfer (point V)) (epsilon : Q') (he : (0 : Q')<epsilon) :
    Σ' W : seminorm.Cauchy,
      (RCle (completedDist (twoStepTransfer (point W)) (point U)) (rat epsilon)) ×'
      (RCle (completedDist (derivativeAction (point W)) (point V)) (rat epsilon)) :=
  ⟨preimage U V epsilon,state_error U V epsilon he,image_error U V h epsilon he⟩

theorem geometric_error_small (Y : seminorm.Cauchy) (r : Nat → seminorm.Cauchy)
    (h : ∀ n,RCle (completedDist (point (r n)) (point Y)) (rat (half^n)))
    (epsilon : Q') (he : (0 : Q')<epsilon) (n : Nat) (hn : halfCutoff epsilon≤n) :
    RCle (completedDist (point (r n)) (point Y)) (rat epsilon) :=
  RCle_trans (h n) (leEv_le_ofQ'_of_approx_le (fun _ =>
    Q'.le_trans' _ _ _ (half_pow_antitone _ n hn) (halfCutoff_spec epsilon he)))

/-- Geometric approximations become represented Cauchy rows with an explicit outer modulus. -/
def geometricRows (Y : seminorm.Cauchy) (r : Nat → seminorm.Cauchy)
    (h : ∀ n,RCle (completedDist (point (r n)) (point Y)) (rat (half^n))) : CauchyRows where
  row := r
  modulus := fun epsilon => halfCutoff (quarter epsilon)
  isCauchy := by
    intro epsilon he m n hm hn
    apply completedDist_two_segment _ (point Y) _ epsilon
    · exact geometric_error_small Y r h _ (quarter_pos he) m hm
    · rw [completedDist_symm]
      exact geometric_error_small Y r h _ (quarter_pos he) n hn

theorem geometricRows_limit (Y : seminorm.Cauchy) (r : Nat → seminorm.Cauchy)
    (h : ∀ n,RCle (completedDist (point (r n)) (point Y)) (rat (half^n))) :
    rowLimit (geometricRows Y r h)=(point Y) :=
  rowLimit_eq_of_bound _ _ halfCutoff (geometric_error_small Y r h)

def stateRows (U V : seminorm.Cauchy) : CauchyRows :=
  geometricRows U (fun n => timeCauchy 2 (preimage U V (half^n)))
    (fun n => state_error U V (half^n) (half_power_positive n))

def imageRows (U V : seminorm.Cauchy) (h : derivativeAction (point U)=twoStepTransfer (point V)) : CauchyRows :=
  geometricRows V (fun n => derivativeRepresentative (preimage U V (half^n)))
    (fun n => image_error U V h (half^n) (half_power_positive n))

theorem stateRows_pin (U V : seminorm.Cauchy) (n : Nat) :
    rowPoint (stateRows U V) n=(approximant U V (half^n)).state := rfl

theorem imageRows_pin (U V : seminorm.Cauchy) (h : derivativeAction (point U)=twoStepTransfer (point V)) (n : Nat) :
    rowPoint (imageRows U V h) n=image (approximant U V (half^n)) := rfl

theorem stateRows_limit (U V : seminorm.Cauchy) : rowLimit (stateRows U V)=(point U) :=
  geometricRows_limit _ _ _

theorem imageRows_limit (U V : seminorm.Cauchy) (h : derivativeAction (point U)=twoStepTransfer (point V)) :
    rowLimit (imageRows U V h)=(point V) := geometricRows_limit _ _ _

end YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation.GraphPoint
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation.GraphPoint.image_unique
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation.fromCore
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation.derivative_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation.derivative_sub
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation.derivative_defect
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation.derivative_defectPower
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation.derivative_partialPreimage
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation.partialPreimage_transfer
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation.graphDegree
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation.preimage
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation.approximant
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation.approximant_image
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation.state_error
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation.image_error
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation.approximationData
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation.geometric_error_small
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation.geometricRows
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation.geometricRows_limit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation.stateRows
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation.imageRows
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation.stateRows_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation.imageRows_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation.stateRows_limit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation.imageRows_limit
