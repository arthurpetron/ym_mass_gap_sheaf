/-
# The actual conditional transfer on dense cube inputs, as Cauchy data

Each finite cube input has a computed sector presentation. Apply the already
inhabited sector-recoding producer to its constant Cauchy representative,
then use the proved raw comparison. Thus each output is a Cauchy representative,
not a quotient point whose representative must be selected.

The full completed-sector pairing pin identifies all output cross pairings
with the SAME physical conditional operator. The four-pairing difference
identity and exact cancellation of the positive normalization prove the
sharp nonexpansive bound on every signed input difference. No strict gap,
stationary sector vacuum or geometric-time claim follows.
-/

import YMGap.Continuum.BF4PhysicalCubeSectorDensePreimage
import YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing
import YMGap.Continuum.RCBilinearDifference

namespace YMGap.Continuum.BF4PhysicalCubeDenseTransfer

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.RCBilinearDifference
open YMGap.Continuum.BF4PhysicalCubeGNSData
open YMGap.Continuum.BF4PhysicalCubeCompletion
open YMGap.Continuum.BF4PhysicalCubeObservableRealization
open YMGap.Continuum.BF4PhysicalCubeCompletedReflectedRealization
open YMGap.Continuum.BF4PhysicalCubeReflectedCompletion
open YMGap.Continuum.BF4PhysicalCubeSectorComparison
open YMGap.Continuum.BF4PhysicalCubeSectorDensePreimage
open YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedAlgebra
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedModule
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer
open YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTail
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTailInhabited
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local notation "D" => cubeGNSData anchorCoupling (by decide)
local notation "M" => centralPhysicalVacuumSectorCylinderSquaredSeminorm
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "G" => centralPhysicalCutoffLinearSquaredSeminorm
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "J" => cubeToCompleted (w := anchorCoupling) (by decide) (by decide)
local notation "P" => centralPhysicalConcreteAdaptiveCompletedMarkovTransfer
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "E" => completedReflectedForm (w := anchorCoupling) (by decide) (by decide) 0
local notation "TM" => centralPhysicalVacuumSectorCylinderCompletedTransfer
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "lambda" => Quotient.mk CReal.crealSetoid anchorNormalization.value

/-- Existing constructive recoding, with its supplied rate, applied to the
explicit finite preimage. No new analytic premise. -/
def rawActionRep (terms : CubeSpan) : CauchyGNS D :=
  sectorCauchyToRaw ((centralPhysicalVacuumSectorAdaptiveRecodingTailData
    (w := anchorCoupling) (by decide) (by decide) 0).recodedCauchy
    ((M).constant (spanPresentation terms)))

def rawAction (terms : CubeSpan) : CubeCompletion anchorCoupling (by decide) :=
  Quotient.mk (cauchySetoid D) (rawActionRep terms)

theorem rawAction_class (terms : CubeSpan) :
    rawAction terms = sectorToRaw (TM ((M).embedRep (spanPresentation terms))) := rfl

theorem rawAction_reflected (terms : CubeSpan) :
    rawToReflected (rawAction terms) = mappedTransfer ((M).embedRep (spanPresentation terms)) := by
  rw [rawAction_class, rawToReflected_sectorToRaw]
  rfl

private theorem global_action (terms : CubeSpan) :
    centralPhysicalVacuumSectorCylinderCompletionToGlobal
      (TM ((M).embedRep (spanPresentation terms))) = P (J terms) := by
  have h := (centralPhysicalVacuumSectorCylinderTransferLiftData
    (w := anchorCoupling) (by decide) (by decide) 0).intertwines
    ((M).embedRep (spanPresentation terms))
  rw [spanPresentation_global] at h
  exact h

/-- Every output cross pairing uses the original completed physical P. -/
theorem rawAction_pairing (left right : CubeSpan) :
    CReal.RCmul ((D).cinnerCompl (rawAction left) (rawAction right)) lambda =
      E (P (J left)) (P (J right)) := by
  refine Eq.trans (cubeReflectedInner_comparison (rawAction left) (rawAction right)).symm ?_
  rw [rawAction_reflected, rawAction_reflected]
  unfold mappedTransfer
  rw [sectorToReflected_pairing, global_action, global_action]

private def globalSub (x y : (G).Completion) : (G).Completion :=
  completedPhysicalLinearAdd (by decide) (by decide) 0 x
    (completedPhysicalLinearNeg (by decide) (by decide) 0 y)

private theorem global_sub_pairing (x y z : (G).Completion) :
    E (globalSub x y) z = CReal.RCsub (E x z) (E y z) := by
  unfold globalSub completedPhysicalLinearNeg
  rw [completedReflectedForm_add_left, completedReflectedForm_smul_left,
    YMGap.Continuum.RCPositiveContractionOneStep.scale_neg_one]
  rfl

private theorem global_cube_sub (left right : CubeSpan) :
    J ((D).sub left right) = globalSub (J left) (J right) := by
  change (G).embedRep (cubeObservable ((D).sub left right)) =
    (G).embedRep (CentralPhysicalLinearObservable.sub (cubeObservable left) (cubeObservable right))
  apply (G).embedRep_eq_of_null
  apply physicalLinearDistSq_equiv_czero_of_equivalent
  intro state
  exact Q'.eqv_trans _ _ _ (cubeObservable_sub_value left right state)
    (Q'.eqv_symm (sub_value_equiv _ _ state))

private theorem global_transfer_sub (x y : (G).Completion) :
    P (globalSub x y) = globalSub (P x) (P y) := by
  unfold globalSub completedPhysicalLinearNeg
  rw [centralPhysicalConcreteAdaptiveCompletedMarkovTransfer_add,
    centralPhysicalConcreteAdaptiveCompletedMarkovTransfer_smul]

/-- The SAME normalization multiplies the completed output difference norm. -/
theorem rawAction_difference_pin (left right : CubeSpan) :
    CReal.RCmul
      ((D).cinnerCompl ((D).cSub (rawAction left) (rawAction right))
        ((D).cSub (rawAction left) (rawAction right))) lambda =
      E (P (J ((D).sub left right))) (P (J ((D).sub left right))) := by
  rw [difference_diagonal (D).cSub (D).cinnerCompl
    (D).cinnerCompl_cSub_left (D).cinnerCompl_comm]
  rw [mul_sub, mul_sub, mul_sub,
    rawAction_pairing, rawAction_pairing, rawAction_pairing, rawAction_pairing]
  rw [global_cube_sub, global_transfer_sub]
  exact (difference_diagonal globalSub E global_sub_pairing
    (completedReflectedForm_symm (w := anchorCoupling) (by decide) (by decide) 0) _ _).symm

/-- Exact nonexpansiveness in the raw completed squared distance. The
normalization is cancelled, so no 65/64 loss enters this estimate. -/
theorem rawAction_contraction (left right : CubeSpan) :
    CReal.RCle
      ((D).cinnerCompl ((D).cSub (rawAction left) (rawAction right))
        ((D).cSub (rawAction left) (rawAction right)))
      (Quotient.mk CReal.crealSetoid (CReal.ofQ' ((D).distSqQ left right))) := by
  have h := completedReflectedForm_contraction (w := anchorCoupling)
    (by decide) (by decide) 0 (J ((D).sub left right))
  rw [← rawAction_difference_pin, cubeToCompleted_reflected_pairing] at h
  exact cancel_positive_factor anchorNormalization.floor anchorNormalization.floor_pos
    anchorNormalization.lower h

end YMGap.Continuum.BF4PhysicalCubeDenseTransfer

#print axioms YMGap.Continuum.BF4PhysicalCubeDenseTransfer.rawActionRep
#print axioms YMGap.Continuum.BF4PhysicalCubeDenseTransfer.rawAction
#print axioms YMGap.Continuum.BF4PhysicalCubeDenseTransfer.rawAction_class
#print axioms YMGap.Continuum.BF4PhysicalCubeDenseTransfer.rawAction_reflected
#print axioms YMGap.Continuum.BF4PhysicalCubeDenseTransfer.rawAction_pairing
#print axioms YMGap.Continuum.BF4PhysicalCubeDenseTransfer.rawAction_difference_pin
#print axioms YMGap.Continuum.BF4PhysicalCubeDenseTransfer.rawAction_contraction
