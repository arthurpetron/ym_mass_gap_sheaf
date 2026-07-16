/-
# Positive cube occurrence in the simultaneous cutoff/volume limit

The dyadic cube cylinder coordinate is evaluated by the already constructed
diagonal representation-cutoff/thermodynamic-volume `CReal`.  Its finite-stage
event is definitionally the occurrence of the transported 24-face cube.
The cutoff- and volume-uniform rational floor therefore passes directly to
that diagonal limit and proves constructive strict positivity.

This establishes non-vacuity of one explicit local observable in the complete
strong-coupling cylinder state.  It remains a fixed-lattice-spacing result and
does not assert an RG comparison or continuum local field.
-/

import YMGap.Continuum.Z4DyadicUnitCubeCylinderInterface
import YMGap.Continuum.Z4SpinSummedDyadicUnitCubeUniformOccurrenceFloor

namespace YMGap.Continuum.Z4SpinSummedDyadicUnitCubeJointNontriviality

open YMGap.Constructive
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4DyadicUnitCubeActivity
open YMGap.Continuum.Z4DyadicUnitCubeCylinderInterface
open YMGap.Continuum.Z4DyadicUnitCubeUniformOccurrenceFloor
open YMGap.Continuum.Z4SpinSummedCompatibleGas
open YMGap.Continuum.Z4SpinSummedCutoffEventBridge
open YMGap.Continuum.Z4SpinSummedCutoffTail
open YMGap.Continuum.Z4SpinSummedDyadicUnitCubeUniformOccurrenceFloor

/-- Select the occurrence bit of the single cube coordinate. -/
def dyadicUnitCubeOccurrencePredicate : List Bool → Bool
  | [] => false
  | bit :: _ => bit

/-- For the singleton cube cylinder, the Boolean pullback is literally the
transported-polymer occurrence event. -/
theorem dyadicUnitCube_targetCylinderEvent_occurrence (n : Nat) :
    targetCylinderEvent 4 n dyadicUnitCubeCylinderRoots
        dyadicUnitCubeOccurrencePredicate =
      familyContainsPolymerB (dyadicUnitCubeSupportIdsAt n) := by
  rfl

/-- The actual simultaneous spin-cutoff and volume limit of the cube
occurrence probabilities. -/
def spinSummedDyadicUnitCubeOccurrenceLimit : CReal :=
  spinSummedDyadicUnitCubeCylinderLimit
    dyadicUnitCubeOccurrencePredicate

@[simp] theorem spinSummedDyadicUnitCubeOccurrenceLimit_approx
    (stage : Nat) :
    spinSummedDyadicUnitCubeOccurrenceLimit.approx stage =
      parametricKCompatibleSupportEventProbability
        (spinSummedJointCutoff stage (4 + stage)) (4 + stage)
        (familyContainsPolymerB
          (dyadicUnitCubeSupportIdsAt (4 + stage))) := by
  unfold spinSummedDyadicUnitCubeOccurrenceLimit
  rw [spinSummedDyadicUnitCubeCylinderLimit_approx]
  rw [dyadicUnitCube_targetCylinderEvent_occurrence]

theorem spinSummedJointCutoff_ge_one_local (precision n : Nat) :
    1 ≤ spinSummedJointCutoff precision n := by
  unfold spinSummedJointCutoff
  exact interactingAdjacentCutoff_ge_one
    (spinSummedJointCutoffStage precision n) n

/-- The exact cutoff-one floor survives the complete diagonal cutoff/volume
limit. -/
theorem dyadicUnitCubeUniformOccurrenceFloor_le_spinSummedLimit :
    CReal.ofQ' dyadicUnitCubeUniformOccurrenceFloor ≤
      spinSummedDyadicUnitCubeOccurrenceLimit := by
  apply CReal.ofQ'_le_of_approx_ge
  intro stage
  rw [spinSummedDyadicUnitCubeOccurrenceLimit_approx]
  exact dyadicUnitCubeUniformOccurrenceFloor_le_parametricK_probability
    (spinSummedJointCutoff_ge_one_local stage (4 + stage)) (by omega)

/-- Constructive strict positivity of one explicit interacting local event in
the full strong-coupling cylinder state. -/
theorem spinSummedDyadicUnitCubeOccurrenceLimit_pos :
    CReal.IsPositive spinSummedDyadicUnitCubeOccurrenceLimit :=
  ⟨dyadicUnitCubeUniformOccurrenceFloor,
    dyadicUnitCubeUniformOccurrenceFloor_pos,
    dyadicUnitCubeUniformOccurrenceFloor_le_spinSummedLimit⟩

end YMGap.Continuum.Z4SpinSummedDyadicUnitCubeJointNontriviality

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4SpinSummedDyadicUnitCubeJointNontriviality.dyadicUnitCube_targetCylinderEvent_occurrence
#print axioms YMGap.Continuum.Z4SpinSummedDyadicUnitCubeJointNontriviality.spinSummedDyadicUnitCubeOccurrenceLimit
#print axioms YMGap.Continuum.Z4SpinSummedDyadicUnitCubeJointNontriviality.dyadicUnitCubeUniformOccurrenceFloor_le_spinSummedLimit
#print axioms YMGap.Continuum.Z4SpinSummedDyadicUnitCubeJointNontriviality.spinSummedDyadicUnitCubeOccurrenceLimit_pos
