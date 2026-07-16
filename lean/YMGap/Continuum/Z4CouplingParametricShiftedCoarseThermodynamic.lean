/-
# Positive shifted coarse-cube occurrence in thermodynamic limits

The activity-matched coarse unit cube is a finite cylinder based in box four.
Its exact all-cutoff, all-volume occurrence floor therefore passes both to the
fixed-cutoff thermodynamic limit and to the simultaneous cutoff/volume
diagonal at the shifted coupling `unitCubeBlockCoupling anchorCoupling`.
-/

import YMGap.Continuum.Z4CouplingParametricCylinderJointCofinal
import YMGap.Continuum.Z4CouplingParametricSpinSummedCoarseOccurrenceFloor

namespace YMGap.Continuum.Z4CouplingParametricShiftedCoarseThermodynamic

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.Z4ActivityMatchedUnitCubeOccurrence
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CouplingParametricContactOccurrenceFloor
open YMGap.Continuum.Z4CouplingParametricCylinderCofinal
open YMGap.Continuum.Z4CouplingParametricCylinderJointCofinal
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricSpinSummedCoarseOccurrenceFloor
open YMGap.Continuum.Z4DyadicUnitCubeBlockCylinderIntertwining
open YMGap.Continuum.Z4SpinSummedCutoffEventBridge
open YMGap.Continuum.Z4SpinSummedCutoffTail
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UnitCubeBareCouplingShift

theorem shiftedCoarseUnitCubeCoupling_nonnegative_local :
    (0 : Q') ≤ unitCubeBlockCoupling anchorCoupling :=
  unitCubeBlockCoupling_nonnegative (by decide)

/-! ## 1. Fixed-cutoff thermodynamic occurrence -/

def shiftedCoarseUnitCubeThermodynamicLimitAtCutoff
    (cutoff : Nat) : CReal :=
  couplingParametricKSpinSummedCylinderCofinalLimit
    (unitCubeBlockCoupling anchorCoupling)
    shiftedCoarseUnitCubeCoupling_nonnegative_local
    anchor_unitCubeBlockCoupling_le cutoff
    unitCubeBlockCylinderRoots_allCanonical
    unitCubeBlockCoarseOccurrencePredicate

@[simp] theorem shiftedCoarseUnitCubeThermodynamicLimitAtCutoff_approx
    (cutoff stage : Nat) :
    (shiftedCoarseUnitCubeThermodynamicLimitAtCutoff cutoff).approx stage =
      couplingParametricKCompatibleSupportEventProbability
        (unitCubeBlockCoupling anchorCoupling)
        shiftedCoarseUnitCubeCoupling_nonnegative_local
        cutoff (4 + stage)
        (familyContainsPolymerB
          (coarseUnitCubeBlockRootAt (4 + stage))) := by
  unfold shiftedCoarseUnitCubeThermodynamicLimitAtCutoff
  rw [couplingParametricKSpinSummedCylinderCofinalLimit_approx]
  unfold couplingParametricKSpinSummedCylinderCofinalSequence
  rw [unitCubeBlock_targetCoarse_eq_occurrence]

theorem activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_thermodynamicAtCutoff
    {cutoff : Nat} (hcutoff : 1 ≤ cutoff) :
    CReal.ofQ' activityMatchedCoarseUnitCubeUniformOccurrenceFloor ≤
      shiftedCoarseUnitCubeThermodynamicLimitAtCutoff cutoff := by
  apply CReal.ofQ'_le_of_approx_ge
  intro stage
  rw [shiftedCoarseUnitCubeThermodynamicLimitAtCutoff_approx]
  exact
    activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_spinSummedProbability
      hcutoff (by omega)

theorem shiftedCoarseUnitCubeThermodynamicLimitAtCutoff_pos
    {cutoff : Nat} (hcutoff : 1 ≤ cutoff) :
    CReal.IsPositive
      (shiftedCoarseUnitCubeThermodynamicLimitAtCutoff cutoff) :=
  ⟨activityMatchedCoarseUnitCubeUniformOccurrenceFloor,
    activityMatchedCoarseUnitCubeUniformOccurrenceFloor_pos,
    activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_thermodynamicAtCutoff
      hcutoff⟩

/-! ## 2. Simultaneous cutoff/volume occurrence -/

def shiftedCoarseUnitCubeJointThermodynamicLimit : CReal :=
  couplingParametricSpinSummedJointCylinderLimit
    (unitCubeBlockCoupling anchorCoupling)
    shiftedCoarseUnitCubeCoupling_nonnegative_local
    anchor_unitCubeBlockCoupling_le
    unitCubeBlockCylinderRoots_allCanonical
    unitCubeBlockCoarseOccurrencePredicate

@[simp] theorem shiftedCoarseUnitCubeJointThermodynamicLimit_approx
    (stage : Nat) :
    shiftedCoarseUnitCubeJointThermodynamicLimit.approx stage =
      couplingParametricKCompatibleSupportEventProbability
        (unitCubeBlockCoupling anchorCoupling)
        shiftedCoarseUnitCubeCoupling_nonnegative_local
        (spinSummedJointCutoff stage (4 + stage)) (4 + stage)
        (familyContainsPolymerB
          (coarseUnitCubeBlockRootAt (4 + stage))) := by
  unfold shiftedCoarseUnitCubeJointThermodynamicLimit
  rw [couplingParametricSpinSummedJointCylinderLimit_approx]
  unfold couplingParametricSpinSummedJointCylinderSequence
  rw [unitCubeBlock_targetCoarse_eq_occurrence]

theorem spinSummedJointCutoff_ge_one_local (precision n : Nat) :
    1 ≤ spinSummedJointCutoff precision n := by
  unfold spinSummedJointCutoff
  exact interactingAdjacentCutoff_ge_one
    (spinSummedJointCutoffStage precision n) n

theorem activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_jointThermodynamicLimit :
    CReal.ofQ' activityMatchedCoarseUnitCubeUniformOccurrenceFloor ≤
      shiftedCoarseUnitCubeJointThermodynamicLimit := by
  apply CReal.ofQ'_le_of_approx_ge
  intro stage
  rw [shiftedCoarseUnitCubeJointThermodynamicLimit_approx]
  exact
    activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_spinSummedProbability
      (spinSummedJointCutoff_ge_one_local stage (4 + stage)) (by omega)

theorem shiftedCoarseUnitCubeJointThermodynamicLimit_pos :
    CReal.IsPositive shiftedCoarseUnitCubeJointThermodynamicLimit :=
  ⟨activityMatchedCoarseUnitCubeUniformOccurrenceFloor,
    activityMatchedCoarseUnitCubeUniformOccurrenceFloor_pos,
    activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_jointThermodynamicLimit⟩

#print axioms shiftedCoarseUnitCubeThermodynamicLimitAtCutoff
#print axioms activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_thermodynamicAtCutoff
#print axioms shiftedCoarseUnitCubeThermodynamicLimitAtCutoff_pos
#print axioms shiftedCoarseUnitCubeJointThermodynamicLimit
#print axioms activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_jointThermodynamicLimit
#print axioms shiftedCoarseUnitCubeJointThermodynamicLimit_pos

end YMGap.Continuum.Z4CouplingParametricShiftedCoarseThermodynamic
