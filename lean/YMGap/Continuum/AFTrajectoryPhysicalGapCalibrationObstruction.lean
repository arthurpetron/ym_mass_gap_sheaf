/-
# A vanishing AF coupling cannot equal a uniformly positive physical gap

The proposed `PhysicalGapTrajectoryIdentification` equates the physical gap
with the shifted AF coupling itself.  The latter tends to zero with the
explicit `afScheduleCutoff` modulus, whereas a `DynamicVacuumSectorPhysicalRateBand`
bounds the same physical gap below by a fixed positive rational.

At the computable cutoff for half that floor, the two values are strictly
separated.  This supplies a finite counterexample to the identification and
also refutes its numerator calibration in the presence of the band.  The
AF-to-exact-log and AF-to-continuum consumers request both incompatible inputs.

Neither input is refuted separately.  The AF scalar variation theorem, the
completed carrier, and the direct physical-gap variation consumer are not
affected.  No Yang--Mills or continuum nonexistence conclusion is asserted.

Constructive contract: explicit rational/Nat witness, existing AF modulus,
no choice, proof holes, new axioms, or trusted external computation.
-/

import YMGap.Continuum.AFTrajectorySummableVariation
import YMGap.Continuum.ContinuumGapModulus

namespace YMGap.Continuum.AFTrajectoryPhysicalGapCalibrationObstruction

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.AFTrajectorySummableVariation
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.ContinuumGapModulus

local infix:50 " ≈ " => Q'.eqv

/-- An explicit scale beyond which the AF coupling is at most half the
positive physical floor. -/
def calibrationObstructionScale
    {half : Nat} {family : DynamicVacuumSectorCompletedFamily half}
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (C : AFTrajectoryCertificate) : Nat :=
  afScheduleCutoff C (band.floor * HalfPow.half)

/-- The AF coupling and the physical gap are strictly separated on the
entire tail starting at the returned scale. -/
theorem shiftedTau_lt_physicalGap_of_obstructionScale_le
    {half : Nat} {family : DynamicVacuumSectorCompletedFamily half}
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (C : AFTrajectoryCertificate) (j : Nat)
    (hj : calibrationObstructionScale band C ≤ j) :
    shiftedTau C j < family.physicalGap j := by
  have hepsilon : (0 : Q') < band.floor * HalfPow.half :=
    Q'.mul_pos band.floor_pos (by decide)
  have htau : shiftedTau C j ≤ band.floor * HalfPow.half :=
    afSchedule_to_zero C _ hepsilon j hj
  have hhalf : band.floor * HalfPow.half < band.floor :=
    YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le
      (Q'.mul_lt_mul_of_pos_left band.floor_pos
        (by decide : HalfPow.half < (1 : Q')))
      (Q'.le_of_eqv (Q'.mul_one_eqv band.floor))
  exact YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le
    (Q'.lt_of_le_of_lt htau hhalf) (band.floor_le_physicalGap j)

/-- A witnessing scale where the proposed equality fails; the scale is
data and does not require elimination of an existential proposition. -/
def physicalGapCalibrationCounterexample
    {half : Nat} {family : DynamicVacuumSectorCompletedFamily half}
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (C : AFTrajectoryCertificate) :
    {j : Nat // ¬ (shiftedTau C j ≈ family.physicalGap j)} := by
  refine ⟨calibrationObstructionScale band C, ?_⟩
  intro heq
  have hlt := shiftedTau_lt_physicalGap_of_obstructionScale_le
    band C (calibrationObstructionScale band C) (Nat.le_refl _)
  have hself : shiftedTau C (calibrationObstructionScale band C) <
      shiftedTau C (calibrationObstructionScale band C) :=
    YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le hlt
      (Q'.ge_of_eqv heq)
  exact (Int.lt_irrefl _) hself

/-- The exact AF identification and a positive physical band on the same
completed family cannot be supplied together. -/
theorem noPhysicalGapTrajectoryIdentification_of_rateBand
    {half : Nat} {family : DynamicVacuumSectorCompletedFamily half}
    (band : DynamicVacuumSectorPhysicalRateBand family)
    {C : AFTrajectoryCertificate}
    (identification : PhysicalGapTrajectoryIdentification family C) : False :=
  (physicalGapCalibrationCounterexample band C).property
    (identification.pointwise (physicalGapCalibrationCounterexample band C).val)

/-- The numerator version has the same obstruction, by the existing exact
positive-spacing cancellation. -/
theorem noPhysicalGapNumeratorCalibration_of_rateBand
    {half : Nat} {family : DynamicVacuumSectorCompletedFamily half}
    (band : DynamicVacuumSectorPhysicalRateBand family)
    {C : AFTrajectoryCertificate}
    (calibration : PhysicalGapNumeratorCalibration family C) : False :=
  noPhysicalGapTrajectoryIdentification_of_rateBand band
    calibration.toIdentification

#print axioms calibrationObstructionScale
#print axioms shiftedTau_lt_physicalGap_of_obstructionScale_le
#print axioms physicalGapCalibrationCounterexample
#print axioms noPhysicalGapTrajectoryIdentification_of_rateBand
#print axioms noPhysicalGapNumeratorCalibration_of_rateBand

end YMGap.Continuum.AFTrajectoryPhysicalGapCalibrationObstruction
