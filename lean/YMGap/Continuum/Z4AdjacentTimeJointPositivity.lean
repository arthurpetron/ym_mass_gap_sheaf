/-
# Strict positivity of the genuine adjacent-time joint atom

The two canonical cube roots on adjacent time slices are distinct and
compatible.  Their individual spin-summed activities are strictly positive
at every positive coupling and every cutoff containing the fundamental
label.  The finite compatible-pair occurrence theorem therefore supplies a
strictly positive `(true,true)` atom in the actual physical two-time law.

This is temporal non-vacuity only.  It does not imply positive correlation or
Osterwalder--Schrader positivity.
-/

import YMGap.Continuum.FiniteCompatibilityPairOccurrence
import YMGap.Continuum.Z4AdjacentTimeUnitCubeActivity
import YMGap.Continuum.Z4CouplingParametricSpinSummedCoarseOccurrenceFloor

namespace YMGap.Continuum.Z4AdjacentTimeJointPositivity

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.FiniteCompatibilityPairOccurrence
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.Z4AdjacentTimeUnitCubeActivity
open YMGap.Continuum.Z4AdjacentTimeUnitCubeCylinder
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas
open YMGap.Continuum.Z4CanonicalIncompatibilityWalk
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4CouplingParametricSpinSummedCoarseOccurrenceFloor
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricSpinSummedPinnedLayer
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4DyadicUnitCubeActivity
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4CutoffOneSupportBijection

local infix:50 " ≈ " => Q'.eqv

theorem timeZeroUnitCubeRootAt_activity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling)
    {volume : Nat} (hvolume : 5 ≤ volume) :
    (0 : Q') < canonicalSurfaceActivity coupling volume
      (timeZeroUnitCubeRootAt volume) := by
  have hfirst := canonicalSurfaceActivity_transport coupling
    (n := 4) (m := 5) (by decide)
    dyadicUnitCubeSupportIds_mem_cutoffOneFaceSupports
  have htimeZeroFace : timeZeroUnitCubeSupportIds ∈
      cutoffOneFaceSupports 5 :=
    canonicalSurfacePolymer_mem_faceSupports
      timeZeroUnitCubeSupportIds_canonical
  have hsecond := canonicalSurfaceActivity_transport coupling hvolume
    htimeZeroFace
  have hchain :
      canonicalSurfaceActivity coupling 4 dyadicUnitCubeSupportIds ≈
        canonicalSurfaceActivity coupling volume
          (timeZeroUnitCubeRootAt volume) := by
    exact Q'.eqv_trans _ _ _ hfirst hsecond
  exact Q'.pos_of_lt_of_le
    (dyadicUnitCube_canonicalSurfaceActivity_pos hcoupling)
    (Q'.le_of_eqv hchain)

theorem timeOneUnitCubeRootAt_activity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling)
    {volume : Nat} (hvolume : 5 ≤ volume) :
    (0 : Q') < canonicalSurfaceActivity coupling volume
      (timeOneUnitCubeRootAt volume) := by
  have hbase := adjacentTimeUnitCube_canonicalSurfaceActivity_pos hcoupling
  have hface : adjacentTimeUnitCubeSupportIds ∈ cutoffOneFaceSupports 5 :=
    adjacentTimeUnitCubeSupportIds_mem_cutoffOneFaceSupports
  have htransport := canonicalSurfaceActivity_transport coupling hvolume hface
  unfold timeOneUnitCubeRootAt
  exact Q'.pos_of_lt_of_le hbase (Q'.le_of_eqv htransport)

theorem timeZeroUnitCubeRootAt_spinSummedActivity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling)
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff)
    {volume : Nat} (hvolume : 5 ≤ volume) :
    (0 : Q') < couplingParametricKSupportActivity coupling cutoff volume
      (timeZeroUnitCubeRootAt volume) := by
  have hnonnegative : (0 : Q') ≤ coupling := Q'.le_of_lt hcoupling
  have hface : timeZeroUnitCubeRootAt volume ∈ cutoffOneFaceSupports volume :=
    canonicalSurfacePolymer_mem_faceSupports
      (timeZeroUnitCubeRootAt_canonical hvolume)
  exact Q'.pos_of_lt_of_le
    (timeZeroUnitCubeRootAt_activity_pos hcoupling hvolume)
    (canonicalSurfaceActivity_le_couplingParametricKSupportActivity
      hnonnegative hcutoff hface)

theorem timeOneUnitCubeRootAt_spinSummedActivity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling)
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff)
    {volume : Nat} (hvolume : 5 ≤ volume) :
    (0 : Q') < couplingParametricKSupportActivity coupling cutoff volume
      (timeOneUnitCubeRootAt volume) := by
  have hnonnegative : (0 : Q') ≤ coupling := Q'.le_of_lt hcoupling
  have hface : timeOneUnitCubeRootAt volume ∈ cutoffOneFaceSupports volume :=
    canonicalSurfacePolymer_mem_faceSupports
      (timeOneUnitCubeRootAt_canonical hvolume)
  exact Q'.pos_of_lt_of_le
    (timeOneUnitCubeRootAt_activity_pos hcoupling hvolume)
    (canonicalSurfaceActivity_le_couplingParametricKSupportActivity
      hnonnegative hcutoff hface)

theorem adjacentTime_true_true_event_eq_jointOccurrence
    (volume : Nat) :
    adjacentTimeOutcomeEvent volume true true =
      (fun family =>
        familyContainsPolymerB (timeZeroUnitCubeRootAt volume) family &&
          familyContainsPolymerB (timeOneUnitCubeRootAt volume) family) := by
  rfl

theorem adjacentTime_jointOccurrenceNumerator_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling)
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff)
    {volume : Nat} (hvolume : 5 ≤ volume) :
    (0 : Q') < couplingParametricKCompatibleSupportEventNumerator
      coupling cutoff volume
      (adjacentTimeOutcomeEvent volume true true) := by
  let first := timeZeroUnitCubeRootAt volume
  let second := timeOneUnitCubeRootAt volume
  let event : List (List Nat) → Bool := fun family =>
    memberB family first && memberB family second
  have hnonnegative : (0 : Q') ≤ coupling := Q'.le_of_lt hcoupling
  have hgeneric :
      couplingParametricKSupportActivity coupling cutoff volume first *
          couplingParametricKSupportActivity coupling cutoff volume second ≤
        couplingParametricKCanonicalPolymerEventNumerator
          coupling cutoff volume (canonicalSurfacePolymers volume) event := by
    unfold couplingParametricKCanonicalPolymerEventNumerator event
    exact pair_weight_le_jointOccurrenceNumerator
      (canonicalPolymerCompatibleB volume)
      (canonicalPolymerCompatibleB_symm volume)
      (couplingParametricKSupportActivity coupling cutoff volume)
      (couplingParametricKSupportActivity_nonnegative
        hnonnegative cutoff volume)
      (canonicalSurfacePolymers volume) first second
      (canonicalSurfacePolymers_nodup volume)
      (timeZeroUnitCubeRootAt_canonical hvolume)
      (timeOneUnitCubeRootAt_canonical hvolume)
      (timeSliceRoots_distinct hvolume)
      (timeSliceRoots_compatible hvolume)
  have hproductPos : (0 : Q') <
      couplingParametricKSupportActivity coupling cutoff volume first *
        couplingParametricKSupportActivity coupling cutoff volume second :=
    Q'.mul_pos
      (timeZeroUnitCubeRootAt_spinSummedActivity_pos
        hcoupling cutoff hcutoff hvolume)
      (timeOneUnitCubeRootAt_spinSummedActivity_pos
        hcoupling cutoff hcutoff hvolume)
  have hgenericPos : (0 : Q') <
      couplingParametricKCanonicalPolymerEventNumerator
        coupling cutoff volume (canonicalSurfacePolymers volume) event :=
    Q'.pos_of_lt_of_le hproductPos hgeneric
  have hbridge :=
    couplingParametricKCanonicalPolymerEventNumerator_eqv_compatible
      coupling cutoff volume event
  have hevent : event = adjacentTimeOutcomeEvent volume true true := by
    funext family
    apply Bool.eq_iff_iff.mpr
    simp [event, first, second, adjacentTimeOutcomeEvent, unitCubeOutcomeEvent,
      boolOutcomeMatches, familyContainsPolymerB, memberB]
  rw [← hevent]
  exact Q'.pos_of_lt_of_le hgenericPos (Q'.le_of_eqv hbridge)

theorem adjacentTime_compatible_true_true_probability_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling)
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff)
    {volume : Nat} (hvolume : 5 ≤ volume) :
    (0 : Q') < couplingParametricKCompatibleSupportEventProbability
      coupling (Q'.le_of_lt hcoupling) cutoff volume
      (adjacentTimeOutcomeEvent volume true true) := by
  unfold couplingParametricKCompatibleSupportEventProbability
  exact Q'.divPos_pos _ _
    (couplingParametricKCompatibleSupportGasPartition_pos
      (Q'.le_of_lt hcoupling) cutoff volume)
    (adjacentTime_jointOccurrenceNumerator_pos
      hcoupling cutoff hcutoff hvolume)

theorem adjacentTimeJointProbability_true_true_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling)
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff)
    {volume : Nat} (hvolume : 5 ≤ volume) :
    (0 : Q') < adjacentTimeJointProbability coupling
      (Q'.le_of_lt hcoupling) cutoff volume true true := by
  have hcompatible := adjacentTime_compatible_true_true_probability_pos
    hcoupling cutoff hcutoff hvolume
  have hbridge := couplingKFamilyEventProbability_eqv_compatible
    coupling (Q'.le_of_lt hcoupling) cutoff volume
    (adjacentTimeOutcomeEvent volume true true)
  unfold adjacentTimeJointProbability
  exact Q'.pos_of_lt_of_le hcompatible (Q'.ge_of_eqv hbridge)

end YMGap.Continuum.Z4AdjacentTimeJointPositivity

#print axioms YMGap.Continuum.Z4AdjacentTimeJointPositivity.timeZeroUnitCubeRootAt_spinSummedActivity_pos
#print axioms YMGap.Continuum.Z4AdjacentTimeJointPositivity.timeOneUnitCubeRootAt_spinSummedActivity_pos
#print axioms YMGap.Continuum.Z4AdjacentTimeJointPositivity.adjacentTime_jointOccurrenceNumerator_pos
#print axioms YMGap.Continuum.Z4AdjacentTimeJointPositivity.adjacentTimeJointProbability_true_true_pos
