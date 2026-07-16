/-
# Positive centered-state occurrence of the coarse unit cube

The six-face coarse unit cube has an exact activity-matched occurrence floor
at the shifted coupling `unitCubeBlockCoupling anchorCoupling`.  Here the
carrier is placed at the center of every receding box rather than transported
from one corner.  Its canonical support still has six faces, so the generic
contact cover has at most `6 * 25 = 150` candidates.  Contact deletion and
fundamental-root insertion therefore give the same all-cutoff rational floor
at every centered stage.

The stage cylinder is literally the singleton occurrence of that receding
root.  Consequently the rational floor passes through the unconditional
centered cylinder functional and gives a constructive-real strict-positivity
certificate for an explicit local observable.
-/

import YMGap.Continuum.Z4CenteredCoarseUnitCubeActivity
import YMGap.Continuum.Z4CouplingParametricSpinSummedCoarseOccurrenceFloor
import YMGap.Continuum.Z4SignedCenteredCylinderStateLaws

namespace YMGap.Continuum.Z4CenteredCoarseUnitCubeStateNontriviality

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.Z4ActivityMatchedUnitCubeOccurrence
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalContactLayerDeletion
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CenteredCoarseUnitCubeActivity
open YMGap.Continuum.Z4CoarseUnitCubeActivity
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4CouplingParametricContactOccurrenceFloor
open YMGap.Continuum.Z4CouplingParametricSpinSummedCoarseOccurrenceFloor
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricSpinSummedPinnedLayer
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4DyadicUnitCubeActivity
open YMGap.Continuum.Z4DyadicUnitCubeBlockCylinderIntertwining
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SignedCenteredCylinderStateLaws
open YMGap.Continuum.Z4SignedCenteredFixedObservableRecoding
open YMGap.Continuum.Z4SignedCenteredRecedingDiagonal
open YMGap.Continuum.Z4SpinSummedCutoffTail
open YMGap.Continuum.Z4SpinSummedCutoffEventBridge
open YMGap.Continuum.Z4SpinSummedCylinderJointCofinal
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UnitCubeBareCouplingShift

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The base-three singleton chart and its exact stage event -/

def centeredCoarseUnitCubeCylinderRootsAtThree : List (List Nat) :=
  [centeredCoarseUnitCubeRootAtThree]

theorem centeredCoarseUnitCubeCylinderRootsAtThree_allCanonical :
    ∀ root, root ∈ centeredCoarseUnitCubeCylinderRootsAtThree →
      root ∈ canonicalSurfacePolymers 3 := by
  intro root hroot
  rw [List.mem_singleton.mp hroot]
  exact centeredCoarseUnitCubeRootAtThree_mem_canonicalSurfacePolymers

theorem centeredCoarseUnitCube_stageEvent_eq_occurrence
    (stage : Nat) :
    centeredRecedingCylinderEvent 3 stage
        centeredCoarseUnitCubeCylinderRootsAtThree
        unitCubeSingleOccurrencePredicate =
      familyContainsPolymerB
        (recedingCenteredCoarseUnitCubeRoot (3 + stage)) := by
  rfl

/-! ## 2. The explicit `2^150` centered contact cover -/

theorem recedingCenteredCoarseUnitCube_contactCandidates_length_le_one_fifty
    {radius : Nat} (hradius : 3 ≤ radius) :
    (canonicalContactFaceCandidates (centeredBoxBase radius)
      (recedingCenteredCoarseUnitCubeRoot radius)).length ≤ 150 := by
  have hlength := canonicalContactFaceCandidates_length_le
    (centeredBoxBase radius)
    (recedingCenteredCoarseUnitCubeRoot radius)
  rw [recedingCenteredCoarseUnitCubeRoot_length hradius] at hlength
  simpa using hlength

private theorem qpow_le_succ_of_one_le_local {base : Q'}
    (hbase : (1 : Q') ≤ base) (exponent : Nat) :
    base ^ exponent ≤ base ^ (exponent + 1) := by
  rw [Q'.pow_succ]
  have hpow0 : (0 : Q') ≤ base ^ exponent :=
    Q'.pow_nonneg base
      (Q'.le_trans' _ _ _ Q'.zero_le_one hbase) exponent
  have hscaled : (1 : Q') * base ^ exponent ≤
      base * base ^ exponent :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hbase hpow0
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.one_mul_eqv (base ^ exponent))) hscaled

private theorem qpow_add_mono_of_one_le_local {base : Q'}
    (hbase : (1 : Q') ≤ base) (first : Nat) :
    ∀ offset : Nat, base ^ first ≤ base ^ (first + offset)
  | 0 => Q'.le_refl' _
  | offset + 1 => by
      have hindex : first + (offset + 1) =
          (first + offset) + 1 := by omega
      rw [hindex]
      exact Q'.le_trans' _ _ _
        (qpow_add_mono_of_one_le_local hbase first offset)
        (qpow_le_succ_of_one_le_local hbase (first + offset))

private theorem qpow_mono_exponent_of_one_le_local {base : Q'}
    (hbase : (1 : Q') ≤ base) {first second : Nat}
    (hle : first ≤ second) : base ^ first ≤ base ^ second := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact qpow_add_mono_of_one_le_local hbase first offset

theorem recedingCenteredCoarseUnitCube_activity_eqv_dyadicAnchor
    {radius : Nat} (hradius : 3 ≤ radius) :
    canonicalSurfaceActivity
        (unitCubeBlockCoupling anchorCoupling)
        (centeredBoxBase radius)
        (recedingCenteredCoarseUnitCubeRoot radius) ≈
      canonicalSurfaceActivity anchorCoupling 4
        dyadicUnitCubeSupportIds := by
  exact Q'.eqv_trans _ _ _
    (recedingCenteredCoarseUnitCube_activity_eqv
      (unitCubeBlockCoupling anchorCoupling) hradius)
    (Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (coarseUnitCube_canonicalSurfaceActivity_eqv
          (unitCubeBlockCoupling anchorCoupling)))
      (coarse_shifted_activity_eqv_dyadic_activity anchorCoupling))

theorem recedingCenteredCoarseUnitCube_baseActivity_le_spinSummedRootActivity
    {cutoff radius : Nat} (hcutoff : 1 ≤ cutoff)
    (hradius : 3 ≤ radius) :
    canonicalSurfaceActivity anchorCoupling 4
        dyadicUnitCubeSupportIds ≤
      couplingParametricKSupportActivity
        (unitCubeBlockCoupling anchorCoupling) cutoff
        (centeredBoxBase radius)
        (recedingCenteredCoarseUnitCubeRoot radius) := by
  have hroot := recedingCenteredCoarseUnitCubeRoot_canonical hradius
  have hactivity :
      canonicalSurfaceActivity anchorCoupling 4
          dyadicUnitCubeSupportIds ≈
        canonicalSurfaceActivity
          (unitCubeBlockCoupling anchorCoupling)
          (centeredBoxBase radius)
          (recedingCenteredCoarseUnitCubeRoot radius) :=
    Q'.eqv_symm
      (recedingCenteredCoarseUnitCube_activity_eqv_dyadicAnchor hradius)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hactivity)
    (canonicalSurfaceActivity_le_couplingParametricKSupportActivity
      (unitCubeBlockCoupling_nonnegative (by decide)) hcutoff
      (canonicalSurfacePolymer_mem_faceSupports hroot))

theorem recedingCenteredCoarseSpinSummedPartition_le_cost_mul_deleted
    {cutoff radius : Nat} (hradius : 3 ≤ radius) :
    couplingParametricKCanonicalPolymerPartition
        (unitCubeBlockCoupling anchorCoupling) cutoff
        (centeredBoxBase radius)
        (canonicalSurfacePolymers (centeredBoxBase radius)) ≤
      activityMatchedCoarseUnitCubeOccurrenceCost *
        couplingParametricKCanonicalPolymerPartition
          (unitCubeBlockCoupling anchorCoupling) cutoff
          (centeredBoxBase radius)
          (canonicalContactDeletedAmbient (centeredBoxBase radius)
            (recedingCenteredCoarseUnitCubeRoot radius)) := by
  let coupling := unitCubeBlockCoupling anchorCoupling
  let volume := centeredBoxBase radius
  let root := recedingCenteredCoarseUnitCubeRoot radius
  let deleted := canonicalContactDeletedAmbient volume root
  have hcoupling : (0 : Q') ≤ coupling := by
    unfold coupling
    exact unitCubeBlockCoupling_nonnegative (by decide)
  have hraw :=
    couplingParametricKCanonicalPolymerPartition_le_contactDeleted
      hcoupling anchor_unitCubeBlockCoupling_le cutoff volume root
  have hlength :=
    recedingCenteredCoarseUnitCube_contactCandidates_length_le_one_fifty
      hradius
  have hpow :
      (Q'.ofNat 2) ^
          (canonicalContactFaceCandidates volume root).length ≤
        (Q'.ofNat 2) ^ 150 :=
    qpow_mono_exponent_of_one_le_local (by decide) hlength
  have hdeleted0 : (0 : Q') ≤
      couplingParametricKCanonicalPolymerPartition
        coupling cutoff volume deleted :=
    couplingParametricKCanonicalPolymerPartition_nonnegative
      hcoupling cutoff volume deleted
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _ hpow hdeleted0
  unfold activityMatchedCoarseUnitCubeOccurrenceCost
  exact Q'.le_trans' _ _ _ hraw hscaled

/-! ## 3. The all-cutoff centered occurrence floor -/

theorem activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_recedingCenteredProbability
    {cutoff radius : Nat} (hcutoff : 1 ≤ cutoff)
    (hradius : 3 ≤ radius) :
    activityMatchedCoarseUnitCubeUniformOccurrenceFloor ≤
      couplingParametricKCompatibleSupportEventProbability
        (unitCubeBlockCoupling anchorCoupling)
        (unitCubeBlockCoupling_nonnegative (by decide)) cutoff
        (centeredBoxBase radius)
        (familyContainsPolymerB
          (recedingCenteredCoarseUnitCubeRoot radius)) := by
  let coupling := unitCubeBlockCoupling anchorCoupling
  let volume := centeredBoxBase radius
  let root := recedingCenteredCoarseUnitCubeRoot radius
  let fullPartition := couplingParametricKCanonicalPolymerPartition
    coupling cutoff volume (canonicalSurfacePolymers volume)
  let deletedPartition := couplingParametricKCanonicalPolymerPartition
    coupling cutoff volume (canonicalContactDeletedAmbient volume root)
  let genericNumerator :=
    couplingParametricKCanonicalPolymerEventNumerator
      coupling cutoff volume (canonicalSurfacePolymers volume)
      (familyContainsPolymerB root)
  let gasPartition := couplingParametricKCompatibleSupportGasPartition
    coupling cutoff volume
  let numerator := couplingParametricKCompatibleSupportEventNumerator
    coupling cutoff volume (familyContainsPolymerB root)
  have hcoupling : (0 : Q') ≤ coupling := by
    unfold coupling
    exact unitCubeBlockCoupling_nonnegative (by decide)
  have hroot : root ∈ canonicalSurfacePolymers volume := by
    unfold root volume
    exact recedingCenteredCoarseUnitCubeRoot_canonical hradius
  have hdeleted0 : (0 : Q') ≤ deletedPartition := by
    unfold deletedPartition
    exact couplingParametricKCanonicalPolymerPartition_nonnegative
      hcoupling cutoff volume _
  have hpartition : fullPartition ≤
      activityMatchedCoarseUnitCubeOccurrenceCost * deletedPartition := by
    unfold fullPartition deletedPartition volume root
    exact recedingCenteredCoarseSpinSummedPartition_le_cost_mul_deleted
      hradius
  have hinsertion :
      couplingParametricKSupportActivity coupling cutoff volume root *
          deletedPartition ≤ genericNumerator := by
    unfold deletedPartition genericNumerator
    exact couplingParametricKRootActivity_mul_deleted_le_numerator
      hcoupling cutoff hroot
  have hbaseRoot :
      canonicalSurfaceActivity anchorCoupling 4 dyadicUnitCubeSupportIds ≤
        couplingParametricKSupportActivity
          coupling cutoff volume root := by
    unfold coupling volume root
    exact
      recedingCenteredCoarseUnitCube_baseActivity_le_spinSummedRootActivity
        hcutoff hradius
  have hbaseInsertion :
      canonicalSurfaceActivity anchorCoupling 4 dyadicUnitCubeSupportIds *
          deletedPartition ≤ genericNumerator :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hbaseRoot hdeleted0)
      hinsertion
  have hfloor0 : (0 : Q') ≤
      activityMatchedCoarseUnitCubeUniformOccurrenceFloor :=
    Q'.le_of_lt activityMatchedCoarseUnitCubeUniformOccurrenceFloor_pos
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _
    hpartition hfloor0
  have hcollapse :
      activityMatchedCoarseUnitCubeUniformOccurrenceFloor *
          (activityMatchedCoarseUnitCubeOccurrenceCost * deletedPartition) ≈
        canonicalSurfaceActivity anchorCoupling 4
          dyadicUnitCubeSupportIds * deletedPartition := by
    refine Q'.eqv_trans _
      ((activityMatchedCoarseUnitCubeUniformOccurrenceFloor *
          activityMatchedCoarseUnitCubeOccurrenceCost) *
        deletedPartition) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    apply Q'.mul_eqv_congr_right
    unfold activityMatchedCoarseUnitCubeUniformOccurrenceFloor
    exact Q'.divPos_mul_eqv _ _
      activityMatchedCoarseUnitCubeOccurrenceCost_pos
  have hgeneric :
      activityMatchedCoarseUnitCubeUniformOccurrenceFloor *
          fullPartition ≤ genericNumerator :=
    Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollapse) hbaseInsertion)
  have hfullGas : fullPartition ≈ gasPartition := by
    unfold fullPartition gasPartition
    exact couplingParametricKCanonicalPolymerPartition_eqv_compatible
      coupling cutoff volume
  have hgenericNumerator : genericNumerator ≈ numerator := by
    unfold genericNumerator numerator
    exact couplingParametricKCanonicalPolymerEventNumerator_eqv_compatible
      coupling cutoff volume (familyContainsPolymerB root)
  have hmul :
      activityMatchedCoarseUnitCubeUniformOccurrenceFloor * gasPartition ≤
        numerator :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left
          activityMatchedCoarseUnitCubeUniformOccurrenceFloor
          gasPartition fullPartition (Q'.eqv_symm hfullGas)))
      (Q'.le_trans' _ _ _ hgeneric
        (Q'.le_of_eqv hgenericNumerator))
  unfold couplingParametricKCompatibleSupportEventProbability
  exact Q'.le_divPos_of_mul_le numerator gasPartition
    (couplingParametricKCompatibleSupportGasPartition_pos
      hcoupling cutoff volume) hmul

/-! ## 4. Passage to the unconditional centered state -/

theorem centeredCoarseUnitCube_stageCutoff_ge_one (stage : Nat) :
    1 ≤ centeredRecedingStageCutoff 3 stage := by
  unfold centeredRecedingStageCutoff spinSummedJointCutoff
  exact interactingAdjacentCutoff_ge_one
    (spinSummedJointCutoffStage stage
      (centeredRecedingStageBase 3 stage))
    (centeredRecedingStageBase 3 stage)

theorem activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_centeredStage
    (stage : Nat) :
    activityMatchedCoarseUnitCubeUniformOccurrenceFloor ≤
      couplingParametricCenteredRecedingCylinderSequence
        (unitCubeBlockCoupling anchorCoupling)
        (unitCubeBlockCoupling_nonnegative (by decide)) 3
        centeredCoarseUnitCubeCylinderRootsAtThree
        unitCubeSingleOccurrencePredicate stage := by
  unfold couplingParametricCenteredRecedingCylinderSequence
  rw [centeredCoarseUnitCube_stageEvent_eq_occurrence]
  simpa only [centeredRecedingStageBase,
    centeredRecedingStageRadius] using
    (activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_recedingCenteredProbability
      (centeredCoarseUnitCube_stageCutoff_ge_one stage)
      (radius := 3 + stage) (by omega))

/-- The explicit local centered-cylinder occurrence in the unconditional
strong-coupling state at the exact activity-matched bare coupling. -/
def centeredCoarseUnitCubeStateOccurrence : CReal :=
  couplingParametricCenteredCylinderFunctionalAtAnchor
    (unitCubeBlockCoupling anchorCoupling)
    (unitCubeBlockCoupling_nonnegative (by decide))
    anchor_unitCubeBlockCoupling_le
    centeredCoarseUnitCubeCylinderRootsAtThree_allCanonical
    unitCubeSingleOccurrencePredicate

@[simp] theorem centeredCoarseUnitCubeStateOccurrence_approx
    (stage : Nat) :
    centeredCoarseUnitCubeStateOccurrence.approx stage =
      couplingParametricCenteredRecedingCylinderSequence
        (unitCubeBlockCoupling anchorCoupling)
        (unitCubeBlockCoupling_nonnegative (by decide)) 3
        centeredCoarseUnitCubeCylinderRootsAtThree
        unitCubeSingleOccurrencePredicate stage := rfl

theorem activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_centeredState :
    CReal.ofQ' activityMatchedCoarseUnitCubeUniformOccurrenceFloor ≤
      centeredCoarseUnitCubeStateOccurrence := by
  apply CReal.ofQ'_le_of_approx_ge
  intro stage
  rw [centeredCoarseUnitCubeStateOccurrence_approx]
  exact
    activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_centeredStage stage

/-- Constructive strict positivity of a nonconstant local cylinder event in
the full signed-centered strong-coupling state. -/
theorem centeredCoarseUnitCubeStateOccurrence_pos :
    CReal.IsPositive centeredCoarseUnitCubeStateOccurrence :=
  ⟨activityMatchedCoarseUnitCubeUniformOccurrenceFloor,
    activityMatchedCoarseUnitCubeUniformOccurrenceFloor_pos,
    activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_centeredState⟩

#print axioms centeredCoarseUnitCubeCylinderRootsAtThree_allCanonical
#print axioms centeredCoarseUnitCube_stageEvent_eq_occurrence
#print axioms recedingCenteredCoarseUnitCube_contactCandidates_length_le_one_fifty
#print axioms recedingCenteredCoarseUnitCube_activity_eqv_dyadicAnchor
#print axioms recedingCenteredCoarseUnitCube_baseActivity_le_spinSummedRootActivity
#print axioms recedingCenteredCoarseSpinSummedPartition_le_cost_mul_deleted
#print axioms activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_recedingCenteredProbability
#print axioms centeredCoarseUnitCube_stageCutoff_ge_one
#print axioms activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_centeredStage
#print axioms centeredCoarseUnitCubeStateOccurrence
#print axioms activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_centeredState
#print axioms centeredCoarseUnitCubeStateOccurrence_pos

end YMGap.Continuum.Z4CenteredCoarseUnitCubeStateNontriviality
