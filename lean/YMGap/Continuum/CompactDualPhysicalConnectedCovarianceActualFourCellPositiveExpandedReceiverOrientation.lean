/-
# Orient supported expanded covariance paths as receiver four-cell rows

The accepted-fiber path carrier has fine sources, accepted fine assignments,
and coarse physical targets.  The same-datum receiver theory instead starts
from an accepted coarse two-replica four-cell row whose first replica is
root-positive.  This module closes the exact event-orientation part of that
interface on the raw support of the actual whole-slab kernel.

A strictly positive raw source-to-target entry constructively supplies an
accepted coarse intertwiner assignment through the already enumerated global
joint carrier.  For a source-cell path the coarse target pair is already in
`11 x 00` order.  For an opposite-cell path it is stored as `01 x 10`, so the
two replicas are swapped to obtain the receiver convention `10 x 01`.
Both resulting pairs are proved members of the established receiver
four-cell carriers.  The swap changes the coarse product weight only by exact
rational commutativity.

This does not yet delete zero-raw-weight paths from the complete path sum,
compare the cross-scale conditional path weight with the same-datum receiver
row weight, or prove a successful-column fraction.  It proves no `O(a)`
estimate, continuum measure, OS/GNS reconstruction, or physical mass gap.

Constructive contract: explicit finite-carrier witnesses, Boolean event
orientation, and exact rational identities only; no choice, `Classical`,
`native_decide`, `sorry`, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.BF4SU2OuterJointCarrierRawRowMass
import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedPaths

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverOrientation

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2OuterJointCarrierEnumeration
open YMGap.Continuum.BF4SU2OuterJointCarrierRawRowMass
open YMGap.Continuum.BF4SU2OuterPositiveRowClosureReduction
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedPaths
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

private theorem not_decide_eq_true_of_not
    {P : Prop} [Decidable P] (hP : ¬ P) : (!decide P) = true := by
  have hfalse : decide P = false := decide_eq_false_iff_not.mpr hP
  rw [hfalse]
  rfl

private theorem not_of_not_decide_eq_true
    {P : Prop} [Decidable P] (hP : (!decide P) = true) : ¬ P := by
  have hfalse : decide P = false := by
    cases hdecision : decide P with
    | false => rfl
    | true =>
        rw [hdecision] at hP
        cases hP
  exact decide_eq_false_iff_not.mp hfalse

/-! ## 1. A positive raw path supplies an accepted coarse endpoint -/

/-- Use the constructive joint-carrier witness selected by a positive raw
entry to attach an accepted coarse intertwiner assignment to its target. -/
def positiveWholeSlabRawTargetExpandedEntry
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (target : PositiveWholeSlabRawTarget S fineState) :
    SlabExpandedFineSourceEntry S.coarse := by
  let selection := target.toJointChannelSelection
  let assignment := jointSelectionFirstFusionWitness selection
  refine ⟨(target.coarseTarget, assignment), ?_⟩
  apply mem_slabExpandedFineSources_iff.mpr
  refine ⟨target.coarseTarget_mem, ?_⟩
  simpa only [slabFineFusionWitnesses] using
    (jointSelectionFirstFusionWitness_mem selection)

/-- Attach root positivity to an accepted expanded entry without changing
either its physical field or its auxiliary assignment. -/
def slabObservablePositiveEntryOfExpanded
    {D : SlabPhysicalData} {rootFaceId : Nat}
    (entry : SlabExpandedFineSourceEntry D)
    (hroot : 0 < entry.1.1 rootFaceId) :
    SlabObservablePositiveSourceEntry D rootFaceId :=
  ⟨entry.1,
    mem_slabObservablePositiveExpandedSources_iff.mpr
      ⟨entry.2, hroot⟩⟩

theorem slabObservablePositiveEntryOfExpanded_weight_eq
    {D : SlabPhysicalData} {rootFaceId : Nat}
    (entry : SlabExpandedFineSourceEntry D)
    (hroot : 0 < entry.1.1 rootFaceId) :
    slabObservablePositiveEntryWeight D
        (slabObservablePositiveEntryOfExpanded entry hroot) =
      slabExpandedFineEntryWeight D entry :=
  rfl

/-! ## 2. Raw-supported source-cell paths -/

/-- A path in the positive accepted-fiber source cell whose two literal
whole-slab raw entries are both strictly positive. -/
structure PositiveExpandedFourCellSourceSupportedPath
    (S : SlabScalePair) (root target : Nat) : Type where
  path : PositiveExpandedPushedPhysicalTwoReplicaPath S
  path_mem :
    path ∈ positiveExpandedPushedFaceRawFourCellSourcePaths
      S root target
  leftRawWeight_pos :
    (0 : Q') < wholeSlabRecouplingRawWeight
      S path.2.1.1.1 path.1.1
  rightRawWeight_pos :
    (0 : Q') < wholeSlabRecouplingRawWeight
      S path.2.2.1.1 path.1.2

namespace PositiveExpandedFourCellSourceSupportedPath

variable {S : SlabScalePair} {root target : Nat}

private theorem targetPair_mem
    (supported : PositiveExpandedFourCellSourceSupportedPath S root target) :
    supported.path.1 ∈
      pushedFaceRawFourCellSourcePairs (S := S) root target :=
  ((mem_cartesian_iff _ _ supported.path).mp supported.path_mem).1

private theorem targetCell_mem
    (supported : PositiveExpandedFourCellSourceSupportedPath S root target) :
    supported.path.1.1 ∈
        S.coarse.physicalLabellings.filter (fun state =>
          slabPhysicalFacePositiveB root state &&
            slabPhysicalFacePositiveB target state) ∧
      supported.path.1.2 ∈
        S.coarse.physicalLabellings.filter (fun state =>
          !(slabPhysicalFacePositiveB root state) &&
            !(slabPhysicalFacePositiveB target state)) := by
  exact (mem_cartesian_iff _ _ supported.path.1).mp supported.targetPair_mem

theorem leftTarget_mem
    (supported : PositiveExpandedFourCellSourceSupportedPath S root target) :
    supported.path.1.1 ∈ S.coarse.physicalLabellings :=
  (List.mem_filter.mp supported.targetCell_mem.1).1

theorem rightTarget_mem
    (supported : PositiveExpandedFourCellSourceSupportedPath S root target) :
    supported.path.1.2 ∈ S.coarse.physicalLabellings :=
  (List.mem_filter.mp supported.targetCell_mem.2).1

theorem left_root_pos
    (supported : PositiveExpandedFourCellSourceSupportedPath S root target) :
    0 < supported.path.1.1 root := by
  have hcell := (List.mem_filter.mp supported.targetCell_mem.1).2
  have hparts := (Bool.and_eq_true _ _).mp hcell
  simpa only [slabPhysicalFacePositiveB, decide_eq_true_eq] using hparts.1

theorem left_target_pos
    (supported : PositiveExpandedFourCellSourceSupportedPath S root target) :
    0 < supported.path.1.1 target := by
  have hcell := (List.mem_filter.mp supported.targetCell_mem.1).2
  have hparts := (Bool.and_eq_true _ _).mp hcell
  simpa only [slabPhysicalFacePositiveB, decide_eq_true_eq] using hparts.2

theorem right_root_not_pos
    (supported : PositiveExpandedFourCellSourceSupportedPath S root target) :
    ¬ 0 < supported.path.1.2 root := by
  have hcell := (List.mem_filter.mp supported.targetCell_mem.2).2
  have hparts := (Bool.and_eq_true _ _).mp hcell
  exact not_of_not_decide_eq_true hparts.1

theorem right_target_not_pos
    (supported : PositiveExpandedFourCellSourceSupportedPath S root target) :
    ¬ 0 < supported.path.1.2 target := by
  have hcell := (List.mem_filter.mp supported.targetCell_mem.2).2
  have hparts := (Bool.and_eq_true _ _).mp hcell
  exact not_of_not_decide_eq_true hparts.2

def leftRawTarget
    (supported : PositiveExpandedFourCellSourceSupportedPath S root target) :
    PositiveWholeSlabRawTarget S supported.path.2.1.1.1 where
  coarseTarget := supported.path.1.1
  coarseTarget_mem := supported.leftTarget_mem
  rawWeight_pos := supported.leftRawWeight_pos

def rightRawTarget
    (supported : PositiveExpandedFourCellSourceSupportedPath S root target) :
    PositiveWholeSlabRawTarget S supported.path.2.2.1.1 where
  coarseTarget := supported.path.1.2
  coarseTarget_mem := supported.rightTarget_mem
  rawWeight_pos := supported.rightRawWeight_pos

def leftExpandedEntry
    (supported : PositiveExpandedFourCellSourceSupportedPath S root target) :
    SlabExpandedFineSourceEntry S.coarse :=
  positiveWholeSlabRawTargetExpandedEntry supported.leftRawTarget

def rightExpandedEntry
    (supported : PositiveExpandedFourCellSourceSupportedPath S root target) :
    SlabExpandedFineSourceEntry S.coarse :=
  positiveWholeSlabRawTargetExpandedEntry supported.rightRawTarget

@[simp] theorem leftExpandedEntry_physical
    (supported : PositiveExpandedFourCellSourceSupportedPath S root target) :
    supported.leftExpandedEntry.1.1 = supported.path.1.1 :=
  rfl

@[simp] theorem rightExpandedEntry_physical
    (supported : PositiveExpandedFourCellSourceSupportedPath S root target) :
    supported.rightExpandedEntry.1.1 = supported.path.1.2 :=
  rfl

def receiverPair
    (supported : PositiveExpandedFourCellSourceSupportedPath S root target) :
    SlabObservableTwoReplicaPair S.coarse root :=
  (slabObservablePositiveEntryOfExpanded supported.leftExpandedEntry
      (by simpa only [leftExpandedEntry_physical] using supported.left_root_pos),
    supported.rightExpandedEntry)

/-- A supported `11 x 00` coarse endpoint is literally a source cell of the
existing same-datum receiver four-cell carrier. -/
theorem receiverPair_mem_fourCellSource
    (supported : PositiveExpandedFourCellSourceSupportedPath S root target) :
    supported.receiverPair ∈
      slabObservableFourCellSourcePairs S.coarse root target := by
  apply (mem_cartesian_iff _ _ supported.receiverPair).mpr
  constructor
  · apply List.mem_filter.mpr
    refine ⟨List.mem_attach _ supported.receiverPair.1, ?_⟩
    unfold SlabObservablePositiveSourceEntry.facePositiveB
    rw [decide_eq_true_eq]
    simpa only [leftExpandedEntry_physical] using supported.left_target_pos
  · apply List.mem_filter.mpr
    refine ⟨List.mem_attach _ supported.receiverPair.2, ?_⟩
    unfold SlabExpandedFineSourceEntry.facePositiveB
    change
      (!decide (0 < supported.rightExpandedEntry.1.1 root) &&
        !decide (0 < supported.rightExpandedEntry.1.1 target)) = true
    apply (Bool.and_eq_true _ _).mpr
    constructor
    · apply not_decide_eq_true_of_not
      simpa only [rightExpandedEntry_physical] using
        supported.right_root_not_pos
    · apply not_decide_eq_true_of_not
      simpa only [rightExpandedEntry_physical] using
        supported.right_target_not_pos

theorem receiverPair_weight_eq
    (supported : PositiveExpandedFourCellSourceSupportedPath S root target) :
    slabObservableTwoReplicaPairWeight S.coarse supported.receiverPair =
      slabExpandedFineEntryWeight S.coarse supported.leftExpandedEntry *
        slabExpandedFineEntryWeight S.coarse supported.rightExpandedEntry := by
  unfold slabObservableTwoReplicaPairWeight receiverPair
  rw [slabObservablePositiveEntryOfExpanded_weight_eq]

end PositiveExpandedFourCellSourceSupportedPath

/-! ## 3. Raw-supported opposite-cell paths and the forced replica swap -/

/-- A path in the accepted-fiber opposite cell whose two literal whole-slab
raw entries are both strictly positive. -/
structure PositiveExpandedFourCellTargetSupportedPath
    (S : SlabScalePair) (root target : Nat) : Type where
  path : PositiveExpandedPushedPhysicalTwoReplicaPath S
  path_mem :
    path ∈ positiveExpandedPushedFaceRawFourCellTargetPaths
      S root target
  leftRawWeight_pos :
    (0 : Q') < wholeSlabRecouplingRawWeight
      S path.2.1.1.1 path.1.1
  rightRawWeight_pos :
    (0 : Q') < wholeSlabRecouplingRawWeight
      S path.2.2.1.1 path.1.2

namespace PositiveExpandedFourCellTargetSupportedPath

variable {S : SlabScalePair} {root target : Nat}

private theorem targetPair_mem
    (supported : PositiveExpandedFourCellTargetSupportedPath S root target) :
    supported.path.1 ∈
      pushedFaceRawFourCellTargetPairs (S := S) root target :=
  ((mem_cartesian_iff _ _ supported.path).mp supported.path_mem).1

private theorem targetCell_mem
    (supported : PositiveExpandedFourCellTargetSupportedPath S root target) :
    supported.path.1.1 ∈
        S.coarse.physicalLabellings.filter (fun state =>
          !(slabPhysicalFacePositiveB root state) &&
            slabPhysicalFacePositiveB target state) ∧
      supported.path.1.2 ∈
        S.coarse.physicalLabellings.filter (fun state =>
          slabPhysicalFacePositiveB root state &&
            !(slabPhysicalFacePositiveB target state)) := by
  exact (mem_cartesian_iff _ _ supported.path.1).mp supported.targetPair_mem

theorem leftTarget_mem
    (supported : PositiveExpandedFourCellTargetSupportedPath S root target) :
    supported.path.1.1 ∈ S.coarse.physicalLabellings :=
  (List.mem_filter.mp supported.targetCell_mem.1).1

theorem rightTarget_mem
    (supported : PositiveExpandedFourCellTargetSupportedPath S root target) :
    supported.path.1.2 ∈ S.coarse.physicalLabellings :=
  (List.mem_filter.mp supported.targetCell_mem.2).1

theorem left_root_not_pos
    (supported : PositiveExpandedFourCellTargetSupportedPath S root target) :
    ¬ 0 < supported.path.1.1 root := by
  have hcell := (List.mem_filter.mp supported.targetCell_mem.1).2
  have hparts := (Bool.and_eq_true _ _).mp hcell
  exact not_of_not_decide_eq_true hparts.1

theorem left_target_pos
    (supported : PositiveExpandedFourCellTargetSupportedPath S root target) :
    0 < supported.path.1.1 target := by
  have hcell := (List.mem_filter.mp supported.targetCell_mem.1).2
  have hparts := (Bool.and_eq_true _ _).mp hcell
  simpa only [slabPhysicalFacePositiveB, decide_eq_true_eq] using hparts.2

theorem right_root_pos
    (supported : PositiveExpandedFourCellTargetSupportedPath S root target) :
    0 < supported.path.1.2 root := by
  have hcell := (List.mem_filter.mp supported.targetCell_mem.2).2
  have hparts := (Bool.and_eq_true _ _).mp hcell
  simpa only [slabPhysicalFacePositiveB, decide_eq_true_eq] using hparts.1

theorem right_target_not_pos
    (supported : PositiveExpandedFourCellTargetSupportedPath S root target) :
    ¬ 0 < supported.path.1.2 target := by
  have hcell := (List.mem_filter.mp supported.targetCell_mem.2).2
  have hparts := (Bool.and_eq_true _ _).mp hcell
  exact not_of_not_decide_eq_true hparts.2

def leftRawTarget
    (supported : PositiveExpandedFourCellTargetSupportedPath S root target) :
    PositiveWholeSlabRawTarget S supported.path.2.1.1.1 where
  coarseTarget := supported.path.1.1
  coarseTarget_mem := supported.leftTarget_mem
  rawWeight_pos := supported.leftRawWeight_pos

def rightRawTarget
    (supported : PositiveExpandedFourCellTargetSupportedPath S root target) :
    PositiveWholeSlabRawTarget S supported.path.2.2.1.1 where
  coarseTarget := supported.path.1.2
  coarseTarget_mem := supported.rightTarget_mem
  rawWeight_pos := supported.rightRawWeight_pos

def leftExpandedEntry
    (supported : PositiveExpandedFourCellTargetSupportedPath S root target) :
    SlabExpandedFineSourceEntry S.coarse :=
  positiveWholeSlabRawTargetExpandedEntry supported.leftRawTarget

def rightExpandedEntry
    (supported : PositiveExpandedFourCellTargetSupportedPath S root target) :
    SlabExpandedFineSourceEntry S.coarse :=
  positiveWholeSlabRawTargetExpandedEntry supported.rightRawTarget

@[simp] theorem leftExpandedEntry_physical
    (supported : PositiveExpandedFourCellTargetSupportedPath S root target) :
    supported.leftExpandedEntry.1.1 = supported.path.1.1 :=
  rfl

@[simp] theorem rightExpandedEntry_physical
    (supported : PositiveExpandedFourCellTargetSupportedPath S root target) :
    supported.rightExpandedEntry.1.1 = supported.path.1.2 :=
  rfl

/-- The opposite coarse pair is stored as `01 x 10`; swap replicas so the
root-positive `10` entry is first, as required by the receiver carrier. -/
def receiverPair
    (supported : PositiveExpandedFourCellTargetSupportedPath S root target) :
    SlabObservableTwoReplicaPair S.coarse root :=
  (slabObservablePositiveEntryOfExpanded supported.rightExpandedEntry
      (by simpa only [rightExpandedEntry_physical] using supported.right_root_pos),
    supported.leftExpandedEntry)

/-- After the forced replica swap, a supported `01 x 10` endpoint is
literally a target cell of the same-datum receiver four-cell carrier. -/
theorem receiverPair_mem_fourCellTarget
    (supported : PositiveExpandedFourCellTargetSupportedPath S root target) :
    supported.receiverPair ∈
      slabObservableFourCellTargetPairs S.coarse root target := by
  apply (mem_cartesian_iff _ _ supported.receiverPair).mpr
  constructor
  · apply List.mem_filter.mpr
    refine ⟨List.mem_attach _ supported.receiverPair.1, ?_⟩
    unfold SlabObservablePositiveSourceEntry.facePositiveB
    change (!decide (0 < supported.rightExpandedEntry.1.1 target)) = true
    apply not_decide_eq_true_of_not
    simpa only [rightExpandedEntry_physical] using
      supported.right_target_not_pos
  · apply List.mem_filter.mpr
    refine ⟨List.mem_attach _ supported.receiverPair.2, ?_⟩
    unfold SlabExpandedFineSourceEntry.facePositiveB
    change
      (!decide (0 < supported.leftExpandedEntry.1.1 root) &&
        decide (0 < supported.leftExpandedEntry.1.1 target)) = true
    apply (Bool.and_eq_true _ _).mpr
    constructor
    · apply not_decide_eq_true_of_not
      simpa only [leftExpandedEntry_physical] using
        supported.left_root_not_pos
    · rw [decide_eq_true_eq]
      simpa only [leftExpandedEntry_physical] using supported.left_target_pos

/-- The orientation swap preserves the coarse two-replica product weight up
to the project's exact rational equivalence. -/
theorem receiverPair_weight_eqv_swapped
    (supported : PositiveExpandedFourCellTargetSupportedPath S root target) :
    slabObservableTwoReplicaPairWeight S.coarse supported.receiverPair ≈
      slabExpandedFineEntryWeight S.coarse supported.leftExpandedEntry *
        slabExpandedFineEntryWeight S.coarse supported.rightExpandedEntry := by
  unfold slabObservableTwoReplicaPairWeight slabObservablePositiveEntryWeight
    receiverPair
  exact Q'.mul_comm_eqv _ _

end PositiveExpandedFourCellTargetSupportedPath

#print axioms positiveWholeSlabRawTargetExpandedEntry
#print axioms slabObservablePositiveEntryOfExpanded
#print axioms slabObservablePositiveEntryOfExpanded_weight_eq
#print axioms PositiveExpandedFourCellSourceSupportedPath
#print axioms PositiveExpandedFourCellSourceSupportedPath.leftTarget_mem
#print axioms PositiveExpandedFourCellSourceSupportedPath.rightTarget_mem
#print axioms PositiveExpandedFourCellSourceSupportedPath.left_root_pos
#print axioms PositiveExpandedFourCellSourceSupportedPath.left_target_pos
#print axioms PositiveExpandedFourCellSourceSupportedPath.right_root_not_pos
#print axioms PositiveExpandedFourCellSourceSupportedPath.right_target_not_pos
#print axioms PositiveExpandedFourCellSourceSupportedPath.leftRawTarget
#print axioms PositiveExpandedFourCellSourceSupportedPath.rightRawTarget
#print axioms PositiveExpandedFourCellSourceSupportedPath.leftExpandedEntry
#print axioms PositiveExpandedFourCellSourceSupportedPath.rightExpandedEntry
#print axioms PositiveExpandedFourCellSourceSupportedPath.receiverPair
#print axioms PositiveExpandedFourCellSourceSupportedPath.receiverPair_mem_fourCellSource
#print axioms PositiveExpandedFourCellSourceSupportedPath.receiverPair_weight_eq
#print axioms PositiveExpandedFourCellTargetSupportedPath
#print axioms PositiveExpandedFourCellTargetSupportedPath.leftTarget_mem
#print axioms PositiveExpandedFourCellTargetSupportedPath.rightTarget_mem
#print axioms PositiveExpandedFourCellTargetSupportedPath.left_root_not_pos
#print axioms PositiveExpandedFourCellTargetSupportedPath.left_target_pos
#print axioms PositiveExpandedFourCellTargetSupportedPath.right_root_pos
#print axioms PositiveExpandedFourCellTargetSupportedPath.right_target_not_pos
#print axioms PositiveExpandedFourCellTargetSupportedPath.leftRawTarget
#print axioms PositiveExpandedFourCellTargetSupportedPath.rightRawTarget
#print axioms PositiveExpandedFourCellTargetSupportedPath.leftExpandedEntry
#print axioms PositiveExpandedFourCellTargetSupportedPath.rightExpandedEntry
#print axioms PositiveExpandedFourCellTargetSupportedPath.receiverPair
#print axioms PositiveExpandedFourCellTargetSupportedPath.receiverPair_mem_fourCellTarget
#print axioms PositiveExpandedFourCellTargetSupportedPath.receiverPair_weight_eqv_swapped

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverOrientation
