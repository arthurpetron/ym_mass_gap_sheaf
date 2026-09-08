/-
# Saturate raw-supported receiver endpoints over all coarse assignments

The first receiver orientation attached one constructively selected coarse
intertwiner assignment to each raw-supported physical endpoint.  That is
enough to orient a path, but it creates an artificial coverage defect:
different accepted assignments above the same physical endpoint are absent
from the image even though the path law itself depends only on the physical
endpoint.

This module removes that auxiliary-coordinate loss exactly.  Above each
raw-supported physical endpoint it enumerates every accepted coarse
assignment in both replicas.  The path density is divided by the product of
the two physical endpoint weights and is therefore constant across this
complete assignment fiber.  Exact accepted-fiber disintegration proves that
the density times the full receiver-fiber mass is the original path mass.

The saturated lifts are then pushed back to the existing duplicate-free
receiver carriers.  Their receiver-weighted source and target masses, their
four-cell cross, and the complete connected raw-cross defect are unchanged.
Thus any remaining off-image receiver is missing for a physical endpoint
reason, not because `jointSelectionFirstFusionWitness` selected only one
auxiliary assignment.

This is a finite exact disintegration.  It proves no physical endpoint
surjectivity, no `O(g^2)` calibration estimate, no continuum measure, no
OS/GNS reconstruction, and no Yang--Mills mass gap.

Constructive contract: dependent finite attachment, positive rational
division, and exact finite Fubini only; no choice, `Classical`,
`native_decide`, `sorry`, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberDensity

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturation

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerConditionalKernel
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.BF4SU2OuterJointCarrierEnumeration
open YMGap.Continuum.BF4SU2OuterJointCarrierRawRowMass
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedPaths
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverDensity
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberDensity
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverOrientation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedSupportedPaths
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualRawKernel
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteCoefficientZeroExtension
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

local instance receiverAssignmentSaturationPairDecidableEq
    (D : SlabPhysicalData) (root : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair D root) :=
  slabObservableTwoReplicaPairDecidableEq D root

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem listQSum_member_le_local {A : Type}
    (value : A → Q') (hnonnegative : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {item : A}, item ∈ items →
      value item ≤ listQSum value items
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.add_le_self_of_nonneg (value head)
          (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun candidate _ => hnonnegative candidate))
      · have ih := listQSum_member_le_local value hnonnegative tail htail
        have hmono : listQSum value tail ≤
            value head + listQSum value tail := by
          have hadd := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail)
            (hnonnegative head)
          rwa [Q'.zero_add'] at hadd
        exact Q'.le_trans' _ _ _ ih hmono

/-! ## 1. The complete accepted assignment fiber above a raw target -/

/-- Replace the selected assignment above a positive raw target by any
accepted assignment above the same physical endpoint. -/
def positiveWholeSlabRawTargetExpandedEntryAt
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (rawTarget : PositiveWholeSlabRawTarget S fineState)
    (assignment : {candidate : SlabFusionWitnessAssignment //
      candidate ∈ slabFineFusionWitnesses
        S.coarse rawTarget.coarseTarget}) :
    SlabExpandedFineSourceEntry S.coarse :=
  ⟨(rawTarget.coarseTarget, assignment.1),
    mem_slabExpandedFineSources_iff.mpr
      ⟨rawTarget.coarseTarget_mem, assignment.2⟩⟩

@[simp] theorem positiveWholeSlabRawTargetExpandedEntryAt_physical
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (rawTarget : PositiveWholeSlabRawTarget S fineState)
    (assignment : {candidate : SlabFusionWitnessAssignment //
      candidate ∈ slabFineFusionWitnesses
        S.coarse rawTarget.coarseTarget}) :
    (positiveWholeSlabRawTargetExpandedEntryAt
      rawTarget assignment).1.1 = rawTarget.coarseTarget :=
  rfl

/-- Every accepted assignment above the raw-supported physical endpoint. -/
def positiveWholeSlabRawTargetExpandedEntries
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (rawTarget : PositiveWholeSlabRawTarget S fineState) :
    List (SlabExpandedFineSourceEntry S.coarse) :=
  (slabFineFusionWitnesses
      S.coarse rawTarget.coarseTarget).attach.map
    (positiveWholeSlabRawTargetExpandedEntryAt rawTarget)

theorem positiveWholeSlabRawTargetExpandedEntries_physical
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (rawTarget : PositiveWholeSlabRawTarget S fineState)
    (entry : SlabExpandedFineSourceEntry S.coarse)
    (hentry : entry ∈
      positiveWholeSlabRawTargetExpandedEntries rawTarget) :
    entry.1.1 = rawTarget.coarseTarget := by
  obtain ⟨assignment, _, heq⟩ := List.mem_map.mp hentry
  rw [← heq]
  rfl

/-- Summing the complete accepted assignment fiber gives the physical target
weight, not the weight of one selected assignment. -/
theorem positiveWholeSlabRawTargetExpandedEntries_weight_total
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (rawTarget : PositiveWholeSlabRawTarget S fineState) :
    listQSum (slabExpandedFineEntryWeight S.coarse)
        (positiveWholeSlabRawTargetExpandedEntries rawTarget) ≈
      S.coarse.physicalTerm rawTarget.coarseTarget := by
  unfold positiveWholeSlabRawTargetExpandedEntries
    positiveWholeSlabRawTargetExpandedEntryAt
    slabExpandedFineEntryWeight slabExpandedFineSourceWeight
  rw [listQSum_map]
  refine Q'.eqv_trans _
    (listQSum
      (retainedFineIntertwinerPhysicalFiberWeight
        S.coarse rawTarget.coarseTarget)
      (slabFineFusionWitnesses
        S.coarse rawTarget.coarseTarget)) _ ?_ ?_
  · exact Q'.eqv_of_eq
      (listQSum_attach
        (retainedFineIntertwinerPhysicalFiberWeight
          S.coarse rawTarget.coarseTarget)
        (slabFineFusionWitnesses
          S.coarse rawTarget.coarseTarget))
  · exact retainedFineIntertwinerPhysicalFiberWeight_total
      S.coarse rawTarget.coarseTarget

/-- A positive raw target has strictly positive physical target weight.  The
witness is the already selected accepted assignment, compared with the exact
sum of its complete accepted fiber. -/
theorem positiveWholeSlabRawTarget_physicalTerm_pos
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rawTarget : PositiveWholeSlabRawTarget S fineState) :
    (0 : Q') < S.coarse.physicalTerm rawTarget.coarseTarget := by
  let selected := positiveWholeSlabRawTargetExpandedEntry rawTarget
  have hselectedPos :
      (0 : Q') < slabExpandedFineEntryWeight S.coarse selected :=
    slabExpandedFineEntryWeight_pos_of_coupling_pos
      S.coarse hcoarseCoupling selected
  have hselectedMem : selected.1.2 ∈
      slabFineFusionWitnesses S.coarse rawTarget.coarseTarget :=
    (mem_slabExpandedFineSources_iff.mp selected.2).2
  have hnonnegative : ∀ assignment,
      (0 : Q') ≤ retainedFineIntertwinerPhysicalFiberWeight
        S.coarse rawTarget.coarseTarget assignment := by
    intro assignment
    exact Q'.le_of_lt (by
      simpa only [selected, positiveWholeSlabRawTargetExpandedEntry,
        slabExpandedFineEntryWeight, slabExpandedFineSourceWeight,
        retainedFineIntertwinerPhysicalFiberWeight,
        retainedFineIntertwinerRawWeight] using hselectedPos)
  have hmember := listQSum_member_le_local
    (retainedFineIntertwinerPhysicalFiberWeight
      S.coarse rawTarget.coarseTarget)
    hnonnegative
    (slabFineFusionWitnesses S.coarse rawTarget.coarseTarget)
    hselectedMem
  have htoPhysical :
      retainedFineIntertwinerPhysicalFiberWeight
          S.coarse rawTarget.coarseTarget selected.1.2 ≤
        S.coarse.physicalTerm rawTarget.coarseTarget :=
    Q'.le_trans' _ _ _ hmember
      (Q'.le_of_eqv
        (retainedFineIntertwinerPhysicalFiberWeight_total
          S.coarse rawTarget.coarseTarget))
  exact Q'.pos_of_lt_of_le (by
    simpa only [selected, positiveWholeSlabRawTargetExpandedEntry,
      slabExpandedFineEntryWeight, slabExpandedFineSourceWeight] using
        hselectedPos) htoPhysical

/-! ## 2. Root-oriented two-replica assignment blocks -/

/-- The complete accepted assignment fiber above a root-positive physical
raw target, attached to the established rooted receiver type. -/
def positiveWholeSlabRawTargetPositiveEntries
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (root : Nat) (rawTarget : PositiveWholeSlabRawTarget S fineState)
    (hroot : 0 < rawTarget.coarseTarget root) :
    List (SlabObservablePositiveSourceEntry S.coarse root) :=
  (positiveWholeSlabRawTargetExpandedEntries rawTarget).attach.map fun entry =>
    slabObservablePositiveEntryOfExpanded entry.1
      (by
        rw [positiveWholeSlabRawTargetExpandedEntries_physical
          rawTarget entry.1 entry.2]
        exact hroot)

theorem positiveWholeSlabRawTargetPositiveEntries_physical
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (root : Nat) (rawTarget : PositiveWholeSlabRawTarget S fineState)
    (hroot : 0 < rawTarget.coarseTarget root)
    (entry : SlabObservablePositiveSourceEntry S.coarse root)
    (hentry : entry ∈
      positiveWholeSlabRawTargetPositiveEntries root rawTarget hroot) :
    entry.1.1 = rawTarget.coarseTarget := by
  obtain ⟨expanded, _, heq⟩ := List.mem_map.mp hentry
  rw [← heq]
  exact positiveWholeSlabRawTargetExpandedEntries_physical
    rawTarget expanded.1 expanded.2

theorem positiveWholeSlabRawTargetPositiveEntries_weight_total
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (root : Nat) (rawTarget : PositiveWholeSlabRawTarget S fineState)
    (hroot : 0 < rawTarget.coarseTarget root) :
    listQSum (slabObservablePositiveEntryWeight S.coarse)
        (positiveWholeSlabRawTargetPositiveEntries
          root rawTarget hroot) ≈
      S.coarse.physicalTerm rawTarget.coarseTarget := by
  unfold positiveWholeSlabRawTargetPositiveEntries
  rw [listQSum_map]
  refine Q'.eqv_trans _
    (listQSum (fun entry : {candidate // candidate ∈
        positiveWholeSlabRawTargetExpandedEntries rawTarget} =>
      slabExpandedFineEntryWeight S.coarse entry.1)
      (positiveWholeSlabRawTargetExpandedEntries rawTarget).attach) _ ?_ ?_
  · apply listQSum_congr
    intro entry
    exact Q'.eqv_of_eq
      (slabObservablePositiveEntryOfExpanded_weight_eq entry.1 _)
  refine Q'.eqv_trans _
    (listQSum (slabExpandedFineEntryWeight S.coarse)
      (positiveWholeSlabRawTargetExpandedEntries rawTarget)) _ ?_ ?_
  · exact Q'.eqv_of_eq
      (listQSum_attach
        (slabExpandedFineEntryWeight S.coarse)
        (positiveWholeSlabRawTargetExpandedEntries rawTarget))
  · exact positiveWholeSlabRawTargetExpandedEntries_weight_total rawTarget

/-- All accepted assignment pairs above two physical raw targets, with the
first endpoint oriented at the receiver root. -/
def positiveWholeSlabRawTargetReceiverPairBlock
    {S : SlabScalePair}
    {leftFineState rightFineState : EdgeLabelling}
    (root : Nat)
    (left : PositiveWholeSlabRawTarget S leftFineState)
    (right : PositiveWholeSlabRawTarget S rightFineState)
    (hleftRoot : 0 < left.coarseTarget root) :
    List (SlabObservableTwoReplicaPair S.coarse root) :=
  cartesian
    (positiveWholeSlabRawTargetPositiveEntries
      root left hleftRoot)
    (positiveWholeSlabRawTargetExpandedEntries right)

theorem positiveWholeSlabRawTargetReceiverPairBlock_physical
    {S : SlabScalePair}
    {leftFineState rightFineState : EdgeLabelling}
    (root : Nat)
    (left : PositiveWholeSlabRawTarget S leftFineState)
    (right : PositiveWholeSlabRawTarget S rightFineState)
    (hleftRoot : 0 < left.coarseTarget root)
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (hreceiver : receiver ∈
      positiveWholeSlabRawTargetReceiverPairBlock
        root left right hleftRoot) :
    receiver.1.1.1 = left.coarseTarget ∧
      receiver.2.1.1 = right.coarseTarget := by
  have hparts := (mem_cartesian_iff _ _ receiver).mp hreceiver
  exact
    ⟨positiveWholeSlabRawTargetPositiveEntries_physical
      root left hleftRoot receiver.1 hparts.1,
     positiveWholeSlabRawTargetExpandedEntries_physical
      right receiver.2 hparts.2⟩

/-- The assignment-saturated receiver block has exactly the product of the
two physical target weights. -/
theorem positiveWholeSlabRawTargetReceiverPairBlock_weight_total
    {S : SlabScalePair}
    {leftFineState rightFineState : EdgeLabelling}
    (root : Nat)
    (left : PositiveWholeSlabRawTarget S leftFineState)
    (right : PositiveWholeSlabRawTarget S rightFineState)
    (hleftRoot : 0 < left.coarseTarget root) :
    listQSum (slabObservableTwoReplicaPairWeight S.coarse)
        (positiveWholeSlabRawTargetReceiverPairBlock
          root left right hleftRoot) ≈
      S.coarse.physicalTerm left.coarseTarget *
        S.coarse.physicalTerm right.coarseTarget := by
  refine Q'.eqv_trans _
    (listQSum (slabObservablePositiveEntryWeight S.coarse)
        (positiveWholeSlabRawTargetPositiveEntries
          root left hleftRoot) *
      listQSum (slabExpandedFineEntryWeight S.coarse)
        (positiveWholeSlabRawTargetExpandedEntries right)) _ ?_ ?_
  · simpa only [positiveWholeSlabRawTargetReceiverPairBlock,
      slabObservableTwoReplicaPairWeight] using
        (listQSum_cartesian_product
          (slabObservablePositiveEntryWeight S.coarse)
          (slabExpandedFineEntryWeight S.coarse)
          (positiveWholeSlabRawTargetPositiveEntries
            root left hleftRoot)
          (positiveWholeSlabRawTargetExpandedEntries right))
  · exact mul_eqv_both_local
      (positiveWholeSlabRawTargetPositiveEntries_weight_total
        root left hleftRoot)
      (positiveWholeSlabRawTargetExpandedEntries_weight_total right)

def positiveWholeSlabRawTargetReceiverPairPhysicalWeight
    {S : SlabScalePair}
    {leftFineState rightFineState : EdgeLabelling}
    (left : PositiveWholeSlabRawTarget S leftFineState)
    (right : PositiveWholeSlabRawTarget S rightFineState) : Q' :=
  S.coarse.physicalTerm left.coarseTarget *
    S.coarse.physicalTerm right.coarseTarget

theorem positiveWholeSlabRawTargetReceiverPairPhysicalWeight_pos
    {S : SlabScalePair}
    {leftFineState rightFineState : EdgeLabelling}
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (left : PositiveWholeSlabRawTarget S leftFineState)
    (right : PositiveWholeSlabRawTarget S rightFineState) :
    (0 : Q') <
      positiveWholeSlabRawTargetReceiverPairPhysicalWeight left right :=
  Q'.mul_pos
    (positiveWholeSlabRawTarget_physicalTerm_pos
      hcoarseCoupling left)
    (positiveWholeSlabRawTarget_physicalTerm_pos
      hcoarseCoupling right)

/-! ## 3. Source-cell saturation -/

def positiveExpandedFourCellSourceReceiverAssignmentBlock
    {S : SlabScalePair} {root target : Nat}
    (supported : PositiveExpandedFourCellSourceSupportedPath
      S root target) :
    List (SlabObservableTwoReplicaPair S.coarse root) :=
  positiveWholeSlabRawTargetReceiverPairBlock
    root supported.leftRawTarget supported.rightRawTarget
      supported.left_root_pos

theorem positiveExpandedFourCellSourceReceiverAssignmentBlock_mem
    {S : SlabScalePair} {root target : Nat}
    (supported : PositiveExpandedFourCellSourceSupportedPath
      S root target)
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (hreceiver : receiver ∈
      positiveExpandedFourCellSourceReceiverAssignmentBlock supported) :
    receiver ∈ slabObservableFourCellSourcePairs
      S.coarse root target := by
  have hphysical :=
    positiveWholeSlabRawTargetReceiverPairBlock_physical
      root supported.leftRawTarget supported.rightRawTarget
        supported.left_root_pos receiver hreceiver
  apply (mem_cartesian_iff _ _ receiver).mpr
  constructor
  · apply List.mem_filter.mpr
    refine ⟨List.mem_attach _ receiver.1, ?_⟩
    unfold SlabObservablePositiveSourceEntry.facePositiveB
    rw [decide_eq_true_eq, hphysical.1]
    exact supported.left_target_pos
  · apply List.mem_filter.mpr
    refine ⟨List.mem_attach _ receiver.2, ?_⟩
    unfold SlabExpandedFineSourceEntry.facePositiveB
    rw [hphysical.2]
    have hrootFalse : decide
        (0 < supported.rightRawTarget.coarseTarget root) = false :=
      decide_eq_false_iff_not.mpr supported.right_root_not_pos
    have htargetFalse : decide
        (0 < supported.rightRawTarget.coarseTarget target) = false :=
      decide_eq_false_iff_not.mpr supported.right_target_not_pos
    rw [hrootFalse, htargetFalse]
    rfl

def positiveExpandedFourCellSourceSaturatedReceiverDensity
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    {root target : Nat}
    (supported : PositiveExpandedFourCellSourceSupportedPath
      S root target) : Q' :=
  Q'.divPos
    (positiveExpandedFourCellSourceSupportedPathRawMass
      S hfineCutoff hcoarseCoupling supported)
    (positiveWholeSlabRawTargetReceiverPairPhysicalWeight
      supported.leftRawTarget supported.rightRawTarget)
    (positiveWholeSlabRawTargetReceiverPairPhysicalWeight_pos
      hcoarseCoupling supported.leftRawTarget supported.rightRawTarget)

theorem positiveExpandedFourCellSourceSaturatedAssignmentBlock_mass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    {root target : Nat}
    (supported : PositiveExpandedFourCellSourceSupportedPath
      S root target) :
    listQSum
        (fun receiver =>
          positiveExpandedFourCellSourceSaturatedReceiverDensity
              S hfineCutoff hcoarseCoupling supported *
            slabObservableTwoReplicaPairWeight S.coarse receiver)
        (positiveExpandedFourCellSourceReceiverAssignmentBlock supported) ≈
      positiveExpandedFourCellSourceSupportedPathRawMass
        S hfineCutoff hcoarseCoupling supported := by
  let physicalWeight :=
    positiveWholeSlabRawTargetReceiverPairPhysicalWeight
      supported.leftRawTarget supported.rightRawTarget
  have hphysicalWeightPos : (0 : Q') < physicalWeight :=
    positiveWholeSlabRawTargetReceiverPairPhysicalWeight_pos
      hcoarseCoupling supported.leftRawTarget supported.rightRawTarget
  refine Q'.eqv_trans _
    (positiveExpandedFourCellSourceSaturatedReceiverDensity
        S hfineCutoff hcoarseCoupling supported *
      listQSum (slabObservableTwoReplicaPairWeight S.coarse)
        (positiveExpandedFourCellSourceReceiverAssignmentBlock
          supported)) _ ?_ ?_
  · exact listQSum_mul_left _ _ _
  refine Q'.eqv_trans _
    (positiveExpandedFourCellSourceSaturatedReceiverDensity
        S hfineCutoff hcoarseCoupling supported * physicalWeight) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (by simpa only [physicalWeight,
          positiveExpandedFourCellSourceReceiverAssignmentBlock,
          positiveWholeSlabRawTargetReceiverPairPhysicalWeight] using
        (positiveWholeSlabRawTargetReceiverPairBlock_weight_total
          root supported.leftRawTarget supported.rightRawTarget
            supported.left_root_pos))
  · unfold positiveExpandedFourCellSourceSaturatedReceiverDensity
    exact Q'.divPos_mul_eqv _ physicalWeight hphysicalWeightPos

structure PositiveExpandedFourCellSourceSaturatedReceiverLift
    (S : SlabScalePair) (root target : Nat) : Type where
  supported : PositiveExpandedFourCellSourceSupportedPath S root target
  receiver : SlabObservableTwoReplicaPair S.coarse root
  receiver_mem : receiver ∈
    positiveExpandedFourCellSourceReceiverAssignmentBlock supported

def positiveExpandedFourCellSourceSaturatedReceiverLiftOf
    {S : SlabScalePair} {root target : Nat}
    (supported : PositiveExpandedFourCellSourceSupportedPath S root target)
    (receiver : {candidate // candidate ∈
      positiveExpandedFourCellSourceReceiverAssignmentBlock supported}) :
    PositiveExpandedFourCellSourceSaturatedReceiverLift S root target :=
  { supported := supported
    receiver := receiver.1
    receiver_mem := receiver.2 }

def positiveExpandedFourCellSourceSaturatedReceiverLifts
    (S : SlabScalePair) (root target : Nat) :
    List (PositiveExpandedFourCellSourceSaturatedReceiverLift
      S root target) :=
  (positiveExpandedFourCellSourceSupportedPaths S root target).flatMap
    fun supported =>
      (positiveExpandedFourCellSourceReceiverAssignmentBlock
        supported).attach.map
          (positiveExpandedFourCellSourceSaturatedReceiverLiftOf supported)

def positiveExpandedFourCellSourceSaturatedLiftDensity
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    {root target : Nat}
    (lift : PositiveExpandedFourCellSourceSaturatedReceiverLift
      S root target) : Q' :=
  positiveExpandedFourCellSourceSaturatedReceiverDensity
    S hfineCutoff hcoarseCoupling lift.supported

theorem positiveExpandedFourCellSourceSaturatedReceiverLifts_mass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    listQSum
        (fun lift =>
          positiveExpandedFourCellSourceSaturatedLiftDensity
              S hfineCutoff hcoarseCoupling lift *
            slabObservableTwoReplicaPairWeight
              S.coarse lift.receiver)
        (positiveExpandedFourCellSourceSaturatedReceiverLifts
          S root target) ≈
      listQSum
        (positiveExpandedFourCellSourceSupportedPathRawMass
          S hfineCutoff hcoarseCoupling)
        (positiveExpandedFourCellSourceSupportedPaths S root target) := by
  unfold positiveExpandedFourCellSourceSaturatedReceiverLifts
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap
      (fun lift =>
        positiveExpandedFourCellSourceSaturatedLiftDensity
            S hfineCutoff hcoarseCoupling lift *
          slabObservableTwoReplicaPairWeight S.coarse lift.receiver)
      (fun supported =>
        (positiveExpandedFourCellSourceReceiverAssignmentBlock
          supported).attach.map
            (positiveExpandedFourCellSourceSaturatedReceiverLiftOf
              supported))
      (positiveExpandedFourCellSourceSupportedPaths S root target)) ?_
  apply listQSum_congr
  intro supported
  rw [listQSum_map]
  simpa only [positiveExpandedFourCellSourceSaturatedReceiverLiftOf,
      positiveExpandedFourCellSourceSaturatedLiftDensity] using
    (Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq
        (listQSum_attach
          (fun receiver =>
            positiveExpandedFourCellSourceSaturatedReceiverDensity
                S hfineCutoff hcoarseCoupling supported *
              slabObservableTwoReplicaPairWeight S.coarse receiver)
          (positiveExpandedFourCellSourceReceiverAssignmentBlock
            supported)))
      (positiveExpandedFourCellSourceSaturatedAssignmentBlock_mass
        S hfineCutoff hcoarseCoupling supported))

/-- Assignment-saturated density on the original complete receiver source
carrier.  Coincident physical paths and assignments retain their full list
multiplicity. -/
def positiveExpandedFourCellSourceSaturatedReceiverFiberDensity
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root) : Q' :=
  finiteCoefficientZeroExtension
    (positiveExpandedFourCellSourceSaturatedReceiverLifts
      S root target)
    (positiveExpandedFourCellSourceSaturatedLiftDensity
      S hfineCutoff hcoarseCoupling)
    PositiveExpandedFourCellSourceSaturatedReceiverLift.receiver
    receiver

theorem positiveExpandedFourCellSourceSaturatedReceiverFiberMass_eqv
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    listQSum
        (fun receiver =>
          positiveExpandedFourCellSourceSaturatedReceiverFiberDensity
              S hfineCutoff hcoarseCoupling root target receiver *
            slabObservableTwoReplicaPairWeight S.coarse receiver)
        (slabObservableFourCellSourcePairs S.coarse root target) ≈
      listQSum
        (positiveExpandedFourCellSourceSupportedPathRawMass
          S hfineCutoff hcoarseCoupling)
        (positiveExpandedFourCellSourceSupportedPaths S root target) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun lift =>
        positiveExpandedFourCellSourceSaturatedLiftDensity
            S hfineCutoff hcoarseCoupling lift *
          slabObservableTwoReplicaPairWeight S.coarse lift.receiver)
      (positiveExpandedFourCellSourceSaturatedReceiverLifts
        S root target)) _ ?_ ?_
  · exact finiteCoefficientZeroExtension_reindex_mul
      (positiveExpandedFourCellSourceSaturatedReceiverLifts
        S root target)
      (positiveExpandedFourCellSourceSaturatedLiftDensity
        S hfineCutoff hcoarseCoupling)
      PositiveExpandedFourCellSourceSaturatedReceiverLift.receiver
      (slabObservableFourCellSourcePairs S.coarse root target)
      (slabObservableFourCellSourcePairs_nodup
        S.coarse root target)
      (fun lift _ =>
        positiveExpandedFourCellSourceReceiverAssignmentBlock_mem
          lift.supported lift.receiver lift.receiver_mem)
      (slabObservableTwoReplicaPairWeight S.coarse)
  · exact positiveExpandedFourCellSourceSaturatedReceiverLifts_mass
      S hfineCutoff hcoarseCoupling root target

/-! ## 4. Opposite-cell saturation after the forced replica swap -/

def positiveExpandedFourCellTargetReceiverAssignmentBlock
    {S : SlabScalePair} {root target : Nat}
    (supported : PositiveExpandedFourCellTargetSupportedPath
      S root target) :
    List (SlabObservableTwoReplicaPair S.coarse root) :=
  positiveWholeSlabRawTargetReceiverPairBlock
    root supported.rightRawTarget supported.leftRawTarget
      supported.right_root_pos

theorem positiveExpandedFourCellTargetReceiverAssignmentBlock_mem
    {S : SlabScalePair} {root target : Nat}
    (supported : PositiveExpandedFourCellTargetSupportedPath
      S root target)
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (hreceiver : receiver ∈
      positiveExpandedFourCellTargetReceiverAssignmentBlock supported) :
    receiver ∈ slabObservableFourCellTargetPairs
      S.coarse root target := by
  have hphysical :=
    positiveWholeSlabRawTargetReceiverPairBlock_physical
      root supported.rightRawTarget supported.leftRawTarget
        supported.right_root_pos receiver hreceiver
  apply (mem_cartesian_iff _ _ receiver).mpr
  constructor
  · apply List.mem_filter.mpr
    refine ⟨List.mem_attach _ receiver.1, ?_⟩
    unfold SlabObservablePositiveSourceEntry.facePositiveB
    rw [hphysical.1]
    have htargetFalse : decide
        (0 < supported.rightRawTarget.coarseTarget target) = false :=
      decide_eq_false_iff_not.mpr supported.right_target_not_pos
    rw [htargetFalse]
    rfl
  · apply List.mem_filter.mpr
    refine ⟨List.mem_attach _ receiver.2, ?_⟩
    unfold SlabExpandedFineSourceEntry.facePositiveB
    rw [hphysical.2]
    have hrootFalse : decide
        (0 < supported.leftRawTarget.coarseTarget root) = false :=
      decide_eq_false_iff_not.mpr supported.left_root_not_pos
    have htargetTrue : decide
        (0 < supported.leftRawTarget.coarseTarget target) = true :=
      decide_eq_true supported.left_target_pos
    rw [hrootFalse, htargetTrue]
    rfl

def positiveExpandedFourCellTargetSaturatedReceiverDensity
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    {root target : Nat}
    (supported : PositiveExpandedFourCellTargetSupportedPath
      S root target) : Q' :=
  Q'.divPos
    (positiveExpandedFourCellTargetSupportedPathRawMass
      S hfineCutoff hcoarseCoupling supported)
    (positiveWholeSlabRawTargetReceiverPairPhysicalWeight
      supported.rightRawTarget supported.leftRawTarget)
    (positiveWholeSlabRawTargetReceiverPairPhysicalWeight_pos
      hcoarseCoupling supported.rightRawTarget supported.leftRawTarget)

theorem positiveExpandedFourCellTargetSaturatedAssignmentBlock_mass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    {root target : Nat}
    (supported : PositiveExpandedFourCellTargetSupportedPath
      S root target) :
    listQSum
        (fun receiver =>
          positiveExpandedFourCellTargetSaturatedReceiverDensity
              S hfineCutoff hcoarseCoupling supported *
            slabObservableTwoReplicaPairWeight S.coarse receiver)
        (positiveExpandedFourCellTargetReceiverAssignmentBlock supported) ≈
      positiveExpandedFourCellTargetSupportedPathRawMass
        S hfineCutoff hcoarseCoupling supported := by
  let physicalWeight :=
    positiveWholeSlabRawTargetReceiverPairPhysicalWeight
      supported.rightRawTarget supported.leftRawTarget
  have hphysicalWeightPos : (0 : Q') < physicalWeight :=
    positiveWholeSlabRawTargetReceiverPairPhysicalWeight_pos
      hcoarseCoupling supported.rightRawTarget supported.leftRawTarget
  refine Q'.eqv_trans _
    (positiveExpandedFourCellTargetSaturatedReceiverDensity
        S hfineCutoff hcoarseCoupling supported *
      listQSum (slabObservableTwoReplicaPairWeight S.coarse)
        (positiveExpandedFourCellTargetReceiverAssignmentBlock
          supported)) _ ?_ ?_
  · exact listQSum_mul_left _ _ _
  refine Q'.eqv_trans _
    (positiveExpandedFourCellTargetSaturatedReceiverDensity
        S hfineCutoff hcoarseCoupling supported * physicalWeight) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (by simpa only [physicalWeight,
          positiveExpandedFourCellTargetReceiverAssignmentBlock,
          positiveWholeSlabRawTargetReceiverPairPhysicalWeight] using
        (positiveWholeSlabRawTargetReceiverPairBlock_weight_total
          root supported.rightRawTarget supported.leftRawTarget
            supported.right_root_pos))
  · unfold positiveExpandedFourCellTargetSaturatedReceiverDensity
    exact Q'.divPos_mul_eqv _ physicalWeight hphysicalWeightPos

structure PositiveExpandedFourCellTargetSaturatedReceiverLift
    (S : SlabScalePair) (root target : Nat) : Type where
  supported : PositiveExpandedFourCellTargetSupportedPath S root target
  receiver : SlabObservableTwoReplicaPair S.coarse root
  receiver_mem : receiver ∈
    positiveExpandedFourCellTargetReceiverAssignmentBlock supported

def positiveExpandedFourCellTargetSaturatedReceiverLiftOf
    {S : SlabScalePair} {root target : Nat}
    (supported : PositiveExpandedFourCellTargetSupportedPath S root target)
    (receiver : {candidate // candidate ∈
      positiveExpandedFourCellTargetReceiverAssignmentBlock supported}) :
    PositiveExpandedFourCellTargetSaturatedReceiverLift S root target :=
  { supported := supported
    receiver := receiver.1
    receiver_mem := receiver.2 }

def positiveExpandedFourCellTargetSaturatedReceiverLifts
    (S : SlabScalePair) (root target : Nat) :
    List (PositiveExpandedFourCellTargetSaturatedReceiverLift
      S root target) :=
  (positiveExpandedFourCellTargetSupportedPaths S root target).flatMap
    fun supported =>
      (positiveExpandedFourCellTargetReceiverAssignmentBlock
        supported).attach.map
          (positiveExpandedFourCellTargetSaturatedReceiverLiftOf supported)

def positiveExpandedFourCellTargetSaturatedLiftDensity
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    {root target : Nat}
    (lift : PositiveExpandedFourCellTargetSaturatedReceiverLift
      S root target) : Q' :=
  positiveExpandedFourCellTargetSaturatedReceiverDensity
    S hfineCutoff hcoarseCoupling lift.supported

theorem positiveExpandedFourCellTargetSaturatedReceiverLifts_mass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    listQSum
        (fun lift =>
          positiveExpandedFourCellTargetSaturatedLiftDensity
              S hfineCutoff hcoarseCoupling lift *
            slabObservableTwoReplicaPairWeight
              S.coarse lift.receiver)
        (positiveExpandedFourCellTargetSaturatedReceiverLifts
          S root target) ≈
      listQSum
        (positiveExpandedFourCellTargetSupportedPathRawMass
          S hfineCutoff hcoarseCoupling)
        (positiveExpandedFourCellTargetSupportedPaths S root target) := by
  unfold positiveExpandedFourCellTargetSaturatedReceiverLifts
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap
      (fun lift =>
        positiveExpandedFourCellTargetSaturatedLiftDensity
            S hfineCutoff hcoarseCoupling lift *
          slabObservableTwoReplicaPairWeight S.coarse lift.receiver)
      (fun supported =>
        (positiveExpandedFourCellTargetReceiverAssignmentBlock
          supported).attach.map
            (positiveExpandedFourCellTargetSaturatedReceiverLiftOf
              supported))
      (positiveExpandedFourCellTargetSupportedPaths S root target)) ?_
  apply listQSum_congr
  intro supported
  rw [listQSum_map]
  simpa only [positiveExpandedFourCellTargetSaturatedReceiverLiftOf,
      positiveExpandedFourCellTargetSaturatedLiftDensity] using
    (Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq
        (listQSum_attach
          (fun receiver =>
            positiveExpandedFourCellTargetSaturatedReceiverDensity
                S hfineCutoff hcoarseCoupling supported *
              slabObservableTwoReplicaPairWeight S.coarse receiver)
          (positiveExpandedFourCellTargetReceiverAssignmentBlock
            supported)))
      (positiveExpandedFourCellTargetSaturatedAssignmentBlock_mass
        S hfineCutoff hcoarseCoupling supported))

def positiveExpandedFourCellTargetSaturatedReceiverFiberDensity
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root) : Q' :=
  finiteCoefficientZeroExtension
    (positiveExpandedFourCellTargetSaturatedReceiverLifts
      S root target)
    (positiveExpandedFourCellTargetSaturatedLiftDensity
      S hfineCutoff hcoarseCoupling)
    PositiveExpandedFourCellTargetSaturatedReceiverLift.receiver
    receiver

theorem positiveExpandedFourCellTargetSaturatedReceiverFiberMass_eqv
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    listQSum
        (fun receiver =>
          positiveExpandedFourCellTargetSaturatedReceiverFiberDensity
              S hfineCutoff hcoarseCoupling root target receiver *
            slabObservableTwoReplicaPairWeight S.coarse receiver)
        (slabObservableFourCellTargetPairs S.coarse root target) ≈
      listQSum
        (positiveExpandedFourCellTargetSupportedPathRawMass
          S hfineCutoff hcoarseCoupling)
        (positiveExpandedFourCellTargetSupportedPaths S root target) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun lift =>
        positiveExpandedFourCellTargetSaturatedLiftDensity
            S hfineCutoff hcoarseCoupling lift *
          slabObservableTwoReplicaPairWeight S.coarse lift.receiver)
      (positiveExpandedFourCellTargetSaturatedReceiverLifts
        S root target)) _ ?_ ?_
  · exact finiteCoefficientZeroExtension_reindex_mul
      (positiveExpandedFourCellTargetSaturatedReceiverLifts
        S root target)
      (positiveExpandedFourCellTargetSaturatedLiftDensity
        S hfineCutoff hcoarseCoupling)
      PositiveExpandedFourCellTargetSaturatedReceiverLift.receiver
      (slabObservableFourCellTargetPairs S.coarse root target)
      (slabObservableFourCellTargetPairs_nodup
        S.coarse root target)
      (fun lift _ =>
        positiveExpandedFourCellTargetReceiverAssignmentBlock_mem
          lift.supported lift.receiver lift.receiver_mem)
      (slabObservableTwoReplicaPairWeight S.coarse)
  · exact positiveExpandedFourCellTargetSaturatedReceiverLifts_mass
      S hfineCutoff hcoarseCoupling root target

/-! ## 5. Exact saturated receiver cross and connected defect -/

def actualPositiveExpandedSaturatedReceiverFiberWeightedFaceRawFourCellPathCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  listQSum
      (fun receiver =>
        positiveExpandedFourCellSourceSaturatedReceiverFiberDensity
            S hfineCutoff hcoarseCoupling root target receiver *
          slabObservableTwoReplicaPairWeight S.coarse receiver)
      (slabObservableFourCellSourcePairs S.coarse root target) -
    listQSum
      (fun receiver =>
        positiveExpandedFourCellTargetSaturatedReceiverFiberDensity
            S hfineCutoff hcoarseCoupling root target receiver *
          slabObservableTwoReplicaPairWeight S.coarse receiver)
      (slabObservableFourCellTargetPairs S.coarse root target)

theorem actualPositiveExpandedSupportedFaceRawFourCellPathCross_eqv_assignmentSaturated
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    actualPositiveExpandedSupportedFaceRawFourCellPathCross
        S hfineCutoff hcoarseCoupling root target ≈
      actualPositiveExpandedSaturatedReceiverFiberWeightedFaceRawFourCellPathCross
        S hfineCutoff hcoarseCoupling root target := by
  unfold actualPositiveExpandedSupportedFaceRawFourCellPathCross
    actualPositiveExpandedSaturatedReceiverFiberWeightedFaceRawFourCellPathCross
  exact sub_eqv_both_local
    (Q'.eqv_symm
      (positiveExpandedFourCellSourceSaturatedReceiverFiberMass_eqv
        S hfineCutoff hcoarseCoupling root target))
    (Q'.eqv_symm
      (positiveExpandedFourCellTargetSaturatedReceiverFiberMass_eqv
        S hfineCutoff hcoarseCoupling root target))

def physicalConnectedCovariancePositiveExpandedAssignmentSaturatedRawCrossDefect
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  (physicalFaceRawFourCellCross
      S.coarse M.coarseRoot M.coarseTarget *
      S.coarse.physicalPartition) *
      rawCovarianceDenominator S.fine.physicalPartition -
    (actualPositiveExpandedSaturatedReceiverFiberWeightedFaceRawFourCellPathCross
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget *
      S.fine.physicalPartition) *
      rawCovarianceDenominator S.coarse.physicalPartition

theorem physicalConnectedCovariancePositiveExpandedSupportedPathRawCrossDefect_eqv_assignmentSaturated
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    physicalConnectedCovariancePositiveExpandedSupportedPathRawCrossDefect
        S hfineCutoff hcoarseCoupling M ≈
      physicalConnectedCovariancePositiveExpandedAssignmentSaturatedRawCrossDefect
        S hfineCutoff hcoarseCoupling M := by
  unfold physicalConnectedCovariancePositiveExpandedSupportedPathRawCrossDefect
    physicalConnectedCovariancePositiveExpandedAssignmentSaturatedRawCrossDefect
  exact sub_eqv_both_local (Q'.eqv_refl _)
    (Q'.mul_eqv_congr_right _ _
      (rawCovarianceDenominator S.coarse.physicalPartition)
      (Q'.mul_eqv_congr_right _ _ S.fine.physicalPartition
        (actualPositiveExpandedSupportedFaceRawFourCellPathCross_eqv_assignmentSaturated
          S hfineCutoff hcoarseCoupling
          M.coarseRoot M.coarseTarget)))

theorem physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedAssignmentSaturated
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    physicalConnectedCovarianceRawCrossDefect
        S hfineCutoff hcoarseCoupling M ≈
      physicalConnectedCovariancePositiveExpandedAssignmentSaturatedRawCrossDefect
        S hfineCutoff hcoarseCoupling M :=
  Q'.eqv_trans _ _ _
    (physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedSupported
      S hfineCutoff hcoarseCoupling M)
    (physicalConnectedCovariancePositiveExpandedSupportedPathRawCrossDefect_eqv_assignmentSaturated
      S hfineCutoff hcoarseCoupling M)

theorem centeredCylinderRemainder_physicalKernel_abs_le_of_positiveExpandedAssignmentSaturatedRawCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (budget : Q')
    (hcross :
      Q'.abs
          (physicalConnectedCovariancePositiveExpandedAssignmentSaturatedRawCrossDefect
            S hfineCutoff hcoarseCoupling M) ≤
        budget * connectedCovarianceRawCrossDenominator S) :
    Q'.abs
        (centeredCylinderRemainder
          (physicalKernel S hfineCutoff hcoarseCoupling) M) ≤
      budget := by
  apply centeredCylinderRemainder_physicalKernel_abs_le_of_positiveExpandedSupportedPathRawCross
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (physicalConnectedCovariancePositiveExpandedSupportedPathRawCrossDefect_eqv_assignmentSaturated
          S hfineCutoff hcoarseCoupling M)))
    hcross

#print axioms positiveWholeSlabRawTargetExpandedEntryAt
#print axioms positiveWholeSlabRawTargetExpandedEntries
#print axioms positiveWholeSlabRawTargetExpandedEntries_weight_total
#print axioms positiveWholeSlabRawTarget_physicalTerm_pos
#print axioms positiveWholeSlabRawTargetPositiveEntries
#print axioms positiveWholeSlabRawTargetPositiveEntries_weight_total
#print axioms positiveWholeSlabRawTargetReceiverPairBlock
#print axioms positiveWholeSlabRawTargetReceiverPairBlock_weight_total
#print axioms positiveWholeSlabRawTargetReceiverPairPhysicalWeight_pos
#print axioms positiveExpandedFourCellSourceReceiverAssignmentBlock_mem
#print axioms positiveExpandedFourCellSourceSaturatedAssignmentBlock_mass
#print axioms positiveExpandedFourCellSourceSaturatedReceiverLifts_mass
#print axioms positiveExpandedFourCellSourceSaturatedReceiverFiberMass_eqv
#print axioms positiveExpandedFourCellTargetReceiverAssignmentBlock_mem
#print axioms positiveExpandedFourCellTargetSaturatedAssignmentBlock_mass
#print axioms positiveExpandedFourCellTargetSaturatedReceiverLifts_mass
#print axioms positiveExpandedFourCellTargetSaturatedReceiverFiberMass_eqv
#print axioms actualPositiveExpandedSupportedFaceRawFourCellPathCross_eqv_assignmentSaturated
#print axioms physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedAssignmentSaturated
#print axioms centeredCylinderRemainder_physicalKernel_abs_le_of_positiveExpandedAssignmentSaturatedRawCross

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturation
