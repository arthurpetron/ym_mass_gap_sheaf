/-
# Assignment-saturated receiver coverage is physical endpoint coverage

The first receiver image retained one constructively selected intertwiner
assignment above each raw-supported physical endpoint.  The assignment-
saturated lift instead contains every accepted assignment above that
endpoint.  This module identifies membership in the enlarged image exactly:
for a receiver already in the source or target cell, membership depends only
on whether its pair of physical coarse labellings occurs as the endpoint of a
positive raw-supported path.

It then partitions the full receiver cells into assignment-saturated covered
mass and genuinely unreachable physical-endpoint mass.  Thus the remaining
coverage estimate no longer asks an analytic argument to recover arbitrary
auxiliary intertwiner assignments.

No quantitative endpoint-surjectivity estimate, `O(g^2)` bound, continuum
measure, OS/GNS reconstruction, or Yang--Mills mass gap is proved here.

Constructive contract: finite list membership, subtype extensionality, and
exact rational sums only; no choice, `Classical`, `native_decide`, `sorry`,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturation
import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectAggregateCoverageDeficit

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedPhysicalCoverage

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.BF4SU2OuterJointCarrierRawRowMass
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectAggregateCoverageDeficit
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectAggregateNormalizedVariation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverOrientation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedSupportedPaths
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

local instance assignmentSaturatedCoverageReceiverDecidableEq
    (S : SlabScalePair) (root : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair S.coarse root) :=
  slabObservableTwoReplicaPairDecidableEq S.coarse root

private theorem le_of_add_le_add_left_local {common left right : Q'}
    (h : common + left ≤ common + right) : left ≤ right := by
  have hadd := Q'.add_le_add_left (-common)
    (common + left) (common + right) h
  have hleft : -common + (common + left) ≈ left := by
    refine Q'.eqv_trans _ ((-common + common) + left) _
      (Q'.eqv_symm (Q'.add_assoc_eqv (-common) common left)) ?_
    refine Q'.eqv_trans _ ((0 : Q') + left) _
      (Q'.add_eqv_congr_right _ _ left
        (Q'.neg_add_self_eqv common)) ?_
    exact QPoly.q_zero_add_eqv left
  have hright : -common + (common + right) ≈ right := by
    refine Q'.eqv_trans _ ((-common + common) + right) _
      (Q'.eqv_symm (Q'.add_assoc_eqv (-common) common right)) ?_
    refine Q'.eqv_trans _ ((0 : Q') + right) _
      (Q'.add_eqv_congr_right _ _ right
        (Q'.neg_add_self_eqv common)) ?_
    exact QPoly.q_zero_add_eqv right
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hright))

/-! ## 1. Complete accepted fibers are characterized by physical data -/

theorem mem_positiveWholeSlabRawTargetExpandedEntries_iff_physical
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (rawTarget : PositiveWholeSlabRawTarget S fineState)
    (entry : SlabExpandedFineSourceEntry S.coarse) :
    entry ∈ positiveWholeSlabRawTargetExpandedEntries rawTarget ↔
      entry.1.1 = rawTarget.coarseTarget := by
  constructor
  · exact positiveWholeSlabRawTargetExpandedEntries_physical
      rawTarget entry
  · intro hphysical
    have hassignment : entry.1.2 ∈
        slabFineFusionWitnesses S.coarse rawTarget.coarseTarget := by
      have hentry := (mem_slabExpandedFineSources_iff.mp entry.2).2
      simpa only [hphysical] using hentry
    let assignment : {candidate // candidate ∈
        slabFineFusionWitnesses S.coarse rawTarget.coarseTarget} :=
      ⟨entry.1.2, hassignment⟩
    apply List.mem_map.mpr
    refine ⟨assignment, List.mem_attach _ _, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact hphysical.symm
    · rfl

theorem mem_positiveWholeSlabRawTargetPositiveEntries_iff_physical
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (root : Nat) (rawTarget : PositiveWholeSlabRawTarget S fineState)
    (hroot : 0 < rawTarget.coarseTarget root)
    (entry : SlabObservablePositiveSourceEntry S.coarse root) :
    entry ∈ positiveWholeSlabRawTargetPositiveEntries
        root rawTarget hroot ↔
      entry.1.1 = rawTarget.coarseTarget := by
  constructor
  · exact positiveWholeSlabRawTargetPositiveEntries_physical
      root rawTarget hroot entry
  · intro hphysical
    let expanded : SlabExpandedFineSourceEntry S.coarse :=
      ⟨entry.1, entry.source_mem_expanded⟩
    have hexpanded : expanded ∈
        positiveWholeSlabRawTargetExpandedEntries rawTarget :=
      (mem_positiveWholeSlabRawTargetExpandedEntries_iff_physical
        rawTarget expanded).mpr hphysical
    apply List.mem_map.mpr
    refine ⟨⟨expanded, hexpanded⟩, List.mem_attach _ _, ?_⟩
    apply Subtype.ext
    rfl

/-- Inside the established receiver type, the complete assignment block is
determined exactly by the two physical coarse endpoints. -/
theorem mem_positiveWholeSlabRawTargetReceiverPairBlock_iff_physical
    {S : SlabScalePair}
    {leftFineState rightFineState : EdgeLabelling}
    (root : Nat)
    (left : PositiveWholeSlabRawTarget S leftFineState)
    (right : PositiveWholeSlabRawTarget S rightFineState)
    (hleftRoot : 0 < left.coarseTarget root)
    (receiver : SlabObservableTwoReplicaPair S.coarse root) :
    receiver ∈ positiveWholeSlabRawTargetReceiverPairBlock
        root left right hleftRoot ↔
      receiver.1.1.1 = left.coarseTarget ∧
        receiver.2.1.1 = right.coarseTarget := by
  unfold positiveWholeSlabRawTargetReceiverPairBlock
  rw [mem_cartesian_iff]
  exact and_congr
    (mem_positiveWholeSlabRawTargetPositiveEntries_iff_physical
      root left hleftRoot receiver.1)
    (mem_positiveWholeSlabRawTargetExpandedEntries_iff_physical
      right receiver.2)

/-! ## 2. The saturated images forget auxiliary assignments -/

def positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage
    (S : SlabScalePair) (root target : Nat) :
    List (SlabObservableTwoReplicaPair S.coarse root) :=
  (positiveExpandedFourCellSourceSupportedPaths S root target).flatMap
    positiveExpandedFourCellSourceReceiverAssignmentBlock

def positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage
    (S : SlabScalePair) (root target : Nat) :
    List (SlabObservableTwoReplicaPair S.coarse root) :=
  (positiveExpandedFourCellTargetSupportedPaths S root target).flatMap
    positiveExpandedFourCellTargetReceiverAssignmentBlock

theorem mem_positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage_iff_physical
    (S : SlabScalePair) (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root) :
    receiver ∈
        positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage
          S root target ↔
      ∃ supported : PositiveExpandedFourCellSourceSupportedPath
          S root target,
        supported ∈
            positiveExpandedFourCellSourceSupportedPaths S root target ∧
          receiver.1.1.1 = supported.leftRawTarget.coarseTarget ∧
          receiver.2.1.1 = supported.rightRawTarget.coarseTarget := by
  unfold positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage
  constructor
  · intro hreceiver
    obtain ⟨supported, hsupported, hblock⟩ :=
      List.mem_flatMap.mp hreceiver
    exact ⟨supported, hsupported,
      (mem_positiveWholeSlabRawTargetReceiverPairBlock_iff_physical
        root supported.leftRawTarget supported.rightRawTarget
          supported.left_root_pos receiver).mp hblock⟩
  · rintro ⟨supported, hsupported, hphysical⟩
    apply List.mem_flatMap.mpr
    exact ⟨supported, hsupported,
      (mem_positiveWholeSlabRawTargetReceiverPairBlock_iff_physical
        root supported.leftRawTarget supported.rightRawTarget
          supported.left_root_pos receiver).mpr hphysical⟩

theorem mem_positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage_iff_physical
    (S : SlabScalePair) (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root) :
    receiver ∈
        positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage
          S root target ↔
      ∃ supported : PositiveExpandedFourCellTargetSupportedPath
          S root target,
        supported ∈
            positiveExpandedFourCellTargetSupportedPaths S root target ∧
          receiver.1.1.1 = supported.rightRawTarget.coarseTarget ∧
          receiver.2.1.1 = supported.leftRawTarget.coarseTarget := by
  unfold positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage
  constructor
  · intro hreceiver
    obtain ⟨supported, hsupported, hblock⟩ :=
      List.mem_flatMap.mp hreceiver
    exact ⟨supported, hsupported,
      (mem_positiveWholeSlabRawTargetReceiverPairBlock_iff_physical
        root supported.rightRawTarget supported.leftRawTarget
          supported.right_root_pos receiver).mp hblock⟩
  · rintro ⟨supported, hsupported, hphysical⟩
    apply List.mem_flatMap.mpr
    exact ⟨supported, hsupported,
      (mem_positiveWholeSlabRawTargetReceiverPairBlock_iff_physical
        root supported.rightRawTarget supported.leftRawTarget
          supported.right_root_pos receiver).mpr hphysical⟩

theorem positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage_mem_cell
    (S : SlabScalePair) (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (hreceiver : receiver ∈
      positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage
        S root target) :
    receiver ∈ slabObservableFourCellSourcePairs
      S.coarse root target := by
  unfold positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage at hreceiver
  obtain ⟨supported, _, hblock⟩ := List.mem_flatMap.mp hreceiver
  exact positiveExpandedFourCellSourceReceiverAssignmentBlock_mem
    supported receiver hblock

theorem positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage_mem_cell
    (S : SlabScalePair) (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (hreceiver : receiver ∈
      positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage
        S root target) :
    receiver ∈ slabObservableFourCellTargetPairs
      S.coarse root target := by
  unfold positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage at hreceiver
  obtain ⟨supported, _, hblock⟩ := List.mem_flatMap.mp hreceiver
  exact positiveExpandedFourCellTargetReceiverAssignmentBlock_mem
    supported receiver hblock

/-- The former one-assignment source image embeds into the saturated image. -/
theorem positiveExpandedFourCellSourceSupportedReceiverImage_subset_assignmentSaturated
    (S : SlabScalePair) (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (hreceiver : receiver ∈
      positiveExpandedFourCellSourceSupportedReceiverImage S root target) :
    receiver ∈
      positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage
        S root target := by
  obtain ⟨supported, hsupported, heq⟩ := List.mem_map.mp hreceiver
  apply
    (mem_positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage_iff_physical
      S root target receiver).mpr
  refine ⟨supported, hsupported, ?_⟩
  rw [← heq]
  exact ⟨rfl, rfl⟩

/-- The former one-assignment target image embeds into the saturated image. -/
theorem positiveExpandedFourCellTargetSupportedReceiverImage_subset_assignmentSaturated
    (S : SlabScalePair) (root target : Nat)
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (hreceiver : receiver ∈
      positiveExpandedFourCellTargetSupportedReceiverImage S root target) :
    receiver ∈
      positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage
        S root target := by
  obtain ⟨supported, hsupported, heq⟩ := List.mem_map.mp hreceiver
  apply
    (mem_positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage_iff_physical
      S root target receiver).mpr
  refine ⟨supported, hsupported, ?_⟩
  rw [← heq]
  exact ⟨rfl, rfl⟩

/-! ## 3. Exact physical-endpoint coverage decomposition -/

def actualPositiveExpandedAssignmentSaturatedSourceCoveredReceiverMass
    (S : SlabScalePair) (root target : Nat) : Q' :=
  listQSum (slabObservableTwoReplicaPairWeight S.coarse)
    ((slabObservableFourCellSourcePairs S.coarse root target).filter
      (fun receiver => decide
        (receiver ∈
          positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage
            S root target)))

def actualPositiveExpandedAssignmentSaturatedSourceUnreachableReceiverMass
    (S : SlabScalePair) (root target : Nat) : Q' :=
  listQSum (slabObservableTwoReplicaPairWeight S.coarse)
    ((slabObservableFourCellSourcePairs S.coarse root target).filter
      (fun receiver => !(decide
        (receiver ∈
          positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage
            S root target))))

def actualPositiveExpandedAssignmentSaturatedTargetCoveredReceiverMass
    (S : SlabScalePair) (root target : Nat) : Q' :=
  listQSum (slabObservableTwoReplicaPairWeight S.coarse)
    ((slabObservableFourCellTargetPairs S.coarse root target).filter
      (fun receiver => decide
        (receiver ∈
          positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage
            S root target)))

def actualPositiveExpandedAssignmentSaturatedTargetUnreachableReceiverMass
    (S : SlabScalePair) (root target : Nat) : Q' :=
  listQSum (slabObservableTwoReplicaPairWeight S.coarse)
    ((slabObservableFourCellTargetPairs S.coarse root target).filter
      (fun receiver => !(decide
        (receiver ∈
          positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage
            S root target))))

def actualPositiveExpandedAssignmentSaturatedCoveredFullReceiverMass
    (S : SlabScalePair) (root target : Nat) : Q' :=
  actualPositiveExpandedAssignmentSaturatedSourceCoveredReceiverMass
      S root target +
    actualPositiveExpandedAssignmentSaturatedTargetCoveredReceiverMass
      S root target

def actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass
    (S : SlabScalePair) (root target : Nat) : Q' :=
  actualPositiveExpandedAssignmentSaturatedSourceUnreachableReceiverMass
      S root target +
    actualPositiveExpandedAssignmentSaturatedTargetUnreachableReceiverMass
      S root target

theorem actualPositiveExpandedAssignmentSaturatedSourceReceiverCellMass_eqv_covered_add_unreachable
    (S : SlabScalePair) (root target : Nat) :
    listQSum (slabObservableTwoReplicaPairWeight S.coarse)
        (slabObservableFourCellSourcePairs S.coarse root target) ≈
      actualPositiveExpandedAssignmentSaturatedSourceCoveredReceiverMass
          S root target +
        actualPositiveExpandedAssignmentSaturatedSourceUnreachableReceiverMass
          S root target := by
  simpa only [
    actualPositiveExpandedAssignmentSaturatedSourceCoveredReceiverMass,
    actualPositiveExpandedAssignmentSaturatedSourceUnreachableReceiverMass]
    using
      (listQSum_filter_partition
        (slabObservableTwoReplicaPairWeight S.coarse)
        (fun receiver : SlabObservableTwoReplicaPair S.coarse root =>
          decide
            (receiver ∈
              positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage
                S root target))
        (slabObservableFourCellSourcePairs S.coarse root target))

theorem actualPositiveExpandedAssignmentSaturatedTargetReceiverCellMass_eqv_covered_add_unreachable
    (S : SlabScalePair) (root target : Nat) :
    listQSum (slabObservableTwoReplicaPairWeight S.coarse)
        (slabObservableFourCellTargetPairs S.coarse root target) ≈
      actualPositiveExpandedAssignmentSaturatedTargetCoveredReceiverMass
          S root target +
        actualPositiveExpandedAssignmentSaturatedTargetUnreachableReceiverMass
          S root target := by
  simpa only [
    actualPositiveExpandedAssignmentSaturatedTargetCoveredReceiverMass,
    actualPositiveExpandedAssignmentSaturatedTargetUnreachableReceiverMass]
    using
      (listQSum_filter_partition
        (slabObservableTwoReplicaPairWeight S.coarse)
        (fun receiver : SlabObservableTwoReplicaPair S.coarse root =>
          decide
            (receiver ∈
              positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage
                S root target))
        (slabObservableFourCellTargetPairs S.coarse root target))

theorem actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass_eqv_assignmentSaturatedCovered_add_unreachable
    (S : SlabScalePair) (root target : Nat) :
    actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass
        S root target ≈
      actualPositiveExpandedAssignmentSaturatedCoveredFullReceiverMass
          S root target +
        actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass
          S root target := by
  let sourceCovered :=
    actualPositiveExpandedAssignmentSaturatedSourceCoveredReceiverMass
      S root target
  let targetCovered :=
    actualPositiveExpandedAssignmentSaturatedTargetCoveredReceiverMass
      S root target
  let sourceUnreachable :=
    actualPositiveExpandedAssignmentSaturatedSourceUnreachableReceiverMass
      S root target
  let targetUnreachable :=
    actualPositiveExpandedAssignmentSaturatedTargetUnreachableReceiverMass
      S root target
  have hsource :=
    actualPositiveExpandedAssignmentSaturatedSourceReceiverCellMass_eqv_covered_add_unreachable
      S root target
  have htarget :=
    actualPositiveExpandedAssignmentSaturatedTargetReceiverCellMass_eqv_covered_add_unreachable
      S root target
  refine Q'.eqv_trans _
    ((sourceCovered + sourceUnreachable) +
      (targetCovered + targetUnreachable)) _ ?_ ?_
  · simpa only [
      actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass,
      sourceCovered, targetCovered, sourceUnreachable, targetUnreachable] using
        Q'.add_eqv_congr' hsource htarget
  simpa only [
    actualPositiveExpandedAssignmentSaturatedCoveredFullReceiverMass,
    actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass,
    sourceCovered, targetCovered, sourceUnreachable, targetUnreachable] using
      (Q'.add_swap_inner sourceCovered sourceUnreachable
        targetCovered targetUnreachable)

/-- The remaining coverage hypothesis is exactly an additive bound on mass
whose physical endpoint pair is absent from every positive raw-supported
path. -/
theorem actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass_le_iff_fullReceiverCellMass_le_covered_add
    (S : SlabScalePair) (root target : Nat) (budget : Q') :
    actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass
          S root target ≤ budget ↔
      actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass
          S root target ≤
        actualPositiveExpandedAssignmentSaturatedCoveredFullReceiverMass
            S root target + budget := by
  let full :=
    actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass
      S root target
  let covered :=
    actualPositiveExpandedAssignmentSaturatedCoveredFullReceiverMass
      S root target
  let unreachable :=
    actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass
      S root target
  have hsplit : full ≈ covered + unreachable := by
    simpa only [full, covered, unreachable] using
      (actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass_eqv_assignmentSaturatedCovered_add_unreachable
        S root target)
  constructor
  · intro hunreachable
    have hadd := Q'.add_le_add_left covered unreachable budget hunreachable
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) hadd
  · intro hcoverage
    have hadd : covered + unreachable ≤ covered + budget :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv hsplit) hcoverage
    exact le_of_add_le_add_left_local hadd

#print axioms mem_positiveWholeSlabRawTargetExpandedEntries_iff_physical
#print axioms mem_positiveWholeSlabRawTargetPositiveEntries_iff_physical
#print axioms mem_positiveWholeSlabRawTargetReceiverPairBlock_iff_physical
#print axioms mem_positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage_iff_physical
#print axioms mem_positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage_iff_physical
#print axioms positiveExpandedFourCellSourceSupportedReceiverImage_subset_assignmentSaturated
#print axioms positiveExpandedFourCellTargetSupportedReceiverImage_subset_assignmentSaturated
#print axioms actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass_eqv_assignmentSaturatedCovered_add_unreachable
#print axioms actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass_le_iff_fullReceiverCellMass_le_covered_add

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedPhysicalCoverage
