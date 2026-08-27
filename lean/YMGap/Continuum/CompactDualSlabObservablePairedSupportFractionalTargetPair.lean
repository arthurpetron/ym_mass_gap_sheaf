/-
# Four-cell targets realized from paired-support recoupling columns

The support-switched physical fields and the accepted assignments constructed
from one abstract recoupling column form two literal expanded source entries.
The support mask fixes the root side and crosses the target side, so their
pair lies in the exact four-cell target carrier.

Constructive contract: finite carrier membership and Boolean face swaps only;
no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization
import YMGap.Continuum.SU2SlabGlobalRecouplingWitnessRealization

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalTargetPair

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRow
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabObservablePairedSupportRecouplingProduct
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2SlabGlobalRecouplingWitnessRealization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Two accepted target entries -/

theorem slabObservablePairedSupportSwitchedLeftPhysical_root_positive
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId) :
    0 < slabObservablePairSupportSwitchedLeftPhysical
      D targetFaceId source.1 rootFaceId := by
  unfold slabObservablePairSupportSwitchedLeftPhysical
    twoReplicaFaceSwapLeft
  rw [slabObservableTwoReplicaPairPairedSupportSwapMask_root_of_disconnected
    D rootFaceId targetFaceId source.1 source.disconnected]
  exact source.1.1.source_positive

def slabObservablePairedSupportRecoupledLeftEntry
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId source) :
    SlabObservablePositiveSourceEntry D rootFaceId :=
  slabObservablePositiveSourceEntryOfCarrier D rootFaceId
    (slabObservablePairSupportSwitchedLeftPhysical
      D targetFaceId source.1)
    (slabObservablePairedSupportSwitchedLeftPhysical_mem D source)
    (slabObservablePairedSupportRecoupledAssignmentsResult
      D rootFaceId targetFaceId htarget source choice).leftAssignment
    (slabObservablePairedSupportRecoupledLeftAssignment_mem
      D rootFaceId targetFaceId htarget source choice)
    (slabObservablePairedSupportSwitchedLeftPhysical_root_positive
      D rootFaceId targetFaceId source)

def slabObservablePairedSupportRecoupledRightEntry
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId source) :
    SlabExpandedFineSourceEntry D :=
  slabExpandedFineSourceEntryOfCarrier D
    (slabObservablePairSupportSwitchedRightPhysical
      D targetFaceId source.1)
    (slabObservablePairedSupportSwitchedRightPhysical_mem D source)
    (slabObservablePairedSupportRecoupledAssignmentsResult
      D rootFaceId targetFaceId htarget source choice).rightAssignment
    (slabObservablePairedSupportRecoupledRightAssignment_mem
      D rootFaceId targetFaceId htarget source choice)

def slabObservablePairedSupportRecoupledTargetPair
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId source) :
    SlabObservableTwoReplicaPair D rootFaceId :=
  (slabObservablePairedSupportRecoupledLeftEntry
      D rootFaceId targetFaceId htarget source choice,
    slabObservablePairedSupportRecoupledRightEntry
      D rootFaceId targetFaceId htarget source choice)

theorem slabObservablePairedSupportRecoupledLeftEntry_physical
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId source) :
    (slabObservablePairedSupportRecoupledLeftEntry
      D rootFaceId targetFaceId htarget source choice).1.1 =
        slabObservablePairSupportSwitchedLeftPhysical
          D targetFaceId source.1 := by
  unfold slabObservablePairedSupportRecoupledLeftEntry
  apply slabObservablePositiveSourceEntryOfCarrier_physical

theorem slabObservablePairedSupportRecoupledRightEntry_physical
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId source) :
    (slabObservablePairedSupportRecoupledRightEntry
      D rootFaceId targetFaceId htarget source choice).1.1 =
        slabObservablePairSupportSwitchedRightPhysical
          D targetFaceId source.1 := by
  unfold slabObservablePairedSupportRecoupledRightEntry
  apply slabExpandedFineSourceEntryOfCarrier_physical

/-! ## 2. A reusable four-cell face-swap lemma -/

/-- Any Boolean face transposition that leaves the root on the left and
crosses the target face sends a source four-cell pair into the target
four-cell carrier. -/
theorem faceSwapEntries_mem_fourCellTarget_of_mask
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservableTwoReplicaPair D rootFaceId)
    (hsource : source ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (mask : Nat → Bool)
    (left : SlabObservablePositiveSourceEntry D rootFaceId)
    (right : SlabExpandedFineSourceEntry D)
    (hleft : left.1.1 =
      twoReplicaFaceSwapLeft mask source.1.1.1 source.2.1.1)
    (hright : right.1.1 =
      twoReplicaFaceSwapRight mask source.1.1.1 source.2.1.1)
    (hroot : mask rootFaceId = false)
    (htarget : mask targetFaceId = true) :
    (left, right) ∈
      slabObservableFourCellTargetPairs D rootFaceId targetFaceId := by
  have hcells := (mem_cartesian_iff
    (slabObservableRootTargetEntries D rootFaceId targetFaceId)
    (slabObservableRootComplementTargetComplementEntries
      D rootFaceId targetFaceId) source).mp hsource
  have hfirst := List.mem_filter.mp hcells.1
  have hsecond := List.mem_filter.mp hcells.2
  have hsecondParts := (Bool.and_eq_true _ _).mp hsecond.2
  apply (mem_cartesian_iff
    (slabObservableRootTargetComplementEntries
      D rootFaceId targetFaceId)
    (slabObservableRootComplementTargetEntries
      D rootFaceId targetFaceId)
    (left, right)).mpr
  constructor
  · apply List.mem_filter.mpr
    constructor
    · exact List.mem_attach _ left
    · unfold SlabObservablePositiveSourceEntry.facePositiveB
      rw [hleft]
      simp only [twoReplicaFaceSwapLeft, htarget, if_true]
      exact hsecondParts.2
  · apply List.mem_filter.mpr
    constructor
    · exact List.mem_attach _ right
    · apply (Bool.and_eq_true _ _).mpr
      constructor
      · unfold SlabExpandedFineSourceEntry.facePositiveB
        rw [hright]
        simp only [twoReplicaFaceSwapRight, hroot]
        exact hsecondParts.1
      · unfold SlabExpandedFineSourceEntry.facePositiveB
        rw [hright]
        simp only [twoReplicaFaceSwapRight, htarget, if_true]
        exact hfirst.2

/-! ## 3. The support-aligned physical realization -/

/-- Every source-dependent abstract target column is realized by an actual
accepted member of the common target four-cell. -/
theorem slabObservablePairedSupportRecoupledTargetPair_mem
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId source) :
    slabObservablePairedSupportRecoupledTargetPair
        D rootFaceId targetFaceId htarget source choice ∈
      slabObservableFourCellTargetPairs
        D rootFaceId targetFaceId := by
  unfold slabObservablePairedSupportRecoupledTargetPair
  apply faceSwapEntries_mem_fourCellTarget_of_mask
    D rootFaceId targetFaceId source.1 source.pair_mem_fourCell
    (slabObservableTwoReplicaPairPairedSupportSwapMask
      D source.1 targetFaceId)
  · exact slabObservablePairedSupportRecoupledLeftEntry_physical
      D rootFaceId targetFaceId htarget source choice
  · exact slabObservablePairedSupportRecoupledRightEntry_physical
      D rootFaceId targetFaceId htarget source choice
  · exact slabObservableTwoReplicaPairPairedSupportSwapMask_root_of_disconnected
      D rootFaceId targetFaceId source.1 source.disconnected
  · exact slabObservableTwoReplicaPairPairedSupportSwapMask_target
      D rootFaceId targetFaceId htarget source.1 source.pair_mem_fourCell

end YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalTargetPair

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalTargetPair.slabObservablePairedSupportSwitchedLeftPhysical_root_positive
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalTargetPair.slabObservablePairedSupportRecoupledTargetPair
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalTargetPair.faceSwapEntries_mem_fourCellTarget_of_mask
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalTargetPair.slabObservablePairedSupportRecoupledTargetPair_mem
