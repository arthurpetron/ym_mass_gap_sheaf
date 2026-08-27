/-
# Physical realization of paired-support recoupling choices

The source-dependent row above a disconnected paired-support source has a
complete target assignment for the common matrix over its switched physical
fields.  This module realizes that assignment as two accepted whole-slab
auxiliary assignments and packages them with the switched physical fields as
one literal target four-cell pair.

Constructive contract: structural dependent products and exact Boolean face
swaps only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRow
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetProduct

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRow
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabObservablePairedSupportRecouplingProduct
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetProduct
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. The switched physical pair remains in the bounded carrier -/

private theorem faceSwapLeft_mem_bounded
    {K : Nat} (edges : List Nat) (mask : Nat → Bool)
    {left right : SlabLabelling}
    (hleft : left ∈ boundedEdgeLabellings K edges)
    (hright : right ∈ boundedEdgeLabellings K edges) :
    twoReplicaFaceSwapLeft mask left right ∈
      boundedEdgeLabellings K edges := by
  have hleftSound := boundedEdgeLabellings_sound K edges left hleft
  have hrightSound := boundedEdgeLabellings_sound K edges right hright
  apply boundedEdgeLabellings_complete
  · intro faceId hface
    cases hmask : mask faceId with
    | false =>
        simpa [twoReplicaFaceSwapLeft, hmask] using
          hleftSound.1 faceId hface
    | true =>
        simpa [twoReplicaFaceSwapLeft, hmask] using
          hrightSound.1 faceId hface
  · intro faceId hface
    cases hmask : mask faceId with
    | false =>
        simpa [twoReplicaFaceSwapLeft, hmask] using
          hleftSound.2 faceId hface
    | true =>
        simpa [twoReplicaFaceSwapLeft, hmask] using
          hrightSound.2 faceId hface

private theorem faceSwapRight_mem_bounded
    {K : Nat} (edges : List Nat) (mask : Nat → Bool)
    {left right : SlabLabelling}
    (hleft : left ∈ boundedEdgeLabellings K edges)
    (hright : right ∈ boundedEdgeLabellings K edges) :
    twoReplicaFaceSwapRight mask left right ∈
      boundedEdgeLabellings K edges := by
  have hleftSound := boundedEdgeLabellings_sound K edges left hleft
  have hrightSound := boundedEdgeLabellings_sound K edges right hright
  apply boundedEdgeLabellings_complete
  · intro faceId hface
    cases hmask : mask faceId with
    | false =>
        simpa [twoReplicaFaceSwapRight, hmask] using
          hrightSound.1 faceId hface
    | true =>
        simpa [twoReplicaFaceSwapRight, hmask] using
          hleftSound.1 faceId hface
  · intro faceId hface
    cases hmask : mask faceId with
    | false =>
        simpa [twoReplicaFaceSwapRight, hmask] using
          hrightSound.2 faceId hface
    | true =>
        simpa [twoReplicaFaceSwapRight, hmask] using
          hleftSound.2 faceId hface

theorem slabObservablePairedSupportSwitchedLeftPhysical_mem
    (D : SlabPhysicalData) {rootFaceId targetFaceId : Nat}
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId) :
    slabObservablePairSupportSwitchedLeftPhysical
        D targetFaceId source.1 ∈ D.physicalLabellings := by
  exact faceSwapLeft_mem_bounded D.faceEdges
    (slabObservableTwoReplicaPairPairedSupportSwapMask
      D source.1 targetFaceId)
    source.1.1.physical_mem
    (mem_slabExpandedFineSources_iff.mp source.1.2.2).1

theorem slabObservablePairedSupportSwitchedRightPhysical_mem
    (D : SlabPhysicalData) {rootFaceId targetFaceId : Nat}
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId) :
    slabObservablePairSupportSwitchedRightPhysical
        D targetFaceId source.1 ∈ D.physicalLabellings := by
  exact faceSwapRight_mem_bounded D.faceEdges
    (slabObservableTwoReplicaPairPairedSupportSwapMask
      D source.1 targetFaceId)
    source.1.1.physical_mem
    (mem_slabExpandedFineSources_iff.mp source.1.2.2).1

theorem slabObservablePairedSupportSwitchedLeftPhysical_bounded
    (D : SlabPhysicalData) {rootFaceId targetFaceId : Nat}
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId) :
    SlabFaceLabellingBounded D.cutoff D.extent
      (slabObservablePairSupportSwitchedLeftPhysical
        D targetFaceId source.1) := by
  intro faceId hface
  exact Nat.le_of_lt_succ
    ((boundedEdgeLabellings_sound D.cutoff D.faceEdges _
      (slabObservablePairedSupportSwitchedLeftPhysical_mem
        D source)).1 faceId hface)

theorem slabObservablePairedSupportSwitchedRightPhysical_bounded
    (D : SlabPhysicalData) {rootFaceId targetFaceId : Nat}
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId) :
    SlabFaceLabellingBounded D.cutoff D.extent
      (slabObservablePairSupportSwitchedRightPhysical
        D targetFaceId source.1) := by
  intro faceId hface
  exact Nat.le_of_lt_succ
    ((boundedEdgeLabellings_sound D.cutoff D.faceEdges _
      (slabObservablePairedSupportSwitchedRightPhysical_mem
        D source)).1 faceId hface)

/-! ## 2. Every abstract target column becomes two accepted assignments -/

def slabObservablePairedSupportRecoupledAssignmentsResult
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId source) :=
  slabPhysicalPairTargetAssignmentsResult D.cutoff D.extent
    (slabObservablePairSupportSwitchedLeftPhysical
      D targetFaceId source.1)
    (slabObservablePairSupportSwitchedRightPhysical
      D targetFaceId source.1)
    (SlabObservablePairedSupportSeparatedSource.toContributor
      source).leftAssignment
    (SlabObservablePairedSupportSeparatedSource.toContributor
      source).rightAssignment
    ((SlabObservablePairedSupportSeparatedSource.toContributor
      source).leftAssignment_mem htarget)
    ((SlabObservablePairedSupportSeparatedSource.toContributor
      source).rightAssignment_mem htarget)
    (slabObservablePairedSupportSwitchedLeftPhysical_bounded D source)
    (slabObservablePairedSupportSwitchedRightPhysical_bounded D source)
    choice

theorem slabObservablePairedSupportRecoupledLeftAssignment_mem
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId source) :
    (slabObservablePairedSupportRecoupledAssignmentsResult
      D rootFaceId targetFaceId htarget source choice).leftAssignment ∈
      slabFineFusionWitnesses D
        (slabObservablePairSupportSwitchedLeftPhysical
          D targetFaceId source.1) :=
  slabPhysicalPairTargetLeftAssignment_mem D.cutoff D.extent
    (slabObservablePairSupportSwitchedLeftPhysical
      D targetFaceId source.1)
    (slabObservablePairSupportSwitchedRightPhysical
      D targetFaceId source.1)
    (SlabObservablePairedSupportSeparatedSource.toContributor
      source).leftAssignment
    (SlabObservablePairedSupportSeparatedSource.toContributor
      source).rightAssignment
    ((SlabObservablePairedSupportSeparatedSource.toContributor
      source).leftAssignment_mem htarget)
    ((SlabObservablePairedSupportSeparatedSource.toContributor
      source).rightAssignment_mem htarget)
    (slabObservablePairedSupportSwitchedLeftPhysical_bounded D source)
    (slabObservablePairedSupportSwitchedRightPhysical_bounded D source)
    choice

theorem slabObservablePairedSupportRecoupledRightAssignment_mem
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId source) :
    (slabObservablePairedSupportRecoupledAssignmentsResult
      D rootFaceId targetFaceId htarget source choice).rightAssignment ∈
      slabFineFusionWitnesses D
        (slabObservablePairSupportSwitchedRightPhysical
          D targetFaceId source.1) :=
  slabPhysicalPairTargetRightAssignment_mem D.cutoff D.extent
    (slabObservablePairSupportSwitchedLeftPhysical
      D targetFaceId source.1)
    (slabObservablePairSupportSwitchedRightPhysical
      D targetFaceId source.1)
    (SlabObservablePairedSupportSeparatedSource.toContributor
      source).leftAssignment
    (SlabObservablePairedSupportSeparatedSource.toContributor
      source).rightAssignment
    ((SlabObservablePairedSupportSeparatedSource.toContributor
      source).leftAssignment_mem htarget)
    ((SlabObservablePairedSupportSeparatedSource.toContributor
      source).rightAssignment_mem htarget)
    (slabObservablePairedSupportSwitchedLeftPhysical_bounded D source)
    (slabObservablePairedSupportSwitchedRightPhysical_bounded D source)
    choice

end YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization.slabObservablePairedSupportSwitchedLeftPhysical_mem
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization.slabObservablePairedSupportSwitchedRightPhysical_mem
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization.slabObservablePairedSupportSwitchedLeftPhysical_bounded
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization.slabObservablePairedSupportSwitchedRightPhysical_bounded
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization.slabObservablePairedSupportRecoupledAssignmentsResult
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization.slabObservablePairedSupportRecoupledLeftAssignment_mem
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization.slabObservablePairedSupportRecoupledRightAssignment_mem
