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
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct

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
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct
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

def slabObservablePairedSupportCanonicalAnchor
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId) :
    SlabPhysicalPairCanonicalAnchor D.cutoff D.extent
      (slabObservablePairSupportSwitchedLeftPhysical
        D targetFaceId source.1)
      (slabObservablePairSupportSwitchedRightPhysical
        D targetFaceId source.1) where
  leftAssignment :=
    (SlabObservablePairedSupportSeparatedSource.toContributor
      source).leftAssignment
  rightAssignment :=
    (SlabObservablePairedSupportSeparatedSource.toContributor
      source).rightAssignment
  left_mem :=
    (SlabObservablePairedSupportSeparatedSource.toContributor
      source).leftAssignment_mem htarget
  right_mem :=
    (SlabObservablePairedSupportSeparatedSource.toContributor
      source).rightAssignment_mem htarget
  leftBounded := slabObservablePairedSupportSwitchedLeftPhysical_bounded
    D source
  rightBounded := slabObservablePairedSupportSwitchedRightPhysical_bounded
    D source

def slabObservablePairedSupportRecoupledAssignmentsResult
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId source) :=
  (slabObservablePairedSupportCanonicalAnchor
    D rootFaceId targetFaceId htarget source).realize choice

theorem slabObservablePairedSupportCanonicalAnchor_leftAssignment_eq_of_result_eq
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (first second : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (firstChoice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId first)
    (secondChoice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId second)
    (heq :
      (slabObservablePairedSupportRecoupledAssignmentsResult
        D rootFaceId targetFaceId htarget first firstChoice).leftAssignment =
      (slabObservablePairedSupportRecoupledAssignmentsResult
        D rootFaceId targetFaceId htarget second secondChoice).leftAssignment) :
    ((slabObservablePairedSupportCanonicalAnchor
        D rootFaceId targetFaceId htarget first).realize
      firstChoice).leftAssignment =
    ((slabObservablePairedSupportCanonicalAnchor
        D rootFaceId targetFaceId htarget second).realize
      secondChoice).leftAssignment := by
  exact heq

theorem slabObservablePairedSupportCanonicalAnchor_rightAssignment_eq_of_result_eq
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (first second : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (firstChoice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId first)
    (secondChoice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId second)
    (heq :
      (slabObservablePairedSupportRecoupledAssignmentsResult
        D rootFaceId targetFaceId htarget first firstChoice).rightAssignment =
      (slabObservablePairedSupportRecoupledAssignmentsResult
        D rootFaceId targetFaceId htarget second secondChoice).rightAssignment) :
    ((slabObservablePairedSupportCanonicalAnchor
        D rootFaceId targetFaceId htarget first).realize
      firstChoice).rightAssignment =
    ((slabObservablePairedSupportCanonicalAnchor
        D rootFaceId targetFaceId htarget second).realize
      secondChoice).rightAssignment := by
  exact heq

theorem slabObservablePairedSupportCanonicalAnchor_target_eq_of_result_eq
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (first second : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (firstChoice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId first)
    (secondChoice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId second)
    (hleftPhysical :
      slabObservablePairSupportSwitchedLeftPhysical
          D targetFaceId first.1 =
        slabObservablePairSupportSwitchedLeftPhysical
          D targetFaceId second.1)
    (hrightPhysical :
      slabObservablePairSupportSwitchedRightPhysical
          D targetFaceId first.1 =
        slabObservablePairSupportSwitchedRightPhysical
          D targetFaceId second.1)
    (hleftAssignment :
      (slabObservablePairedSupportRecoupledAssignmentsResult
        D rootFaceId targetFaceId htarget first firstChoice).leftAssignment =
      (slabObservablePairedSupportRecoupledAssignmentsResult
        D rootFaceId targetFaceId htarget second secondChoice).leftAssignment)
    (hrightAssignment :
      (slabObservablePairedSupportRecoupledAssignmentsResult
        D rootFaceId targetFaceId htarget first firstChoice).rightAssignment =
      (slabObservablePairedSupportRecoupledAssignmentsResult
        D rootFaceId targetFaceId htarget second secondChoice).rightAssignment) :
    transportSlabPhysicalPairRecouplingTargetAssignment
        hleftPhysical hrightPhysical firstChoice = secondChoice :=
  SlabPhysicalPairCanonicalAnchor.target_eq_of_realizations_eq
    (slabObservablePairedSupportCanonicalAnchor
      D rootFaceId targetFaceId htarget first)
    (slabObservablePairedSupportCanonicalAnchor
      D rootFaceId targetFaceId htarget second)
    hleftPhysical hrightPhysical firstChoice secondChoice
    (slabObservablePairedSupportCanonicalAnchor_leftAssignment_eq_of_result_eq
      D rootFaceId targetFaceId htarget first second
      firstChoice secondChoice hleftAssignment)
    (slabObservablePairedSupportCanonicalAnchor_rightAssignment_eq_of_result_eq
      D rootFaceId targetFaceId htarget first second
      firstChoice secondChoice hrightAssignment)

theorem slabObservablePairedSupportRecoupledLeftAssignment_mem
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId source) :
    let anchor := slabObservablePairedSupportCanonicalAnchor
      D rootFaceId targetFaceId htarget source
    (anchor.realize choice).leftAssignment ∈
      slabFineFusionWitnesses D
        (slabObservablePairSupportSwitchedLeftPhysical
          D targetFaceId source.1) :=
  (slabObservablePairedSupportCanonicalAnchor
    D rootFaceId targetFaceId htarget source).realize_left_mem choice

theorem slabObservablePairedSupportRecoupledRightAssignment_mem
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      D rootFaceId targetFaceId source) :
    let anchor := slabObservablePairedSupportCanonicalAnchor
      D rootFaceId targetFaceId htarget source
    (anchor.realize choice).rightAssignment ∈
      slabFineFusionWitnesses D
        (slabObservablePairSupportSwitchedRightPhysical
          D targetFaceId source.1) :=
  (slabObservablePairedSupportCanonicalAnchor
    D rootFaceId targetFaceId htarget source).realize_right_mem choice

end YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization.slabObservablePairedSupportSwitchedLeftPhysical_mem
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization.slabObservablePairedSupportSwitchedRightPhysical_mem
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization.slabObservablePairedSupportSwitchedLeftPhysical_bounded
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization.slabObservablePairedSupportSwitchedRightPhysical_bounded
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization.slabObservablePairedSupportCanonicalAnchor
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization.slabObservablePairedSupportRecoupledAssignmentsResult
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization.slabObservablePairedSupportCanonicalAnchor_leftAssignment_eq_of_result_eq
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization.slabObservablePairedSupportCanonicalAnchor_rightAssignment_eq_of_result_eq
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization.slabObservablePairedSupportCanonicalAnchor_target_eq_of_result_eq
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization.slabObservablePairedSupportRecoupledLeftAssignment_mem
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization.slabObservablePairedSupportRecoupledRightAssignment_mem
