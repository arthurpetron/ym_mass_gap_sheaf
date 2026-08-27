/-
# Global accepted assignments for the paired-face switch

The paired union component supplies one face mask closed across every strand
edge of both accepted source replicas.  Restricting that mask to each
boundary-complete slab link gives the two partner-closed local selections
required by the original-cutoff cross-replica switch compiler.

This module assembles those local outputs in the literal production link
order.  The result is a pair of complete accepted fusion-witness assignments
over the two face-swapped physical labellings.  No decoder or injectivity
claim is made here; recovering the two source intertwiner fields from their
crossed sums is the next finite combinatorial frontier.

Constructive contract: finite graph closure, decidable link membership, and
structural Cartesian assembly only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, `noncomputable`, or enlarged
heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabCrossReplicaLocalSwitch
import YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
import YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment

namespace YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAssignment

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabCrossReplicaLocalSwitch
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabPhysicalSelectionPullback
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Source physical fields retain the datum cutoff -/

/-- Every attached expanded source inherits the literal physical Cartesian
cutoff bound from its source membership. -/
theorem SlabExpandedFineSourceEntry.physical_bounded
    {D : SlabPhysicalData} (entry : SlabExpandedFineSourceEntry D) :
    SlabFaceLabellingBounded D.cutoff D.extent entry.1.1 := by
  have hphysical := (mem_slabExpandedFineSources_iff.mp entry.2).1
  have hsound := boundedEdgeLabellings_sound
    D.cutoff D.faceEdges entry.1.1 hphysical
  intro faceId hface
  exact Nat.le_of_lt_succ (hsound.1 faceId (by
    unfold SlabPhysicalData.faceEdges
    exact hface))

/-- The positive first-replica subtype carries the same physical bound. -/
theorem SlabObservablePositiveSourceEntry.physical_bounded
    {D : SlabPhysicalData} {faceId : Nat}
    (entry : SlabObservablePositiveSourceEntry D faceId) :
    SlabFaceLabellingBounded D.cutoff D.extent entry.1.1 :=
  SlabExpandedFineSourceEntry.physical_bounded
    ⟨entry.1, entry.source_mem_expanded⟩

/-! ## 2. The paired mask restricted to each source link -/

/-- Linkwise partner-closed selection in the first replica induced by the
paired target component. -/
def slabObservablePairLeftSelectionAtLink
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (linked : {link // link ∈ boundaryCompleteSlabLinks D.extent}) :
    let auxiliary := slabFusionWitnessAssignmentAt linked.1 pair.1.1.2
    let hmem := slabFusionWitnessAssignmentAt_mem_local
      D.cutoff D.extent pair.1.1.1
      (boundaryCompleteSlabLinks D.extent) pair.1.1.2
      pair.1.assignment_mem linked.1 linked.2
    SlabLinkPartnerClosedFaceSelection
      D.cutoff D.extent pair.1.1.1 linked.1 auxiliary hmem := by
  dsimp
  apply slabGlobalEdgeClosedSelectionAtLink
    (selected := fun copy =>
      slabObservableTwoReplicaPairPairedFaceSwapMask
        D pair targetFaceId copy.faceId)
  intro edge hedge
  exact slabObservableTwoReplicaPairPairedFaceSwapMask_eq_of_left_edge
    D rootFaceId targetFaceId htarget pair hpair hedge

/-- The same paired face mask restricted to the second source replica. -/
def slabObservablePairRightSelectionAtLink
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (linked : {link // link ∈ boundaryCompleteSlabLinks D.extent}) :
    let auxiliary := slabFusionWitnessAssignmentAt linked.1 pair.2.1.2
    let hmem := slabFusionWitnessAssignmentAt_mem_local
      D.cutoff D.extent pair.2.1.1
      (boundaryCompleteSlabLinks D.extent) pair.2.1.2
      (slabExpandedFineSourceEntryAssignment_mem pair.2)
      linked.1 linked.2
    SlabLinkPartnerClosedFaceSelection
      D.cutoff D.extent pair.2.1.1 linked.1 auxiliary hmem := by
  dsimp
  apply slabGlobalEdgeClosedSelectionAtLink
    (selected := fun copy =>
      slabObservableTwoReplicaPairPairedFaceSwapMask
        D pair targetFaceId copy.faceId)
  intro edge hedge
  exact slabObservableTwoReplicaPairPairedFaceSwapMask_eq_of_right_edge
    D rootFaceId targetFaceId htarget pair hpair hedge

/-! ## 3. Total local switched fields and structural assembly -/

/-- Totalized first-output auxiliary field.  The zero branch lies outside the
assembled link list and is never used by the membership theorem. -/
def slabObservablePairSwitchedLeftAuxiliaryAt
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (link : SlabLink) : SlabLabelling :=
  if hlink : link ∈ boundaryCompleteSlabLinks D.extent then
    slabCrossReplicaLeftAuxiliary
      (slabObservablePairLeftSelectionAtLink
        D rootFaceId targetFaceId htarget pair hpair ⟨link, hlink⟩)
      (slabObservablePairRightSelectionAtLink
        D rootFaceId targetFaceId htarget pair hpair ⟨link, hlink⟩)
  else zeroEdgeLabelling

/-- Totalized second-output auxiliary field. -/
def slabObservablePairSwitchedRightAuxiliaryAt
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (link : SlabLink) : SlabLabelling :=
  if hlink : link ∈ boundaryCompleteSlabLinks D.extent then
    slabCrossReplicaRightAuxiliary
      (slabObservablePairLeftSelectionAtLink
        D rootFaceId targetFaceId htarget pair hpair ⟨link, hlink⟩)
      (slabObservablePairRightSelectionAtLink
        D rootFaceId targetFaceId htarget pair hpair ⟨link, hlink⟩)
  else zeroEdgeLabelling

def slabObservablePairSwitchedLeftAssignment
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) : SlabFusionWitnessAssignment :=
  slabFusionWitnessAssignmentFrom
    (boundaryCompleteSlabLinks D.extent)
    (slabObservablePairSwitchedLeftAuxiliaryAt
      D rootFaceId targetFaceId htarget pair hpair)

def slabObservablePairSwitchedRightAssignment
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) : SlabFusionWitnessAssignment :=
  slabFusionWitnessAssignmentFrom
    (boundaryCompleteSlabLinks D.extent)
    (slabObservablePairSwitchedRightAuxiliaryAt
      D rootFaceId targetFaceId htarget pair hpair)

/-! ## 4. Both global outputs inhabit the exact production fibers -/

theorem slabObservablePairSwitchedLeftAssignment_mem
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    slabObservablePairSwitchedLeftAssignment
        D rootFaceId targetFaceId htarget pair hpair ∈
      slabFineFusionWitnesses D
        (twoReplicaFaceSwapLeft
          (slabObservableTwoReplicaPairPairedFaceSwapMask
            D pair targetFaceId)
          pair.1.1.1 pair.2.1.1) := by
  unfold slabObservablePairSwitchedLeftAssignment slabFineFusionWitnesses
  apply slabFusionWitnessAssignmentFrom_mem
  intro link hlink
  unfold slabObservablePairSwitchedLeftAuxiliaryAt
  rw [dif_pos hlink]
  apply slabCrossReplicaLeftAuxiliary_mem
    (slabObservableTwoReplicaPairPairedFaceSwapMask D pair targetFaceId)
    (SlabObservablePositiveSourceEntry.physical_bounded pair.1)
    (SlabExpandedFineSourceEntry.physical_bounded pair.2)
  · intro copy
    simp [slabObservablePairLeftSelectionAtLink]
  · intro copy
    simp [slabObservablePairRightSelectionAtLink]

theorem slabObservablePairSwitchedRightAssignment_mem
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    slabObservablePairSwitchedRightAssignment
        D rootFaceId targetFaceId htarget pair hpair ∈
      slabFineFusionWitnesses D
        (twoReplicaFaceSwapRight
          (slabObservableTwoReplicaPairPairedFaceSwapMask
            D pair targetFaceId)
          pair.1.1.1 pair.2.1.1) := by
  unfold slabObservablePairSwitchedRightAssignment slabFineFusionWitnesses
  apply slabFusionWitnessAssignmentFrom_mem
  intro link hlink
  unfold slabObservablePairSwitchedRightAuxiliaryAt
  rw [dif_pos hlink]
  apply slabCrossReplicaRightAuxiliary_mem
    (slabObservableTwoReplicaPairPairedFaceSwapMask D pair targetFaceId)
    (SlabObservablePositiveSourceEntry.physical_bounded pair.1)
    (SlabExpandedFineSourceEntry.physical_bounded pair.2)
  · intro copy
    simp [slabObservablePairLeftSelectionAtLink]
  · intro copy
    simp [slabObservablePairRightSelectionAtLink]

#print axioms SlabExpandedFineSourceEntry.physical_bounded
#print axioms SlabObservablePositiveSourceEntry.physical_bounded
#print axioms slabObservablePairLeftSelectionAtLink
#print axioms slabObservablePairRightSelectionAtLink
#print axioms slabObservablePairSwitchedLeftAssignment_mem
#print axioms slabObservablePairSwitchedRightAssignment_mem

end YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAssignment
