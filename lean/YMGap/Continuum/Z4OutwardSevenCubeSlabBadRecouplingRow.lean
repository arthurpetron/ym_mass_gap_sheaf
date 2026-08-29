/-
# Accepted-pair closure of the seven-cube forced bypass

The outward seven-cube source is connected in physical union support, but its
two displayed bivalent bypass links force a target-to-root strand path for
every accepted left auxiliary assignment.  This module packages those two
edges for an arbitrary accepted two-replica pair whose left physical field is
the displayed seven-cube field and proves that the pair's connectedness
Boolean is true.

Together with the existing facts that a recoupled pair remains in the
four-cell source and preserves its left physical field, this is the geometric
input showing why the literal seven-cube row cannot furnish a pointwise
disconnection channel.  This module deliberately does not normalize the full
concrete recoupling list or state a zero-mass corollary.  A viable contraction
must instead use aggregate physical mass or a physical-label repair which
moves the source to a different row.

Constructive contract: explicit finite carriers, accepted assignments, and
Boolean computation only; no `Classical`, choice, `native_decide`, `sorry`,
new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4OutwardSevenCubeSlabPivotBypass

namespace YMGap.Continuum.Z4OutwardSevenCubeSlabBadRecouplingRow

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4OutwardSevenCubeSlabConnectedSource
open YMGap.Continuum.Z4OutwardSevenCubeSlabPivotBypass
open YMGap.Continuum.Z4OutwardSevenCubeSlabPivotRecouplingFloor
open YMGap.Continuum.Z4OutwardSevenCubeSlabSwitchingProfile

/-! ## Every accepted pair on the seven-cube left field is connected -/

/-- Transport a face-strand edge contravariantly along equality of the
physical labelling indexing its endpoint types. -/
private def castSlabFaceStrandEdge
    {physical targetPhysical : SlabLabelling}
    (hphysical : physical = targetPhysical)
    (edge : SlabFaceStrandEdge targetPhysical) :
    SlabFaceStrandEdge physical :=
  hphysical.symm ▸ edge

private theorem castSlabFaceStrandEdge_source_faceId
    {physical targetPhysical : SlabLabelling}
    (hphysical : physical = targetPhysical)
    (edge : SlabFaceStrandEdge targetPhysical) :
    (castSlabFaceStrandEdge hphysical edge).source.faceId =
      edge.source.faceId := by
  cases hphysical
  rfl

private theorem castSlabFaceStrandEdge_target_faceId
    {physical targetPhysical : SlabLabelling}
    (hphysical : physical = targetPhysical)
    (edge : SlabFaceStrandEdge targetPhysical) :
    (castSlabFaceStrandEdge hphysical edge).target.faceId =
      edge.target.faceId := by
  cases hphysical
  rfl

/-- Membership in the assembled strand-edge list is stable under the same
physical-labelling transport.  Keeping this lemma independent of an attached
source pair avoids dependent elimination on the whole pair. -/
private theorem castSlabFineFusionWitnessFaceStrandEdge_mem
    (D : SlabPhysicalData)
    {physical targetPhysical : SlabLabelling}
    (hphysical : physical = targetPhysical)
    (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈ slabFineFusionWitnesses D physical)
    (htargetAssignment : assignment ∈
      slabFineFusionWitnesses D targetPhysical)
    (edge : SlabFaceStrandEdge targetPhysical)
    (hedge : edge ∈ slabFineFusionWitnessFaceStrandEdges
      D targetPhysical assignment htargetAssignment) :
    castSlabFaceStrandEdge hphysical edge ∈
      slabFineFusionWitnessFaceStrandEdges
        D physical assignment hassignment := by
  cases hphysical
  exact hedge

/-- The forced bypass depends only on the displayed left physical field and
acceptance of its auxiliary assignment.  It therefore applies to any accepted
two-replica source pair over that field, independently of how the assignment
was produced. -/
theorem sevenCubeSwitchAcceptedPair_connected
    (pair : SlabObservableTwoReplicaPair sevenCubeSwitchPhysicalData
      sevenCubeSwitchRootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      sevenCubeSwitchPhysicalData sevenCubeSwitchRootFaceId
        sevenCubeSwitchTargetFaceId)
    (hphysical : pair.1.1.1 = sevenCubeSwitchLeftPhysical) :
    slabObservableTwoReplicaPairPairedFaceConnectedB
      sevenCubeSwitchPhysicalData sevenCubeSwitchRootFaceId
        sevenCubeSwitchTargetFaceId pair = true := by
  have hassignment : pair.1.1.2 ∈
      slabFusionWitnessAssignmentsOn 1 5 sevenCubeSwitchLeftPhysical
        (boundaryCompleteSlabLinks 5) := by
    rw [← hphysical]
    exact pair.1.assignment_mem
  let first := sevenCubeSwitchBypassFirst_globalForcedEdge
    pair.1.1.2 hassignment
  let second := sevenCubeSwitchBypassSecond_globalForcedEdge
    pair.1.1.2 hassignment
  let firstEdge := castSlabFaceStrandEdge hphysical first.edge
  let secondEdge := castSlabFaceStrandEdge hphysical second.edge
  have hfirst : firstEdge ∈ slabObservableTwoReplicaPairLeftStrandEdges
      sevenCubeSwitchPhysicalData pair := by
    exact castSlabFineFusionWitnessFaceStrandEdge_mem
      sevenCubeSwitchPhysicalData hphysical pair.1.1.2
        pair.1.assignment_mem hassignment first.edge first.edge_mem
  have hsecond : secondEdge ∈ slabObservableTwoReplicaPairLeftStrandEdges
      sevenCubeSwitchPhysicalData pair := by
    exact castSlabFineFusionWitnessFaceStrandEdge_mem
      sevenCubeSwitchPhysicalData hphysical pair.1.1.2
        pair.1.assignment_mem hassignment second.edge second.edge_mem
  have hfirstSource : firstEdge.source.faceId =
      sevenCubeSwitchTargetFaceId :=
    (castSlabFaceStrandEdge_source_faceId hphysical first.edge).trans
      first.source_eq
  have hfirstTarget : firstEdge.target.faceId =
      sevenCubeSwitchBypassMiddleFaceId :=
    (castSlabFaceStrandEdge_target_faceId hphysical first.edge).trans
      first.target_eq
  have hsecondSource : secondEdge.source.faceId =
      sevenCubeSwitchBypassMiddleFaceId :=
    (castSlabFaceStrandEdge_source_faceId hphysical second.edge).trans
      second.source_eq
  have hsecondTarget : secondEdge.target.faceId =
      sevenCubeSwitchRootFaceId :=
    (castSlabFaceStrandEdge_target_faceId hphysical second.edge).trans
      second.target_eq
  exact sevenCubeSwitchPair_connected_of_two_left_edges
    pair hpair firstEdge secondEdge hfirst hsecond
    hfirstSource hfirstTarget hsecondSource hsecondTarget

#print axioms sevenCubeSwitchAcceptedPair_connected

end YMGap.Continuum.Z4OutwardSevenCubeSlabBadRecouplingRow
