/-
# An accepted connected source for the seven-cube switching surface

Fix coupling one, cutoff one, and half-width two, so the corrected slab has
extent five.  The left physical replica is the selected seven-cube binary
surface and the right replica is the binary vacuum.  Positivity of their
finite spin-foam terms constructively extracts accepted global fusion
assignments, giving literal entries of the expanded source carriers.

Two selected faces of the seven-cube surface define the observable root and
target.  The existing constructive plaquette-path certificate is mapped to
the finite physical face graph: every shared geometric edge is a displayed
slab link, and root-component closure propagates along the path.  The resulting
pair is therefore an actual support-connected member of the source cell
`11 x 00`.

Constructive contract: explicit positive finite summands, Sigma-valued witness
extraction, and a retained geometric path; no choice, `Classical`,
`native_decide`, `sorry`, new axiom, or unbounded heartbeat.
-/

import YMGap.Continuum.BF4SU2OuterFineWitnessRoutingReduction
import YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
import YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
import YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
import YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedGeometry
import YMGap.Continuum.Z4OutwardSevenCubeCycleConnectedRoots
import YMGap.Continuum.Z4OutwardSevenCubeSlabPivotRecouplingFloor

namespace YMGap.Continuum.Z4OutwardSevenCubeSlabConnectedSource

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2OuterFineWitnessRoutingReduction
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedGeometry
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2SlabGlobalRecouplingWitnessRealization
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4OutwardSevenCubeCycleConnectedRoots
open YMGap.Continuum.Z4OutwardSevenCubeCycleGeometry
open YMGap.Continuum.Z4OutwardSevenCubeSlabPivotRecouplingFloor
open YMGap.Continuum.Z4OutwardSevenCubeSlabSwitchingProfile
open YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
open YMGap.Continuum.Z4UnitCubeIncidenceParity

/-! ## 1. Fixed physical datum and two marked faces -/

def sevenCubeSwitchPhysicalData : SlabPhysicalData where
  coupling := 1
  coupling_nonnegative := by decide
  cutoff := 1
  half := 2

theorem sevenCubeSwitchPhysicalData_extent :
    sevenCubeSwitchPhysicalData.extent = 5 := rfl

def sevenCubeSwitchRootFaceId : Nat :=
  slabFaceIdOfPlaquette 5 outwardYQueryFace

def sevenCubeSwitchTargetFaceId : Nat :=
  slabFaceIdOfPlaquette 5 outwardZQueryFace

private theorem outwardYQueryFace_mem_slab :
    outwardYQueryFace ∈ boundaryCompleteSlabPlaquettes 5 :=
  sevenCubeSwitchSurface_subset_slab_five _
    sevenCube011To100_queryFaces.1.2.1

private theorem outwardZQueryFace_mem_slab :
    outwardZQueryFace ∈ boundaryCompleteSlabPlaquettes 5 :=
  sevenCubeSwitchSurface_subset_slab_five _
    sevenCube011To100_queryFaces.1.2.2

theorem sevenCubeSwitchRootFaceId_physical :
    sevenCubeSwitchRootFaceId ∈ slabPhysicalFaceEdges 5 :=
  slabFaceIdOfPlaquette_physical outwardYQueryFace_mem_slab

theorem sevenCubeSwitchTargetFaceId_physical :
    sevenCubeSwitchTargetFaceId ∈ slabPhysicalFaceEdges 5 :=
  slabFaceIdOfPlaquette_physical outwardZQueryFace_mem_slab

/-! ## 2. Positive physical terms and accepted global assignments -/

private theorem qOfNat_pos_of_pos {n : Nat} (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact Q'.ofNat_succ_pos m

private theorem binarySupportPhysicalTerm_pos
    (support : List Z4Plaq)
    (hsubset : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boundaryCompleteSlabPlaquettes 5)
    (hnodup : support.Nodup)
    (heven : EvenFaceIncidence support) :
    (0 : Q') < sevenCubeSwitchPhysicalData.physicalTerm
      (slabBinarySupportLabelling 5 support) := by
  have hbounded : SlabFaceLabellingBounded 1 5
      (slabBinarySupportLabelling 5 support) := by
    intro id _
    exact slabBinarySupportLabelling_le_one 5 support id
  have hface : (0 : Q') < slabParametricKPhysicalFaceFactor
      sevenCubeSwitchPhysicalData.coupling
      sevenCubeSwitchPhysicalData.cutoff
      sevenCubeSwitchPhysicalData.extent
      (slabBinarySupportLabelling 5 support) :=
    slabParametricKPhysicalFaceFactor_pos_of_bounded
      sevenCubeSwitchPhysicalData (by decide)
      (slabBinarySupportLabelling 5 support) hbounded
  have hlinks : 0 < slabExplicitLinkMultiplicityProduct 1 5
      (slabBinarySupportLabelling 5 support) :=
    slabBinarySupport_linkMultiplicityProduct_pos
      (by omega) hsubset hnodup heven
  unfold SlabPhysicalData.physicalTerm slabParametricKPhysicalTerm
  exact Q'.mul_pos hface (qOfNat_pos_of_pos hlinks)

theorem sevenCubeSwitchLeftPhysicalTerm_pos :
    (0 : Q') < sevenCubeSwitchPhysicalData.physicalTerm
      sevenCubeSwitchLeftPhysical := by
  change (0 : Q') < sevenCubeSwitchPhysicalData.physicalTerm
    (slabBinarySupportLabelling 5 sevenCubeSwitchSurface)
  exact binarySupportPhysicalTerm_pos sevenCubeSwitchSurface
    sevenCubeSwitchSurface_subset_slab_five
    sevenCubeSwitchSurface_nodup
    sevenCubeSwitchSurface_evenFaceIncidence

theorem sevenCubeSwitchRightPhysicalTerm_pos :
    (0 : Q') < sevenCubeSwitchPhysicalData.physicalTerm
      sevenCubeSwitchRightPhysical := by
  change (0 : Q') < sevenCubeSwitchPhysicalData.physicalTerm
    (slabBinarySupportLabelling 5 [])
  exact binarySupportPhysicalTerm_pos []
    (fun plaquette hmem => False.elim (List.not_mem_nil hmem))
    List.nodup_nil (fun _ => rfl)

def sevenCubeSwitchLeftFineWitness :
    Σ' witness : SlabFusionWitnessAssignment,
      witness ∈ slabFineFusionWitnesses
        sevenCubeSwitchPhysicalData sevenCubeSwitchLeftPhysical :=
  positivePhysicalTermFineFusionWitness
    sevenCubeSwitchPhysicalData sevenCubeSwitchLeftPhysical
    sevenCubeSwitchLeftPhysicalTerm_pos

def sevenCubeSwitchRightFineWitness :
    Σ' witness : SlabFusionWitnessAssignment,
      witness ∈ slabFineFusionWitnesses
        sevenCubeSwitchPhysicalData sevenCubeSwitchRightPhysical :=
  positivePhysicalTermFineFusionWitness
    sevenCubeSwitchPhysicalData sevenCubeSwitchRightPhysical
    sevenCubeSwitchRightPhysicalTerm_pos

/-! ## 3. Literal entries of cells `11` and `00` -/

theorem sevenCubeSwitchFace_positive
    (plaquette : Z4Plaq) (hplaquette : plaquette ∈ sevenCubeSwitchSurface) :
    0 < sevenCubeSwitchLeftPhysical
      (slabFaceIdOfPlaquette 5 plaquette) := by
  have hslab :=
    sevenCubeSwitchSurface_subset_slab_five plaquette hplaquette
  have hphysical := slabFaceIdOfPlaquette_physical hslab
  unfold sevenCubeSwitchLeftPhysical
  rw [slabBinarySupportLabelling_eq_indicator hphysical,
    slabPlaquetteAt_faceIdOfPlaquette hslab, if_pos hplaquette]
  omega

theorem sevenCubeSwitchRightPhysical_zero (faceId : Nat) :
    sevenCubeSwitchRightPhysical faceId = 0 := by
  unfold sevenCubeSwitchRightPhysical slabBinarySupportLabelling
  split <;> simp

theorem sevenCubeSwitchLeftPhysical_mem :
    sevenCubeSwitchLeftPhysical ∈
      sevenCubeSwitchPhysicalData.physicalLabellings := by
  unfold SlabPhysicalData.physicalLabellings SlabPhysicalData.faceEdges
  change slabBinarySupportLabelling 5 sevenCubeSwitchSurface ∈
    boundedEdgeLabellings 1 (slabPhysicalFaceEdges 5)
  exact slabBinarySupportLabelling_mem (by omega) sevenCubeSwitchSurface

theorem sevenCubeSwitchRightPhysical_mem :
    sevenCubeSwitchRightPhysical ∈
      sevenCubeSwitchPhysicalData.physicalLabellings := by
  unfold SlabPhysicalData.physicalLabellings SlabPhysicalData.faceEdges
  change slabBinarySupportLabelling 5 [] ∈
    boundedEdgeLabellings 1 (slabPhysicalFaceEdges 5)
  exact slabBinarySupportLabelling_mem (by omega) []

def sevenCubeSwitchLeftPositiveEntry :
    {source : SlabLabelling × SlabFusionWitnessAssignment //
      source ∈ slabObservablePositiveExpandedSources
        sevenCubeSwitchPhysicalData sevenCubeSwitchRootFaceId} :=
  slabObservablePositiveSourceEntryOfCarrier
    sevenCubeSwitchPhysicalData sevenCubeSwitchRootFaceId
    sevenCubeSwitchLeftPhysical sevenCubeSwitchLeftPhysical_mem
    sevenCubeSwitchLeftFineWitness.1 sevenCubeSwitchLeftFineWitness.2
    (sevenCubeSwitchFace_positive outwardYQueryFace
      sevenCube011To100_queryFaces.1.2.1)

def sevenCubeSwitchRightExpandedEntry :
    {source : SlabLabelling × SlabFusionWitnessAssignment //
      source ∈ slabExpandedFineSources sevenCubeSwitchPhysicalData} :=
  slabExpandedFineSourceEntryOfCarrier
    sevenCubeSwitchPhysicalData sevenCubeSwitchRightPhysical
    sevenCubeSwitchRightPhysical_mem
    sevenCubeSwitchRightFineWitness.1 sevenCubeSwitchRightFineWitness.2

@[simp] theorem sevenCubeSwitchLeftPositiveEntry_physical :
    sevenCubeSwitchLeftPositiveEntry.1.1 = sevenCubeSwitchLeftPhysical := by
  unfold sevenCubeSwitchLeftPositiveEntry
  apply slabObservablePositiveSourceEntryOfCarrier_physical

@[simp] theorem sevenCubeSwitchRightExpandedEntry_physical :
    sevenCubeSwitchRightExpandedEntry.1.1 = sevenCubeSwitchRightPhysical := by
  unfold sevenCubeSwitchRightExpandedEntry
  apply slabExpandedFineSourceEntryOfCarrier_physical

theorem sevenCubeSwitchLeftPositiveEntry_mem_rootTarget :
    sevenCubeSwitchLeftPositiveEntry ∈
      slabObservableRootTargetEntries sevenCubeSwitchPhysicalData
        sevenCubeSwitchRootFaceId sevenCubeSwitchTargetFaceId := by
  apply List.mem_filter.mpr
  refine ⟨List.mem_attach _ sevenCubeSwitchLeftPositiveEntry, ?_⟩
  unfold SlabObservablePositiveSourceEntry.facePositiveB
  exact decide_eq_true
    (sevenCubeSwitchFace_positive outwardZQueryFace
      sevenCube011To100_queryFaces.1.2.2)

theorem sevenCubeSwitchRightExpandedEntry_mem_rootComplementTargetComplement :
    sevenCubeSwitchRightExpandedEntry ∈
      slabObservableRootComplementTargetComplementEntries
        sevenCubeSwitchPhysicalData
        sevenCubeSwitchRootFaceId sevenCubeSwitchTargetFaceId := by
  apply List.mem_filter.mpr
  refine ⟨List.mem_attach _ sevenCubeSwitchRightExpandedEntry, ?_⟩
  unfold SlabExpandedFineSourceEntry.facePositiveB
  rw [sevenCubeSwitchRightExpandedEntry_physical,
    sevenCubeSwitchRightPhysical_zero,
    sevenCubeSwitchRightPhysical_zero]
  rfl

def sevenCubeSwitchSourcePair :
    ({source : SlabLabelling × SlabFusionWitnessAssignment //
        source ∈ slabObservablePositiveExpandedSources
          sevenCubeSwitchPhysicalData sevenCubeSwitchRootFaceId}) ×
      {source : SlabLabelling × SlabFusionWitnessAssignment //
        source ∈ slabExpandedFineSources sevenCubeSwitchPhysicalData} :=
  (sevenCubeSwitchLeftPositiveEntry, sevenCubeSwitchRightExpandedEntry)

theorem sevenCubeSwitchSourcePair_mem_fourCell :
    sevenCubeSwitchSourcePair ∈
      slabObservableFourCellSourcePairs sevenCubeSwitchPhysicalData
        sevenCubeSwitchRootFaceId sevenCubeSwitchTargetFaceId := by
  apply (mem_cartesian_iff _ _ sevenCubeSwitchSourcePair).mpr
  exact ⟨sevenCubeSwitchLeftPositiveEntry_mem_rootTarget,
    sevenCubeSwitchRightExpandedEntry_mem_rootComplementTargetComplement⟩

/-! ## 4. Map the retained plaquette path into the support component -/

private theorem sevenCubeFaceId_mem_incident
    {plaquette : Z4Plaq} {link : Z4Link}
    (hplaquette : plaquette ∈ sevenCubeSwitchSurface)
    (hedge : link ∈ edgesOf plaquette) :
    slabFaceIdOfPlaquette 5 plaquette ∈ slabIncidentPlaqIds 5 link := by
  have hslab := sevenCubeSwitchSurface_subset_slab_five _ hplaquette
  have hphysical := slabFaceIdOfPlaquette_physical hslab
  apply mem_slabIncidentPlaqIds.mpr
  refine ⟨plaquette, ?_, hedge⟩
  simpa only [slabPlaquetteAt_faceIdOfPlaquette hslab] using
    slabPlaquetteAt_mem_enumerate hphysical

private theorem sevenCubeFaceId_mem_supportVertices
    {plaquette : Z4Plaq} (hplaquette : plaquette ∈ sevenCubeSwitchSurface) :
    slabFaceIdOfPlaquette 5 plaquette ∈
      slabTwoReplicaSupportFaceVertices 5
        sevenCubeSwitchLeftPhysical sevenCubeSwitchRightPhysical := by
  have hslab := sevenCubeSwitchSurface_subset_slab_five _ hplaquette
  apply mem_slabTwoReplicaSupportFaceVertices
    (slabFaceIdOfPlaquette_physical hslab)
  exact Or.inl (sevenCubeSwitchFace_positive plaquette hplaquette)

private theorem sevenCubeFaceIds_adjacent
    {left right : Z4Plaq}
    (hleft : left ∈ sevenCubeSwitchSurface)
    (hright : right ∈ sevenCubeSwitchSurface)
    (hadjacent : z4Chain.toLattice.Adjacent left right) :
    slabSupportFaceAdjacentB 5
      (slabFaceIdOfPlaquette 5 left)
      (slabFaceIdOfPlaquette 5 right) = true := by
  obtain ⟨link, honLeft, honRight⟩ := hadjacent
  have hedgeLeft : link ∈ edgesOf left := of_decide_eq_true honLeft
  have hedgeRight : link ∈ edgesOf right := of_decide_eq_true honRight
  apply slabSupportFaceAdjacentB_true_of_link
    ((mem_boundaryCompleteSlabLinks_iff 5 link).mpr
      ⟨left, sevenCubeSwitchSurface_subset_slab_five left hleft,
        hedgeLeft⟩)
  · exact sevenCubeFaceId_mem_incident hleft hedgeLeft
  · exact sevenCubeFaceId_mem_incident hright hedgeRight

private def sevenCubeChainEndpoint_mem_targetComponent :
    {first last : Z4Plaq} →
    (hfirst : first ∈ sevenCubeSwitchSurface) →
    PolymerModel.ChainIn z4Chain.toLattice
      sevenCubeSwitchSurface first last →
    slabFaceIdOfPlaquette 5 first ∈
      slabTwoReplicaTargetSupportComponent 5
        sevenCubeSwitchLeftPhysical sevenCubeSwitchRightPhysical
        sevenCubeSwitchTargetFaceId →
    slabFaceIdOfPlaquette 5 last ∈
      slabTwoReplicaTargetSupportComponent 5
        sevenCubeSwitchLeftPhysical sevenCubeSwitchRightPhysical
        sevenCubeSwitchTargetFaceId
  | _, _, _, .refl _, hcomponent => hcomponent
  | _, _, hfirst, .step hadjacent hnext rest,
      hcomponent =>
      sevenCubeChainEndpoint_mem_targetComponent hnext rest
        (rootComponent_closed_under_edge
          (slabSupportFaceAdjacentB 5)
          (slabSupportFaceAdjacentB_symmetric 5)
          (sevenCubeFaceId_mem_supportVertices
            sevenCube011To100_queryFaces.1.2.2)
          hcomponent
          (sevenCubeFaceId_mem_supportVertices hnext)
          (sevenCubeFaceIds_adjacent hfirst hnext hadjacent))

theorem sevenCubeSwitchRoot_mem_targetSupportComponent :
    sevenCubeSwitchRootFaceId ∈
      slabTwoReplicaTargetSupportComponent 5
        sevenCubeSwitchLeftPhysical sevenCubeSwitchRightPhysical
        sevenCubeSwitchTargetFaceId := by
  have htargetComponent : sevenCubeSwitchTargetFaceId ∈
      slabTwoReplicaTargetSupportComponent 5
        sevenCubeSwitchLeftPhysical sevenCubeSwitchRightPhysical
        sevenCubeSwitchTargetFaceId := by
    unfold slabTwoReplicaTargetSupportComponent
    exact root_mem_rootComponent
      (slabSupportFaceAdjacentB 5)
      (sevenCubeFaceId_mem_supportVertices
        sevenCube011To100_queryFaces.1.2.2)
  exact sevenCubeChainEndpoint_mem_targetComponent
    sevenCube011To100_queryFaces.1.2.2
    (sevenCube011To100Surface_connected
      outwardZQueryFace outwardYQueryFace
      sevenCube011To100_queryFaces.1.2.2
      sevenCube011To100_queryFaces.1.2.1)
    htargetComponent

theorem sevenCubeSwitchSourcePair_connected :
    slabObservableTwoReplicaPairPairedSupportConnectedB
      sevenCubeSwitchPhysicalData sevenCubeSwitchRootFaceId
      sevenCubeSwitchTargetFaceId sevenCubeSwitchSourcePair = true := by
  unfold slabObservableTwoReplicaPairPairedSupportConnectedB
    slabObservableTwoReplicaPairPairedSupportSwapMask
    slabTwoReplicaSupportSwapMask sevenCubeSwitchSourcePair
  rw [sevenCubeSwitchLeftPositiveEntry_physical,
    sevenCubeSwitchRightExpandedEntry_physical]
  change decide (sevenCubeSwitchRootFaceId ∈
    slabTwoReplicaTargetSupportComponent 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchRightPhysical
      sevenCubeSwitchTargetFaceId) = true
  exact decide_eq_true sevenCubeSwitchRoot_mem_targetSupportComponent

/-! ## 5. The actual connected source -/

theorem sevenCubeSwitchSourcePair_mem_connectedFourCell :
    sevenCubeSwitchSourcePair ∈
      slabObservablePairedSupportConnectedFourCellSourcePairs
        sevenCubeSwitchPhysicalData sevenCubeSwitchRootFaceId
        sevenCubeSwitchTargetFaceId :=
  List.mem_filter.mpr
    ⟨sevenCubeSwitchSourcePair_mem_fourCell,
      sevenCubeSwitchSourcePair_connected⟩

def sevenCubeSwitchConnectedStrandSource :
    {pair : SlabObservableTwoReplicaPair sevenCubeSwitchPhysicalData
        sevenCubeSwitchRootFaceId //
      pair ∈ slabObservablePairedSupportConnectedFourCellSourcePairs
        sevenCubeSwitchPhysicalData sevenCubeSwitchRootFaceId
        sevenCubeSwitchTargetFaceId} :=
  ⟨sevenCubeSwitchSourcePair,
    sevenCubeSwitchSourcePair_mem_connectedFourCell⟩

end YMGap.Continuum.Z4OutwardSevenCubeSlabConnectedSource

#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabConnectedSource.sevenCubeSwitchLeftPhysicalTerm_pos
#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabConnectedSource.sevenCubeSwitchRightPhysicalTerm_pos
#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabConnectedSource.sevenCubeSwitchSourcePair_mem_fourCell
#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabConnectedSource.sevenCubeSwitchRoot_mem_targetSupportComponent
#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabConnectedSource.sevenCubeSwitchSourcePair_connected
#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabConnectedSource.sevenCubeSwitchConnectedStrandSource
