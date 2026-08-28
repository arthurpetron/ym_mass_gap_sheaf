/-
# An accepted connected source for the outward Y/Z cut carrier

At coupling one, cutoff one, and half-width two, positivity of the twelve-face
binary surface and of the vacuum constructively extracts accepted global
fusion assignments.  The already proved connectedness of the edge-touch
surface maps to the finite physical support graph between the marked outward
Z and Y faces.  Together these data form a literal connected source in the
observable four-cell.

Constructive contract: positive finite summands, Sigma-valued witness
extraction, and a retained geometric path; no choice, `Classical`,
`native_decide`, `sorry`, new axiom, or unbounded heartbeat.
-/

import YMGap.Continuum.BF4SU2OuterFineWitnessRoutingReduction
import YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
import YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
import YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
import YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedGeometry
import YMGap.Continuum.Z4OutwardYZEdgeTouchSlabWholeProductPositivity

namespace YMGap.Continuum.Z4OutwardYZEdgeTouchSlabConnectedSource

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
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2SlabGlobalRecouplingWitnessRealization
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier
open YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabWholeProductPositivity
open YMGap.Continuum.Z4UnitCubeIncidenceParity

/-! ## 1. Fixed datum and marked faces -/

def outwardYZSwitchPhysicalData : SlabPhysicalData where
  coupling := 1
  coupling_nonnegative := by decide
  cutoff := 1
  half := 2

theorem outwardYZSwitchPhysicalData_extent :
    outwardYZSwitchPhysicalData.extent = 5 := rfl

def outwardYZSwitchRootFaceId : Nat :=
  slabFaceIdOfPlaquette 5 outwardYQueryFace

def outwardYZSwitchTargetFaceId : Nat :=
  slabFaceIdOfPlaquette 5 outwardZQueryFace

private theorem outwardYQueryFace_mem_slab :
    outwardYQueryFace ∈ boundaryCompleteSlabPlaquettes 5 :=
  outwardYZSwitchSurface_subset_slab_five _ outwardYQueryFace_mem_YZ

private theorem outwardZQueryFace_mem_slab :
    outwardZQueryFace ∈ boundaryCompleteSlabPlaquettes 5 :=
  outwardYZSwitchSurface_subset_slab_five _ outwardZQueryFace_mem_YZ

theorem outwardYZSwitchRootFaceId_physical :
    outwardYZSwitchRootFaceId ∈ slabPhysicalFaceEdges 5 :=
  slabFaceIdOfPlaquette_physical outwardYQueryFace_mem_slab

theorem outwardYZSwitchTargetFaceId_physical :
    outwardYZSwitchTargetFaceId ∈ slabPhysicalFaceEdges 5 :=
  slabFaceIdOfPlaquette_physical outwardZQueryFace_mem_slab

/-! ## 2. Positive terms and accepted global assignments -/

private theorem qOfNat_pos_of_pos {n : Nat} (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact Q'.ofNat_succ_pos m

private theorem binarySupportPhysicalTerm_pos
    (support : List Z4Plaq)
    (hsubset : forall plaquette, plaquette ∈ support ->
      plaquette ∈ boundaryCompleteSlabPlaquettes 5)
    (hnodup : support.Nodup)
    (heven : EvenFaceIncidence support) :
    (0 : Q') < outwardYZSwitchPhysicalData.physicalTerm
      (slabBinarySupportLabelling 5 support) := by
  have hbounded : SlabFaceLabellingBounded 1 5
      (slabBinarySupportLabelling 5 support) := by
    intro id _
    exact slabBinarySupportLabelling_le_one 5 support id
  have hface : (0 : Q') < slabParametricKPhysicalFaceFactor
      outwardYZSwitchPhysicalData.coupling
      outwardYZSwitchPhysicalData.cutoff
      outwardYZSwitchPhysicalData.extent
      (slabBinarySupportLabelling 5 support) :=
    slabParametricKPhysicalFaceFactor_pos_of_bounded
      outwardYZSwitchPhysicalData (by decide)
      (slabBinarySupportLabelling 5 support) hbounded
  have hlinks : 0 < slabExplicitLinkMultiplicityProduct 1 5
      (slabBinarySupportLabelling 5 support) :=
    slabBinarySupport_linkMultiplicityProduct_pos
      (by omega) hsubset hnodup heven
  unfold SlabPhysicalData.physicalTerm slabParametricKPhysicalTerm
  exact Q'.mul_pos hface (qOfNat_pos_of_pos hlinks)

theorem outwardYZSwitchLeftPhysicalTerm_pos :
    (0 : Q') < outwardYZSwitchPhysicalData.physicalTerm
      outwardYZSwitchLeftPhysical := by
  change (0 : Q') < outwardYZSwitchPhysicalData.physicalTerm
    (slabBinarySupportLabelling 5 outwardYZSwitchSurface)
  exact binarySupportPhysicalTerm_pos outwardYZSwitchSurface
    outwardYZSwitchSurface_subset_slab_five
    outwardYZSwitchSurface_nodup
    outwardYZSwitchSurface_evenFaceIncidence

theorem outwardYZSwitchRightPhysicalTerm_pos :
    (0 : Q') < outwardYZSwitchPhysicalData.physicalTerm
      outwardYZSwitchRightPhysical := by
  change (0 : Q') < outwardYZSwitchPhysicalData.physicalTerm
    (slabBinarySupportLabelling 5 [])
  exact binarySupportPhysicalTerm_pos []
    (fun plaquette hmem => False.elim (List.not_mem_nil hmem))
    List.nodup_nil (fun _ => rfl)

def outwardYZSwitchLeftFineWitness :
    Σ' witness : SlabFusionWitnessAssignment,
      witness ∈ slabFineFusionWitnesses
        outwardYZSwitchPhysicalData outwardYZSwitchLeftPhysical :=
  positivePhysicalTermFineFusionWitness
    outwardYZSwitchPhysicalData outwardYZSwitchLeftPhysical
    outwardYZSwitchLeftPhysicalTerm_pos

def outwardYZSwitchRightFineWitness :
    Σ' witness : SlabFusionWitnessAssignment,
      witness ∈ slabFineFusionWitnesses
        outwardYZSwitchPhysicalData outwardYZSwitchRightPhysical :=
  positivePhysicalTermFineFusionWitness
    outwardYZSwitchPhysicalData outwardYZSwitchRightPhysical
    outwardYZSwitchRightPhysicalTerm_pos

/-! ## 3. Literal entries of cells `11` and `00` -/

theorem outwardYZSwitchFace_positive
    (plaquette : Z4Plaq) (hplaquette : plaquette ∈ outwardYZSwitchSurface) :
    0 < outwardYZSwitchLeftPhysical
      (slabFaceIdOfPlaquette 5 plaquette) := by
  have hslab := outwardYZSwitchSurface_subset_slab_five plaquette hplaquette
  have hphysical := slabFaceIdOfPlaquette_physical hslab
  unfold outwardYZSwitchLeftPhysical
  rw [slabBinarySupportLabelling_eq_indicator hphysical,
    slabPlaquetteAt_faceIdOfPlaquette hslab, if_pos hplaquette]
  omega

theorem outwardYZSwitchRightPhysical_zero (faceId : Nat) :
    outwardYZSwitchRightPhysical faceId = 0 := by
  unfold outwardYZSwitchRightPhysical slabBinarySupportLabelling
  split <;> simp

theorem outwardYZSwitchLeftPhysical_mem :
    outwardYZSwitchLeftPhysical ∈
      outwardYZSwitchPhysicalData.physicalLabellings := by
  unfold SlabPhysicalData.physicalLabellings SlabPhysicalData.faceEdges
  change slabBinarySupportLabelling 5 outwardYZSwitchSurface ∈
    boundedEdgeLabellings 1 (slabPhysicalFaceEdges 5)
  exact slabBinarySupportLabelling_mem (by omega) outwardYZSwitchSurface

theorem outwardYZSwitchRightPhysical_mem :
    outwardYZSwitchRightPhysical ∈
      outwardYZSwitchPhysicalData.physicalLabellings := by
  unfold SlabPhysicalData.physicalLabellings SlabPhysicalData.faceEdges
  change slabBinarySupportLabelling 5 [] ∈
    boundedEdgeLabellings 1 (slabPhysicalFaceEdges 5)
  exact slabBinarySupportLabelling_mem (by omega) []

def outwardYZSwitchLeftPositiveEntry :
    {source : SlabLabelling × SlabFusionWitnessAssignment //
      source ∈ slabObservablePositiveExpandedSources
        outwardYZSwitchPhysicalData outwardYZSwitchRootFaceId} :=
  slabObservablePositiveSourceEntryOfCarrier
    outwardYZSwitchPhysicalData outwardYZSwitchRootFaceId
    outwardYZSwitchLeftPhysical outwardYZSwitchLeftPhysical_mem
    outwardYZSwitchLeftFineWitness.1 outwardYZSwitchLeftFineWitness.2
    (outwardYZSwitchFace_positive outwardYQueryFace
      outwardYQueryFace_mem_YZ)

def outwardYZSwitchRightExpandedEntry :
    {source : SlabLabelling × SlabFusionWitnessAssignment //
      source ∈ slabExpandedFineSources outwardYZSwitchPhysicalData} :=
  slabExpandedFineSourceEntryOfCarrier
    outwardYZSwitchPhysicalData outwardYZSwitchRightPhysical
    outwardYZSwitchRightPhysical_mem
    outwardYZSwitchRightFineWitness.1 outwardYZSwitchRightFineWitness.2

@[simp] theorem outwardYZSwitchLeftPositiveEntry_physical :
    outwardYZSwitchLeftPositiveEntry.1.1 = outwardYZSwitchLeftPhysical := by
  unfold outwardYZSwitchLeftPositiveEntry
  apply slabObservablePositiveSourceEntryOfCarrier_physical

@[simp] theorem outwardYZSwitchRightExpandedEntry_physical :
    outwardYZSwitchRightExpandedEntry.1.1 = outwardYZSwitchRightPhysical := by
  unfold outwardYZSwitchRightExpandedEntry
  apply slabExpandedFineSourceEntryOfCarrier_physical

theorem outwardYZSwitchLeftPositiveEntry_mem_rootTarget :
    outwardYZSwitchLeftPositiveEntry ∈
      slabObservableRootTargetEntries outwardYZSwitchPhysicalData
        outwardYZSwitchRootFaceId outwardYZSwitchTargetFaceId := by
  apply List.mem_filter.mpr
  refine ⟨List.mem_attach _ outwardYZSwitchLeftPositiveEntry, ?_⟩
  unfold SlabObservablePositiveSourceEntry.facePositiveB
  exact decide_eq_true
    (outwardYZSwitchFace_positive outwardZQueryFace
      outwardZQueryFace_mem_YZ)

theorem outwardYZSwitchRightExpandedEntry_mem_rootComplementTargetComplement :
    outwardYZSwitchRightExpandedEntry ∈
      slabObservableRootComplementTargetComplementEntries
        outwardYZSwitchPhysicalData
        outwardYZSwitchRootFaceId outwardYZSwitchTargetFaceId := by
  apply List.mem_filter.mpr
  refine ⟨List.mem_attach _ outwardYZSwitchRightExpandedEntry, ?_⟩
  unfold SlabExpandedFineSourceEntry.facePositiveB
  rw [outwardYZSwitchRightExpandedEntry_physical,
    outwardYZSwitchRightPhysical_zero,
    outwardYZSwitchRightPhysical_zero]
  rfl

def outwardYZSwitchSourcePair :
    ({source : SlabLabelling × SlabFusionWitnessAssignment //
        source ∈ slabObservablePositiveExpandedSources
          outwardYZSwitchPhysicalData outwardYZSwitchRootFaceId}) ×
      {source : SlabLabelling × SlabFusionWitnessAssignment //
        source ∈ slabExpandedFineSources outwardYZSwitchPhysicalData} :=
  (outwardYZSwitchLeftPositiveEntry, outwardYZSwitchRightExpandedEntry)

theorem outwardYZSwitchSourcePair_mem_fourCell :
    outwardYZSwitchSourcePair ∈
      slabObservableFourCellSourcePairs outwardYZSwitchPhysicalData
        outwardYZSwitchRootFaceId outwardYZSwitchTargetFaceId := by
  apply (mem_cartesian_iff _ _ outwardYZSwitchSourcePair).mpr
  exact ⟨outwardYZSwitchLeftPositiveEntry_mem_rootTarget,
    outwardYZSwitchRightExpandedEntry_mem_rootComplementTargetComplement⟩

/-! ## 4. Map the geometric path into the physical support component -/

private theorem outwardYZFaceId_mem_incident
    {plaquette : Z4Plaq} {link : Z4Link}
    (hplaquette : plaquette ∈ outwardYZSwitchSurface)
    (hedge : link ∈ edgesOf plaquette) :
    slabFaceIdOfPlaquette 5 plaquette ∈ slabIncidentPlaqIds 5 link := by
  have hslab := outwardYZSwitchSurface_subset_slab_five _ hplaquette
  have hphysical := slabFaceIdOfPlaquette_physical hslab
  apply mem_slabIncidentPlaqIds.mpr
  refine ⟨plaquette, ?_, hedge⟩
  simpa only [slabPlaquetteAt_faceIdOfPlaquette hslab] using
    slabPlaquetteAt_mem_enumerate hphysical

private theorem outwardYZFaceId_mem_supportVertices
    {plaquette : Z4Plaq} (hplaquette : plaquette ∈ outwardYZSwitchSurface) :
    slabFaceIdOfPlaquette 5 plaquette ∈
      slabTwoReplicaSupportFaceVertices 5
        outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical := by
  have hslab := outwardYZSwitchSurface_subset_slab_five _ hplaquette
  apply mem_slabTwoReplicaSupportFaceVertices
    (slabFaceIdOfPlaquette_physical hslab)
  exact Or.inl (outwardYZSwitchFace_positive plaquette hplaquette)

private theorem outwardYZFaceIds_adjacent
    {left right : Z4Plaq}
    (hleft : left ∈ outwardYZSwitchSurface)
    (hright : right ∈ outwardYZSwitchSurface)
    (hadjacent : z4Chain.toLattice.Adjacent left right) :
    slabSupportFaceAdjacentB 5
      (slabFaceIdOfPlaquette 5 left)
      (slabFaceIdOfPlaquette 5 right) = true := by
  obtain ⟨link, honLeft, honRight⟩ := hadjacent
  have hedgeLeft : link ∈ edgesOf left := of_decide_eq_true honLeft
  have hedgeRight : link ∈ edgesOf right := of_decide_eq_true honRight
  apply slabSupportFaceAdjacentB_true_of_link
    ((mem_boundaryCompleteSlabLinks_iff 5 link).mpr
      ⟨left, outwardYZSwitchSurface_subset_slab_five left hleft,
        hedgeLeft⟩)
  · exact outwardYZFaceId_mem_incident hleft hedgeLeft
  · exact outwardYZFaceId_mem_incident hright hedgeRight

private def outwardYZChainEndpoint_mem_targetComponent :
    {first last : Z4Plaq} ->
    (hfirst : first ∈ outwardYZSwitchSurface) ->
    PolymerModel.ChainIn z4Chain.toLattice
      outwardYZSwitchSurface first last ->
    slabFaceIdOfPlaquette 5 first ∈
      slabTwoReplicaTargetSupportComponent 5
        outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical
        outwardYZSwitchTargetFaceId ->
    slabFaceIdOfPlaquette 5 last ∈
      slabTwoReplicaTargetSupportComponent 5
        outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical
        outwardYZSwitchTargetFaceId
  | _, _, _, .refl _, hcomponent => hcomponent
  | _, _, hfirst, .step hadjacent hnext rest, hcomponent =>
      outwardYZChainEndpoint_mem_targetComponent hnext rest
        (rootComponent_closed_under_edge
          (slabSupportFaceAdjacentB 5)
          (slabSupportFaceAdjacentB_symmetric 5)
          (outwardYZFaceId_mem_supportVertices outwardZQueryFace_mem_YZ)
          hcomponent
          (outwardYZFaceId_mem_supportVertices hnext)
          (outwardYZFaceIds_adjacent hfirst hnext hadjacent))

theorem outwardYZSwitchRoot_mem_targetSupportComponent :
    outwardYZSwitchRootFaceId ∈
      slabTwoReplicaTargetSupportComponent 5
        outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical
        outwardYZSwitchTargetFaceId := by
  have htargetComponent : outwardYZSwitchTargetFaceId ∈
      slabTwoReplicaTargetSupportComponent 5
        outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical
        outwardYZSwitchTargetFaceId := by
    unfold slabTwoReplicaTargetSupportComponent
    exact root_mem_rootComponent
      (slabSupportFaceAdjacentB 5)
      (outwardYZFaceId_mem_supportVertices outwardZQueryFace_mem_YZ)
  exact outwardYZChainEndpoint_mem_targetComponent
    outwardZQueryFace_mem_YZ
    (outwardYZSurface_connected
      outwardZQueryFace outwardYQueryFace
      outwardZQueryFace_mem_YZ outwardYQueryFace_mem_YZ)
    htargetComponent

theorem outwardYZSwitchSourcePair_connected :
    slabObservableTwoReplicaPairPairedSupportConnectedB
      outwardYZSwitchPhysicalData outwardYZSwitchRootFaceId
      outwardYZSwitchTargetFaceId outwardYZSwitchSourcePair = true := by
  unfold slabObservableTwoReplicaPairPairedSupportConnectedB
    slabObservableTwoReplicaPairPairedSupportSwapMask
    slabTwoReplicaSupportSwapMask outwardYZSwitchSourcePair
  rw [outwardYZSwitchLeftPositiveEntry_physical,
    outwardYZSwitchRightExpandedEntry_physical]
  change decide (outwardYZSwitchRootFaceId ∈
    slabTwoReplicaTargetSupportComponent 5
      outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical
      outwardYZSwitchTargetFaceId) = true
  exact decide_eq_true outwardYZSwitchRoot_mem_targetSupportComponent

/-! ## 5. The accepted connected source -/

theorem outwardYZSwitchSourcePair_mem_connectedFourCell :
    outwardYZSwitchSourcePair ∈
      slabObservablePairedSupportConnectedFourCellSourcePairs
        outwardYZSwitchPhysicalData outwardYZSwitchRootFaceId
        outwardYZSwitchTargetFaceId :=
  List.mem_filter.mpr
    ⟨outwardYZSwitchSourcePair_mem_fourCell,
      outwardYZSwitchSourcePair_connected⟩

def outwardYZSwitchConnectedStrandSource :
    {pair : SlabObservableTwoReplicaPair outwardYZSwitchPhysicalData
        outwardYZSwitchRootFaceId //
      pair ∈ slabObservablePairedSupportConnectedFourCellSourcePairs
        outwardYZSwitchPhysicalData outwardYZSwitchRootFaceId
        outwardYZSwitchTargetFaceId} :=
  ⟨outwardYZSwitchSourcePair,
    outwardYZSwitchSourcePair_mem_connectedFourCell⟩

#print axioms outwardYZSwitchLeftPhysicalTerm_pos
#print axioms outwardYZSwitchRightPhysicalTerm_pos
#print axioms outwardYZSwitchSourcePair_mem_fourCell
#print axioms outwardYZSwitchRoot_mem_targetSupportComponent
#print axioms outwardYZSwitchSourcePair_connected
#print axioms outwardYZSwitchConnectedStrandSource

end YMGap.Continuum.Z4OutwardYZEdgeTouchSlabConnectedSource
