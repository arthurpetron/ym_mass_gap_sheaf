/-
# A connected binary surface constructs an accepted slab source

Factor the common source construction away from any particular finite
surface.  A noduplicated even-incidence binary support in the extent-five
corrected slab, equipped with two retained plaquettes and a Type-valued path
between them, has a positive physical term at coupling one.  Positivity
constructively extracts accepted global fusion assignments for that support
and for the vacuum.  The marked path maps into the finite physical support
component, so the resulting literal `11 x 00` pair is an accepted connected
strand source.

Existence remains data-bearing throughout: the output contains the two
actual global auxiliary assignments.  This module is the reusable
geometry-to-source compiler needed by aligned cut carriers.

Constructive contract: positive finite summands, Sigma-valued witnesses, and
path recursion; no choice, `Classical`, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.BF4SU2OuterFineWitnessRoutingReduction
import YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
import YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
import YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
import YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedGeometry

namespace YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource

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
open YMGap.Continuum.Z4UnitCubeIncidenceParity

/-! ## 1. The exact geometric input -/

structure SlabBinarySupportConnectedCarrier : Type where
  support : List Z4Plaq
  rootPlaquette : Z4Plaq
  targetPlaquette : Z4Plaq
  support_subset_slab_five : forall plaquette, plaquette ∈ support ->
    plaquette ∈ boundaryCompleteSlabPlaquettes 5
  support_nodup : support.Nodup
  support_even : EvenFaceIncidence support
  root_mem : rootPlaquette ∈ support
  target_mem : targetPlaquette ∈ support
  support_connected : PolymerModel.connectedIn
    (L := z4Chain.toLattice) support

def binarySupportConnectedPhysicalData : SlabPhysicalData where
  coupling := 1
  coupling_nonnegative := by decide
  cutoff := 1
  half := 2

theorem binarySupportConnectedPhysicalData_extent :
    binarySupportConnectedPhysicalData.extent = 5 := rfl

namespace SlabBinarySupportConnectedCarrier

def leftPhysical (carrier : SlabBinarySupportConnectedCarrier) :
    SlabLabelling :=
  slabBinarySupportLabelling 5 carrier.support

def rightPhysical (_carrier : SlabBinarySupportConnectedCarrier) :
    SlabLabelling :=
  slabBinarySupportLabelling 5 []

def rootFaceId (carrier : SlabBinarySupportConnectedCarrier) : Nat :=
  slabFaceIdOfPlaquette 5 carrier.rootPlaquette

def targetFaceId (carrier : SlabBinarySupportConnectedCarrier) : Nat :=
  slabFaceIdOfPlaquette 5 carrier.targetPlaquette

theorem rootFaceId_physical (carrier : SlabBinarySupportConnectedCarrier) :
    carrier.rootFaceId ∈ slabPhysicalFaceEdges 5 :=
  slabFaceIdOfPlaquette_physical
    (carrier.support_subset_slab_five _ carrier.root_mem)

theorem targetFaceId_physical
    (carrier : SlabBinarySupportConnectedCarrier) :
    carrier.targetFaceId ∈ slabPhysicalFaceEdges 5 :=
  slabFaceIdOfPlaquette_physical
    (carrier.support_subset_slab_five _ carrier.target_mem)

/-! ## 2. Positive terms and accepted assignments -/

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
    (0 : Q') < binarySupportConnectedPhysicalData.physicalTerm
      (slabBinarySupportLabelling 5 support) := by
  have hbounded : SlabFaceLabellingBounded 1 5
      (slabBinarySupportLabelling 5 support) := by
    intro id _
    exact slabBinarySupportLabelling_le_one 5 support id
  have hface : (0 : Q') < slabParametricKPhysicalFaceFactor
      binarySupportConnectedPhysicalData.coupling
      binarySupportConnectedPhysicalData.cutoff
      binarySupportConnectedPhysicalData.extent
      (slabBinarySupportLabelling 5 support) :=
    slabParametricKPhysicalFaceFactor_pos_of_bounded
      binarySupportConnectedPhysicalData (by decide)
      (slabBinarySupportLabelling 5 support) hbounded
  have hlinks : 0 < slabExplicitLinkMultiplicityProduct 1 5
      (slabBinarySupportLabelling 5 support) :=
    slabBinarySupport_linkMultiplicityProduct_pos
      (by omega) hsubset hnodup heven
  unfold SlabPhysicalData.physicalTerm slabParametricKPhysicalTerm
  exact Q'.mul_pos hface (qOfNat_pos_of_pos hlinks)

theorem leftPhysicalTerm_pos
    (carrier : SlabBinarySupportConnectedCarrier) :
    (0 : Q') < binarySupportConnectedPhysicalData.physicalTerm
      carrier.leftPhysical := by
  unfold leftPhysical
  exact binarySupportPhysicalTerm_pos carrier.support
    carrier.support_subset_slab_five carrier.support_nodup
    carrier.support_even

theorem rightPhysicalTerm_pos
    (carrier : SlabBinarySupportConnectedCarrier) :
    (0 : Q') < binarySupportConnectedPhysicalData.physicalTerm
      carrier.rightPhysical := by
  unfold rightPhysical
  exact binarySupportPhysicalTerm_pos []
    (fun plaquette hmem => False.elim (List.not_mem_nil hmem))
    List.nodup_nil (fun _ => rfl)

def leftFineWitness (carrier : SlabBinarySupportConnectedCarrier) :
    Σ' witness : SlabFusionWitnessAssignment,
      witness ∈ slabFineFusionWitnesses
        binarySupportConnectedPhysicalData carrier.leftPhysical :=
  positivePhysicalTermFineFusionWitness
    binarySupportConnectedPhysicalData carrier.leftPhysical
    carrier.leftPhysicalTerm_pos

def rightFineWitness (carrier : SlabBinarySupportConnectedCarrier) :
    Σ' witness : SlabFusionWitnessAssignment,
      witness ∈ slabFineFusionWitnesses
        binarySupportConnectedPhysicalData carrier.rightPhysical :=
  positivePhysicalTermFineFusionWitness
    binarySupportConnectedPhysicalData carrier.rightPhysical
    carrier.rightPhysicalTerm_pos

/-! ## 3. Literal `11 x 00` source pair -/

theorem face_positive (carrier : SlabBinarySupportConnectedCarrier)
    (plaquette : Z4Plaq) (hplaquette : plaquette ∈ carrier.support) :
    0 < carrier.leftPhysical
      (slabFaceIdOfPlaquette 5 plaquette) := by
  have hslab := carrier.support_subset_slab_five plaquette hplaquette
  have hphysical := slabFaceIdOfPlaquette_physical hslab
  unfold leftPhysical
  rw [slabBinarySupportLabelling_eq_indicator hphysical,
    slabPlaquetteAt_faceIdOfPlaquette hslab, if_pos hplaquette]
  omega

theorem rightPhysical_zero (carrier : SlabBinarySupportConnectedCarrier)
    (faceId : Nat) : carrier.rightPhysical faceId = 0 := by
  unfold rightPhysical slabBinarySupportLabelling
  split <;> simp

theorem leftPhysical_mem (carrier : SlabBinarySupportConnectedCarrier) :
    carrier.leftPhysical ∈
      binarySupportConnectedPhysicalData.physicalLabellings := by
  unfold SlabPhysicalData.physicalLabellings SlabPhysicalData.faceEdges
    leftPhysical
  change slabBinarySupportLabelling 5 carrier.support ∈
    boundedEdgeLabellings 1 (slabPhysicalFaceEdges 5)
  exact slabBinarySupportLabelling_mem (by omega) carrier.support

theorem rightPhysical_mem (carrier : SlabBinarySupportConnectedCarrier) :
    carrier.rightPhysical ∈
      binarySupportConnectedPhysicalData.physicalLabellings := by
  unfold SlabPhysicalData.physicalLabellings SlabPhysicalData.faceEdges
    rightPhysical
  change slabBinarySupportLabelling 5 [] ∈
    boundedEdgeLabellings 1 (slabPhysicalFaceEdges 5)
  exact slabBinarySupportLabelling_mem (by omega) []

def leftPositiveEntry (carrier : SlabBinarySupportConnectedCarrier) :
    {source : SlabLabelling × SlabFusionWitnessAssignment //
      source ∈ slabObservablePositiveExpandedSources
        binarySupportConnectedPhysicalData carrier.rootFaceId} :=
  slabObservablePositiveSourceEntryOfCarrier
    binarySupportConnectedPhysicalData carrier.rootFaceId
    carrier.leftPhysical carrier.leftPhysical_mem
    carrier.leftFineWitness.1 carrier.leftFineWitness.2
    (carrier.face_positive carrier.rootPlaquette carrier.root_mem)

def rightExpandedEntry (carrier : SlabBinarySupportConnectedCarrier) :
    {source : SlabLabelling × SlabFusionWitnessAssignment //
      source ∈ slabExpandedFineSources binarySupportConnectedPhysicalData} :=
  slabExpandedFineSourceEntryOfCarrier
    binarySupportConnectedPhysicalData carrier.rightPhysical
    carrier.rightPhysical_mem
    carrier.rightFineWitness.1 carrier.rightFineWitness.2

@[simp] theorem leftPositiveEntry_physical
    (carrier : SlabBinarySupportConnectedCarrier) :
    carrier.leftPositiveEntry.1.1 = carrier.leftPhysical := by
  unfold leftPositiveEntry
  apply slabObservablePositiveSourceEntryOfCarrier_physical

@[simp] theorem rightExpandedEntry_physical
    (carrier : SlabBinarySupportConnectedCarrier) :
    carrier.rightExpandedEntry.1.1 = carrier.rightPhysical := by
  unfold rightExpandedEntry
  apply slabExpandedFineSourceEntryOfCarrier_physical

theorem leftPositiveEntry_mem_rootTarget
    (carrier : SlabBinarySupportConnectedCarrier) :
    carrier.leftPositiveEntry ∈
      slabObservableRootTargetEntries binarySupportConnectedPhysicalData
        carrier.rootFaceId carrier.targetFaceId := by
  apply List.mem_filter.mpr
  refine ⟨List.mem_attach _ carrier.leftPositiveEntry, ?_⟩
  unfold SlabObservablePositiveSourceEntry.facePositiveB
  rw [carrier.leftPositiveEntry_physical]
  exact decide_eq_true
    (carrier.face_positive carrier.targetPlaquette carrier.target_mem)

theorem rightExpandedEntry_mem_rootComplementTargetComplement
    (carrier : SlabBinarySupportConnectedCarrier) :
    carrier.rightExpandedEntry ∈
      slabObservableRootComplementTargetComplementEntries
        binarySupportConnectedPhysicalData carrier.rootFaceId
          carrier.targetFaceId := by
  apply List.mem_filter.mpr
  refine ⟨List.mem_attach _ carrier.rightExpandedEntry, ?_⟩
  unfold SlabExpandedFineSourceEntry.facePositiveB
  rw [carrier.rightExpandedEntry_physical,
    carrier.rightPhysical_zero, carrier.rightPhysical_zero]
  rfl

def sourcePair (carrier : SlabBinarySupportConnectedCarrier) :
    ({source : SlabLabelling × SlabFusionWitnessAssignment //
        source ∈ slabObservablePositiveExpandedSources
          binarySupportConnectedPhysicalData carrier.rootFaceId}) ×
      {source : SlabLabelling × SlabFusionWitnessAssignment //
        source ∈ slabExpandedFineSources
          binarySupportConnectedPhysicalData} :=
  (carrier.leftPositiveEntry, carrier.rightExpandedEntry)

theorem sourcePair_mem_fourCell
    (carrier : SlabBinarySupportConnectedCarrier) :
    carrier.sourcePair ∈
      slabObservableFourCellSourcePairs binarySupportConnectedPhysicalData
        carrier.rootFaceId carrier.targetFaceId := by
  apply (mem_cartesian_iff _ _ carrier.sourcePair).mpr
  exact ⟨carrier.leftPositiveEntry_mem_rootTarget,
    carrier.rightExpandedEntry_mem_rootComplementTargetComplement⟩

/-! ## 4. Map the retained geometric path into physical support -/

private theorem faceId_mem_incident
    (carrier : SlabBinarySupportConnectedCarrier)
    {plaquette : Z4Plaq} {link : Z4Link}
    (hplaquette : plaquette ∈ carrier.support)
    (hedge : link ∈ edgesOf plaquette) :
    slabFaceIdOfPlaquette 5 plaquette ∈ slabIncidentPlaqIds 5 link := by
  have hslab := carrier.support_subset_slab_five _ hplaquette
  have hphysical := slabFaceIdOfPlaquette_physical hslab
  apply mem_slabIncidentPlaqIds.mpr
  refine ⟨plaquette, ?_, hedge⟩
  simpa only [slabPlaquetteAt_faceIdOfPlaquette hslab] using
    slabPlaquetteAt_mem_enumerate hphysical

private theorem faceId_mem_supportVertices
    (carrier : SlabBinarySupportConnectedCarrier)
    {plaquette : Z4Plaq} (hplaquette : plaquette ∈ carrier.support) :
    slabFaceIdOfPlaquette 5 plaquette ∈
      slabTwoReplicaSupportFaceVertices 5
        carrier.leftPhysical carrier.rightPhysical := by
  have hslab := carrier.support_subset_slab_five _ hplaquette
  apply mem_slabTwoReplicaSupportFaceVertices
    (slabFaceIdOfPlaquette_physical hslab)
  exact Or.inl (carrier.face_positive plaquette hplaquette)

private theorem faceIds_adjacent
    (carrier : SlabBinarySupportConnectedCarrier)
    {left right : Z4Plaq}
    (hleft : left ∈ carrier.support)
    (hright : right ∈ carrier.support)
    (hadjacent : z4Chain.toLattice.Adjacent left right) :
    slabSupportFaceAdjacentB 5
      (slabFaceIdOfPlaquette 5 left)
      (slabFaceIdOfPlaquette 5 right) = true := by
  obtain ⟨link, honLeft, honRight⟩ := hadjacent
  have hedgeLeft : link ∈ edgesOf left := of_decide_eq_true honLeft
  have hedgeRight : link ∈ edgesOf right := of_decide_eq_true honRight
  apply slabSupportFaceAdjacentB_true_of_link
    ((mem_boundaryCompleteSlabLinks_iff 5 link).mpr
      ⟨left, carrier.support_subset_slab_five left hleft, hedgeLeft⟩)
  · exact carrier.faceId_mem_incident hleft hedgeLeft
  · exact carrier.faceId_mem_incident hright hedgeRight

private def chainEndpoint_mem_targetComponent
    (carrier : SlabBinarySupportConnectedCarrier) :
    {first last : Z4Plaq} ->
    (hfirst : first ∈ carrier.support) ->
    PolymerModel.ChainIn z4Chain.toLattice carrier.support first last ->
    slabFaceIdOfPlaquette 5 first ∈
      slabTwoReplicaTargetSupportComponent 5
        carrier.leftPhysical carrier.rightPhysical carrier.targetFaceId ->
    slabFaceIdOfPlaquette 5 last ∈
      slabTwoReplicaTargetSupportComponent 5
        carrier.leftPhysical carrier.rightPhysical carrier.targetFaceId
  | _, _, _, .refl _, hcomponent => hcomponent
  | _, _, hfirst, .step hadjacent hnext rest, hcomponent =>
      carrier.chainEndpoint_mem_targetComponent hnext rest
        (rootComponent_closed_under_edge
          (slabSupportFaceAdjacentB 5)
          (slabSupportFaceAdjacentB_symmetric 5)
          (carrier.faceId_mem_supportVertices carrier.target_mem)
          hcomponent
          (carrier.faceId_mem_supportVertices hnext)
          (carrier.faceIds_adjacent hfirst hnext hadjacent))

theorem root_mem_targetSupportComponent
    (carrier : SlabBinarySupportConnectedCarrier) :
    carrier.rootFaceId ∈
      slabTwoReplicaTargetSupportComponent 5
        carrier.leftPhysical carrier.rightPhysical carrier.targetFaceId := by
  have htargetComponent : carrier.targetFaceId ∈
      slabTwoReplicaTargetSupportComponent 5
        carrier.leftPhysical carrier.rightPhysical carrier.targetFaceId := by
    unfold slabTwoReplicaTargetSupportComponent
    exact root_mem_rootComponent
      (slabSupportFaceAdjacentB 5)
      (carrier.faceId_mem_supportVertices carrier.target_mem)
  exact carrier.chainEndpoint_mem_targetComponent carrier.target_mem
    (carrier.support_connected carrier.targetPlaquette carrier.rootPlaquette
      carrier.target_mem carrier.root_mem)
    htargetComponent

theorem sourcePair_connected
    (carrier : SlabBinarySupportConnectedCarrier) :
    slabObservableTwoReplicaPairPairedSupportConnectedB
      binarySupportConnectedPhysicalData carrier.rootFaceId
      carrier.targetFaceId carrier.sourcePair = true := by
  unfold slabObservableTwoReplicaPairPairedSupportConnectedB
    slabObservableTwoReplicaPairPairedSupportSwapMask
    slabTwoReplicaSupportSwapMask sourcePair
  rw [carrier.leftPositiveEntry_physical,
    carrier.rightExpandedEntry_physical]
  change decide (carrier.rootFaceId ∈
    slabTwoReplicaTargetSupportComponent 5
      carrier.leftPhysical carrier.rightPhysical carrier.targetFaceId) = true
  exact decide_eq_true carrier.root_mem_targetSupportComponent

/-! ## 5. The accepted connected source -/

theorem sourcePair_mem_connectedFourCell
    (carrier : SlabBinarySupportConnectedCarrier) :
    carrier.sourcePair ∈
      slabObservablePairedSupportConnectedFourCellSourcePairs
        binarySupportConnectedPhysicalData carrier.rootFaceId
          carrier.targetFaceId :=
  List.mem_filter.mpr
    ⟨carrier.sourcePair_mem_fourCell, carrier.sourcePair_connected⟩

def connectedStrandSource
    (carrier : SlabBinarySupportConnectedCarrier) :
    {pair : SlabObservableTwoReplicaPair
        binarySupportConnectedPhysicalData carrier.rootFaceId //
      pair ∈ slabObservablePairedSupportConnectedFourCellSourcePairs
        binarySupportConnectedPhysicalData carrier.rootFaceId
          carrier.targetFaceId} :=
  ⟨carrier.sourcePair, carrier.sourcePair_mem_connectedFourCell⟩

#print axioms leftPhysicalTerm_pos
#print axioms rightPhysicalTerm_pos
#print axioms sourcePair_mem_fourCell
#print axioms root_mem_targetSupportComponent
#print axioms sourcePair_connected
#print axioms connectedStrandSource

end SlabBinarySupportConnectedCarrier

end YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource
