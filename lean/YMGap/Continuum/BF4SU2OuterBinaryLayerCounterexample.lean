/-
# A positive-row obstruction to the SU(2) binary-layer input

The ordinary set union of two adjacent cube boundaries contains eleven
faces.  Give every one of those faces twice-spin label two.  Every touched
link then carries either two or three copies of label two, so its SU(2)
invariant multiplicity is positive.  Nevertheless a decomposition into at
most two binary layers is impossible: every supported face has label two,
forcing both layers to contain the whole eleven-face union, whose displayed
interface link has incidence three.

This module first proves the decomposition obstruction.  The remaining
section verifies that the literal corrected-slab spin-foam summand is
strictly positive, so the obstruction applies to the proposed
`SU2OuterBinaryLayerDecomposition` input itself.

## Axiom gate

Finite `Nat`/`List` computation and exact `Q'` order only.  No
`Classical.*`, `sorry`, `native_decide`, custom axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4SU2OuterBinaryLayerReduction
import YMGap.Continuum.BF4SU2OuterRawKernelCutoffDiagnostics
import YMGap.Continuum.CompactDualAllCutoffOddParitySlabLayer
import YMGap.Continuum.Z4AdjacentCubeCancellationCarrier
import YMGap.Continuum.Z4AxisCubeSixFaceActivity
import YMGap.Continuum.Z4FusionPathZeroInsertion
import YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier
import YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand

namespace YMGap.Continuum.BF4SU2OuterBinaryLayerCounterexample

set_option maxRecDepth 100000
set_option maxHeartbeats 100000

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4SU2OuterBinaryLayerReduction
open YMGap.Continuum.BF4SU2OuterCutoffBlockGramContract
open YMGap.Continuum.BF4SU2OuterPhysicalMarkovKernelFrontier
open YMGap.Continuum.BF4SU2OuterRawKernelCutoffDiagnostics
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualAllCutoffOddParitySlabLayer
open YMGap.Continuum.CompactDualCutoffOnePositivePhysicalClosure
open YMGap.Continuum.CompactDualCutoffOneParitySlabTarget
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FusionSupportAddition
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4AdjacentCubeCancellationCarrier
open YMGap.Continuum.Z4AxisCubeSixFaceActivity
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand

/-! ## 1. Literal extent-three corrected-slab source -/

def counterGeometry : CutoffOneGeometry where
  coarseHalf := 0

def counterScalePair : SlabScalePair :=
  su2OuterScalePair counterGeometry 1 (by decide) 1 (by decide) 2

theorem counterScalePair_fine_extent :
    counterScalePair.fine.extent = 3 := rfl

def plainUnionIndicator : EdgeLabelling :=
  slabBinarySupportLabelling 3 zeroXAxisPlainUnionSurface

def plainUnionSpinTwoState : EdgeLabelling :=
  addEdgeLabelling plainUnionIndicator plainUnionIndicator

theorem zeroXAxisPlainUnionSurface_eq_literal :
    zeroXAxisPlainUnionSurface =
      [((0, 0, 0, 0), .p01), ((0, 0, 1, 0), .p01),
       ((0, 0, 0, 0), .p02), ((0, 1, 0, 0), .p02),
       ((0, 0, 0, 0), .p12), ((1, 0, 0, 0), .p12),
       ((1, 0, 0, 0), .p01), ((1, 0, 1, 0), .p01),
       ((1, 0, 0, 0), .p02), ((1, 1, 0, 0), .p02),
       ((2, 0, 0, 0), .p12)] := by
  decide

theorem zeroXAxisPlainUnionSurface_nodup :
    zeroXAxisPlainUnionSurface.Nodup := by
  rw [zeroXAxisPlainUnionSurface_eq_literal]
  decide

theorem zeroXAxisPlainUnionSurface_subset_slab_three :
    ∀ plaquette, plaquette ∈ zeroXAxisPlainUnionSurface →
      plaquette ∈ boundaryCompleteSlabPlaquettes 3 := by
  intro plaquette hplaquette
  rw [zeroXAxisPlainUnionSurface_eq_literal] at hplaquette
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hplaquette
  rcases hplaquette with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem plainUnionIndicator_mem_cutoff_one :
    plainUnionIndicator ∈
      boundedEdgeLabellings 1 (slabPhysicalFaceEdges 3) := by
  exact slabBinarySupportLabelling_mem
    (by decide) zeroXAxisPlainUnionSurface

theorem plainUnionSpinTwoState_mem :
    plainUnionSpinTwoState ∈
      counterScalePair.fine.physicalLabellings := by
  change plainUnionSpinTwoState ∈
    boundedEdgeLabellings 2 (slabPhysicalFaceEdges 3)
  exact addEdgeLabelling_mem_bounded
    (leftCutoff := 1) (rightCutoff := 1)
    (left := plainUnionIndicator) (right := plainUnionIndicator)
    (slabPhysicalFaceEdges 3)
    plainUnionIndicator_mem_cutoff_one
    plainUnionIndicator_mem_cutoff_one

def leftCubeIndicator : EdgeLabelling :=
  slabBinarySupportLabelling 3
    (axisCubeSurface zeroAxisOffset)

def rightCubeIndicator : EdgeLabelling :=
  slabBinarySupportLabelling 3
    (axisCubeSurface xAxisOffset)

def cancelledIndicator : EdgeLabelling :=
  slabBinarySupportLabelling 3
    zeroXAxisCancelledSurface

private theorem leftCube_subset_slab_three :
    ∀ plaquette, plaquette ∈ axisCubeSurface zeroAxisOffset →
      plaquette ∈ boundaryCompleteSlabPlaquettes 3 := by
  intro plaquette hplaquette
  apply zeroXAxisPlainUnionSurface_subset_slab_three plaquette
  unfold zeroXAxisPlainUnionSurface
  simp only [List.mem_eraseDups, List.mem_append]
  exact Or.inl hplaquette

private theorem rightCube_subset_slab_three :
    ∀ plaquette, plaquette ∈ axisCubeSurface xAxisOffset →
      plaquette ∈ boundaryCompleteSlabPlaquettes 3 := by
  intro plaquette hplaquette
  apply zeroXAxisPlainUnionSurface_subset_slab_three plaquette
  unfold zeroXAxisPlainUnionSurface
  simp only [List.mem_eraseDups, List.mem_append]
  exact Or.inr hplaquette

private theorem cancelledSurface_subset_slab_three :
    ∀ plaquette, plaquette ∈ zeroXAxisCancelledSurface →
      plaquette ∈ boundaryCompleteSlabPlaquettes 3 := by
  intro plaquette hplaquette
  apply zeroXAxisPlainUnionSurface_subset_slab_three plaquette
  unfold zeroXAxisPlainUnionSurface
  simp only [List.mem_eraseDups, List.mem_append]
  exact List.mem_append.mp (List.mem_filter.mp hplaquette).1

private theorem leftCube_linkProduct_pos :
    0 < slabExplicitLinkMultiplicityProduct
      1 3 leftCubeIndicator := by
  apply slabBinarySupport_linkMultiplicityProduct_pos
  · decide
  · exact leftCube_subset_slab_three
  · exact axisCubeSurface_nodup zeroAxisOffset
  · exact axisShift_evenFaceIncidence
      zeroAxisOffset unitCubeSurface_evenFaceIncidence

private theorem rightCube_linkProduct_pos :
    0 < slabExplicitLinkMultiplicityProduct
      1 3 rightCubeIndicator := by
  apply slabBinarySupport_linkMultiplicityProduct_pos
  · decide
  · exact rightCube_subset_slab_three
  · exact axisCubeSurface_nodup xAxisOffset
  · exact axisShift_evenFaceIncidence
      xAxisOffset unitCubeSurface_evenFaceIncidence

private theorem cancelledIndicator_linkProduct_pos :
    0 < slabExplicitLinkMultiplicityProduct
      1 3 cancelledIndicator := by
  apply slabBinarySupport_linkMultiplicityProduct_pos
  · decide
  · exact cancelledSurface_subset_slab_three
  · exact zeroXAxisCancelledSurface_nodup
  · exact zeroXAxisCancelledSurface_evenFaceIncidence

/-- Exact pointwise carrier identity
`2·(A ∪ B) = A + B + (A △ B)` for the two adjacent cube boundaries. -/
theorem threeSheetCarrier_eq_plainUnionSpinTwoState :
    addEdgeLabelling
        (addEdgeLabelling leftCubeIndicator rightCubeIndicator)
        cancelledIndicator =
      plainUnionSpinTwoState := by
  funext id
  unfold leftCubeIndicator rightCubeIndicator cancelledIndicator
    plainUnionSpinTwoState plainUnionIndicator addEdgeLabelling
    slabBinarySupportLabelling
  by_cases hphysical : id ∈ slabPhysicalFaceEdges 3
  · by_cases hleft :
        slabPlaquetteAt 3 id ∈ axisCubeSurface zeroAxisOffset
    · by_cases hright :
          slabPlaquetteAt 3 id ∈ axisCubeSurface xAxisOffset
      · simp [zeroXAxisPlainUnionSurface,
          zeroXAxisCancelledSurface, hleft, hright]
      · simp [zeroXAxisPlainUnionSurface,
          zeroXAxisCancelledSurface, hleft, hright]
    · by_cases hright :
          slabPlaquetteAt 3 id ∈ axisCubeSurface xAxisOffset
      · simp [zeroXAxisPlainUnionSurface,
          zeroXAxisCancelledSurface, hleft, hright]
      · simp [zeroXAxisPlainUnionSurface,
          zeroXAxisCancelledSurface, hleft, hright]
  · rw [if_neg hphysical, if_neg hphysical, if_neg hphysical,
      if_neg hphysical]

/-- Structural production certificate.  Each of the two cube boundaries and
their symmetric difference is an even binary sheet, so their sum has
positive cutoff-three link product.  The exact carrier identity above and
cutoff independence for a cutoff-two-bounded source transport that
certificate to the physical cutoff two. -/
theorem plainUnionSpinTwoState_linkProduct_pos :
    0 < slabExplicitLinkMultiplicityProduct
      2 3 plainUnionSpinTwoState := by
  have htwo :
      0 < slabExplicitLinkMultiplicityProduct
        (1 + 1) 3
        (addEdgeLabelling leftCubeIndicator rightCubeIndicator) :=
    slabExplicitLinkMultiplicityProduct_add_pos
      leftCube_linkProduct_pos rightCube_linkProduct_pos
  have hthree :
      0 < slabExplicitLinkMultiplicityProduct
        ((1 + 1) + 1) 3
        (addEdgeLabelling
          (addEdgeLabelling leftCubeIndicator rightCubeIndicator)
          cancelledIndicator) :=
    slabExplicitLinkMultiplicityProduct_add_pos
      htwo cancelledIndicator_linkProduct_pos
  rw [threeSheetCarrier_eq_plainUnionSpinTwoState] at hthree
  have hbounded :
      SlabFaceLabellingBounded
        2 3 plainUnionSpinTwoState := by
    exact slabFaceLabellingBounded_of_physical
      plainUnionSpinTwoState_mem
  have hstable :=
    slabExplicitLinkMultiplicityProduct_cutoff_stable
      (K := 2) (L := 3) (extent := 3)
      (physical := plainUnionSpinTwoState)
      (by omega) hbounded
  rw [hstable] at hthree
  exact hthree

private theorem eliminateLinks_pos_local
    (value : Nat → Q') (hvalue : ∀ id, (0 : Q') < value id) :
    ∀ ids : List Nat, (0 : Q') < eliminateLinks value ids
  | [] => by
      show (0 : Q') < 1
      decide
  | head :: tail =>
      Q'.mul_pos (hvalue head)
        (eliminateLinks_pos_local value hvalue tail)

theorem plainUnionSpinTwoState_faceFactor_pos :
    (0 : Q') <
      slabParametricKPhysicalFaceFactor
        1 2 3 plainUnionSpinTwoState := by
  unfold slabParametricKPhysicalFaceFactor
  apply eliminateLinks_pos_local
  intro id
  have hspin : plainUnionSpinTwoState id < 2 + 1 := by
    unfold plainUnionSpinTwoState plainUnionIndicator addEdgeLabelling
    have hleft :=
      slabBinarySupportLabelling_le_one
        3 zeroXAxisPlainUnionSurface id
    omega
  rw [coeffAt_heatKernelPacket hspin]
  exact
    YMGap.Continuum.FusionResidualBound.coeffW_pos
      (by decide) (plainUnionSpinTwoState id)

private theorem qOfNat_pos_of_pos
    (value : Nat) (hvalue : 0 < value) :
    (0 : Q') < Q'.ofNat value := by
  show (0 : Int) * ((Q'.ofNat value).den : Int) <
    (Q'.ofNat value).num * (1 : Int)
  rw [Int.zero_mul, Q'.ofNat_num_cast, Int.mul_one]
  exact Int.ofNat_lt.mpr hvalue

/-- The counterexample is not a merely combinatorial state: its exact
corrected-slab heat-kernel face factor and every link multiplicity are
strictly positive, hence its full physical spin-foam summand is positive. -/
theorem plainUnionSpinTwoState_physicalTerm_pos :
    (0 : Q') <
      counterScalePair.fine.physicalTerm
        plainUnionSpinTwoState := by
  change
    (0 : Q') <
      slabParametricKPhysicalFaceFactor
          1 2 3 plainUnionSpinTwoState *
        Q'.ofNat
          (slabExplicitLinkMultiplicityProduct
            2 3 plainUnionSpinTwoState)
  exact Q'.mul_pos
    plainUnionSpinTwoState_faceFactor_pos
    (qOfNat_pos_of_pos _
      plainUnionSpinTwoState_linkProduct_pos)

def sharedInterfaceFaceId : Nat := 339

theorem sharedInterfaceFaceId_mem :
    sharedInterfaceFaceId ∈ slabPhysicalFaceEdges 3 := by
  decide

theorem sharedInterfaceFaceId_lookup :
    slabPlaquetteAt 3 sharedInterfaceFaceId =
      zeroXAxisSharedInterfaceFace := by
  decide

theorem plainUnionSpinTwoState_sharedInterface :
    plainUnionSpinTwoState sharedInterfaceFaceId = 2 := by
  unfold plainUnionSpinTwoState plainUnionIndicator addEdgeLabelling
  unfold slabBinarySupportLabelling
  rw [sharedInterfaceFaceId_lookup]
  simp [zeroXAxisSharedInterfaceFace_mem_plainUnion,
    sharedInterfaceFaceId_mem]

/-! ## 2. Two forced layers would both equal the odd plain union -/

private theorem layer_eq_plainUnionIndicator
    {left right : BinaryEvenSlabLayer counterScalePair}
    (hsum :
      addEdgeLabelling left.state right.state =
        plainUnionSpinTwoState) :
    left.state = plainUnionIndicator := by
  have hleft :=
    boundedEdgeLabellings_sound 1
      (slabPhysicalFaceEdges 3) left.state left.state_mem
  have hright :=
    boundedEdgeLabellings_sound 1
      (slabPhysicalFaceEdges 3) right.state right.state_mem
  funext id
  by_cases hid : id ∈ slabPhysicalFaceEdges 3
  · have heq := congrFun hsum id
    unfold plainUnionSpinTwoState addEdgeLabelling at heq
    unfold plainUnionIndicator at heq ⊢
    unfold slabBinarySupportLabelling at heq
    rw [slabBinarySupportLabelling_eq_indicator hid]
    by_cases hsupport :
        slabPlaquetteAt 3 id ∈ zeroXAxisPlainUnionSurface
    · simp [hsupport, hid] at heq ⊢
      have hl := hleft.1 id hid
      have hr := hright.1 id hid
      omega
    · simp [hsupport, hid] at heq ⊢
      omega
  · rw [hleft.2 id hid,
      show plainUnionIndicator id = 0 by
        unfold plainUnionIndicator
        exact slabBinarySupportLabelling_eq_zero_of_not_physical hid]

private theorem plainUnionIndicator_not_even_layer
    (layer : BinaryEvenSlabLayer counterScalePair)
    (hlayer : layer.state = plainUnionIndicator) : False := by
  have hstate :=
    cutoffOneFineState_eq_oddSupportLabelling
      (S := binaryScalePair counterScalePair)
      rfl layer.state_mem
  rw [binaryScalePair_fine_extent,
    counterScalePair_fine_extent] at hstate
  have hodd :=
    slabBinarySupport_localExternalSpinSum
      (fun _ hmem => fineOddSlabSupport_subset hmem)
      (fineOddSlabSupport_nodup
        (binaryScalePair counterScalePair) layer.state)
      zeroXAxisInterfaceBoundaryLink
  rw [binaryScalePair_fine_extent,
    counterScalePair_fine_extent] at hodd
  rw [← hstate, hlayer] at hodd
  have hplain :=
    slabBinarySupport_localExternalSpinSum
      zeroXAxisPlainUnionSurface_subset_slab_three
      zeroXAxisPlainUnionSurface_nodup
      zeroXAxisInterfaceBoundaryLink
  have hincidence :=
    Eq.trans hodd.symm
      (Eq.trans hplain
        zeroXAxisPlainUnion_interface_incidence_three)
  have heven :=
    layer.oddSupport_even zeroXAxisInterfaceBoundaryLink
  rw [hlayer] at heven
  rw [hincidence] at heven
  cases heven

/-- The doubled adjacent-cube state has no decomposition into at most two
globally even cutoff-one slab layers. -/
theorem plainUnionSpinTwoState_no_binary_decomposition :
    BinaryEvenSlabDecomposition
      counterScalePair plainUnionSpinTwoState → False := by
  intro decomposition
  cases hlayers : decomposition.layers with
  | nil =>
      have hpoint :=
        congrFun decomposition.reconstruct sharedInterfaceFaceId
      rw [hlayers] at hpoint
      simp only [sumLayerStates] at hpoint
      rw [plainUnionSpinTwoState_sharedInterface] at hpoint
      cases hpoint
  | cons first rest =>
      cases rest with
      | nil =>
          have hpoint :=
            congrFun decomposition.reconstruct sharedInterfaceFaceId
          rw [hlayers] at hpoint
          simp only [sumLayerStates, addEdgeLabelling,
            zeroEdgeLabelling, Nat.add_zero] at hpoint
          have hbound :=
            (boundedEdgeLabellings_sound 1
              (slabPhysicalFaceEdges 3)
              first.state first.state_mem).1
              sharedInterfaceFaceId sharedInterfaceFaceId_mem
          rw [plainUnionSpinTwoState_sharedInterface] at hpoint
          omega
      | cons second tail =>
          cases tail with
          | nil =>
              have hsum :
                  addEdgeLabelling first.state second.state =
                    plainUnionSpinTwoState := by
                have hrec := decomposition.reconstruct
                rw [hlayers] at hrec
                simpa only [sumLayerStates, addEdgeLabelling,
                  zeroEdgeLabelling, Nat.add_zero] using
                  hrec
              exact plainUnionIndicator_not_even_layer first
                (layer_eq_plainUnionIndicator hsum)
          | cons third tail =>
              have hcount := decomposition.layer_count_le_cutoff
              rw [hlayers] at hcount
              simp only [List.length_cons] at hcount
              dsimp [counterScalePair, su2OuterScalePair,
                su2FineOuterData] at hcount
              omega

/-- The advertised all-positive-row binary-sheet input is inconsistent
already at cutoff two on the literal extent-three corrected slab. -/
theorem no_SU2OuterBinaryLayerDecomposition :
    SU2OuterBinaryLayerDecomposition
      counterGeometry 1 (by decide) 1 (by decide) → False := by
  intro layers
  exact plainUnionSpinTwoState_no_binary_decomposition
    (layers.decompose
      2 plainUnionSpinTwoState
      (by decide)
      plainUnionSpinTwoState_mem
      plainUnionSpinTwoState_physicalTerm_pos)

#print axioms counterScalePair
#print axioms zeroXAxisPlainUnionSurface_subset_slab_three
#print axioms plainUnionSpinTwoState_mem
#print axioms threeSheetCarrier_eq_plainUnionSpinTwoState
#print axioms plainUnionSpinTwoState_linkProduct_pos
#print axioms plainUnionSpinTwoState_faceFactor_pos
#print axioms plainUnionSpinTwoState_physicalTerm_pos
#print axioms plainUnionSpinTwoState_no_binary_decomposition
#print axioms no_SU2OuterBinaryLayerDecomposition

end YMGap.Continuum.BF4SU2OuterBinaryLayerCounterexample
