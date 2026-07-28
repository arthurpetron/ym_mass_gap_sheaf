/-
# Binary-layer reduction for the SU(2) outer positive row

An arbitrary twice-spin face field can be viewed as a finite sum of binary
sheet fields only when those sheets can be chosen globally compatible at
every fine link.  This module records that condition as explicit `Type` data.
Each layer is a cutoff-one physical slab state whose odd support has even
incidence, and a decomposition carries the pointwise natural-number sum
identity back to the original higher-cutoff state.

The cutoff-one cellular theorem supplies one coherent coarse parity target
per layer.  The additive closure of SU(2) fusion support then merges their
link intertwiners.  The remaining face calculation is finite: binary parity
channels add componentwise, and `fusionOK_add` shows that the sum channel is
admissible for the summed four-spin packet.

Thus a binary-layer decomposition constructs the exact
`WholeSlabJointChannelSelection` required by the outer raw kernel.  The
module does not assert that every positive higher-spin row has such a
decomposition; that is isolated at the end as a strictly geometric,
Type-valued layer-decomposition input.

## Axiom gate

Finite `Nat`/`List` recursion and exact `Q'` order only.  No `Classical.*`,
`sorry`, `native_decide`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4SU2OuterFineWitnessRoutingReduction
import YMGap.Continuum.BF4SU2OuterRawKernelCutoffDiagnostics
import YMGap.Continuum.CompactDualCutoffOneParitySlabTarget
import YMGap.Continuum.SU2FusionSupportAddition
import YMGap.Continuum.Z4ValenceFusionCutoffIndependence

namespace YMGap.Continuum.BF4SU2OuterBinaryLayerReduction

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4SU2OuterCutoffBlockGramContract
open YMGap.Continuum.BF4SU2OuterFineWitnessRoutingReduction
open YMGap.Continuum.BF4SU2OuterPhysicalMarkovKernelFrontier
open YMGap.Continuum.BF4SU2OuterPositiveRowClosureReduction
open YMGap.Continuum.BF4SU2OuterRawKernelCutoffDiagnostics
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualCutoffOneCoarseFaceDoor
open YMGap.Continuum.CompactDualCutoffOneParitySlabTarget
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FusionSupportAddition
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. A cutoff-one copy of an arbitrary scale-pair geometry -/

def binaryFineData (S : SlabScalePair) : SlabPhysicalData where
  coupling := S.fine.coupling
  coupling_nonnegative := S.fine.coupling_nonnegative
  cutoff := 1
  half := S.fine.half

def binaryCoarseData (S : SlabScalePair) : SlabPhysicalData where
  coupling := S.coarse.coupling
  coupling_nonnegative := S.coarse.coupling_nonnegative
  cutoff := 4
  half := S.coarse.half

/-- Same corrected-slab geometry and couplings as `S`, but with the literal
cutoff-one/four cutoff pair used by the cellular parity theorem. -/
def binaryScalePair (S : SlabScalePair) : SlabScalePair where
  fine := binaryFineData S
  coarse := binaryCoarseData S
  couplingFlow := fun _ => S.coarse.coupling
  fine_extent := by
    exact S.fine_extent
  coarse_cutoff := rfl
  coarse_coupling := Q'.eqv_refl _

theorem binaryScalePair_fine_extent (S : SlabScalePair) :
    (binaryScalePair S).fine.extent = S.fine.extent := rfl

theorem binaryScalePair_coarse_extent (S : SlabScalePair) :
    (binaryScalePair S).coarse.extent = S.coarse.extent := rfl

/-! ## 2. Binary even layers and exact reconstruction -/

/-- One globally closed binary sheet on the fine corrected slab. -/
structure BinaryEvenSlabLayer (S : SlabScalePair) : Type where
  state : EdgeLabelling
  state_mem :
    state ∈ (binaryScalePair S).fine.physicalLabellings
  oddSupport_even :
    EvenFaceIncidence
      (fineOddSlabSupport (binaryScalePair S) state)

def sumEdgeLabellings : List EdgeLabelling → EdgeLabelling
  | [] => zeroEdgeLabelling
  | head :: tail =>
      addEdgeLabelling head (sumEdgeLabellings tail)

def sumLayerStates {S : SlabScalePair} :
    List (BinaryEvenSlabLayer S) → EdgeLabelling
  | [] => zeroEdgeLabelling
  | head :: tail =>
      addEdgeLabelling head.state (sumLayerStates tail)

/-- A higher-spin fine state written as finitely many closed binary sheets.
The length bound is the constructive active-layer budget needed to return
the merged channels to the original cutoff. -/
structure BinaryEvenSlabDecomposition
    (S : SlabScalePair) (fineState : EdgeLabelling) : Type where
  layers : List (BinaryEvenSlabLayer S)
  reconstruct : sumLayerStates layers = fineState
  layer_count_le_cutoff : layers.length ≤ S.fine.cutoff

/-! ## 3. Canonical per-layer coarse data -/

def BinaryEvenSlabLayer.coarseState
    {S : SlabScalePair} (layer : BinaryEvenSlabLayer S) :
    EdgeLabelling :=
  cutoffOneCoarseParityState (binaryScalePair S) layer.state

def BinaryEvenSlabLayer.faceChannel
    {S : SlabScalePair} (layer : BinaryEvenSlabLayer S)
    (faceId : Nat) : PairChannelState :=
  binaryPacketParityChannel
    (wholeSlabFinePacket (binaryScalePair S) layer.state faceId)

theorem BinaryEvenSlabLayer.coarseState_mem
    {S : SlabScalePair} (layer : BinaryEvenSlabLayer S)
    (hcutoff : 1 ≤ S.coarse.cutoff) :
    layer.coarseState ∈ S.coarse.physicalLabellings := by
  unfold BinaryEvenSlabLayer.coarseState cutoffOneCoarseParityState
    SlabPhysicalData.physicalLabellings SlabPhysicalData.faceEdges
  exact slabBinarySupportLabelling_mem hcutoff _

theorem BinaryEvenSlabLayer.coarseState_bounded
    {S : SlabScalePair} (layer : BinaryEvenSlabLayer S) :
    SlabFaceLabellingBounded 1 S.coarse.extent layer.coarseState := by
  intro faceId _
  unfold BinaryEvenSlabLayer.coarseState cutoffOneCoarseParityState
  exact slabBinarySupportLabelling_le_one _ _ _

theorem BinaryEvenSlabLayer.coarseState_linkProduct_pos
    {S : SlabScalePair} (layer : BinaryEvenSlabLayer S) :
    0 < slabExplicitLinkMultiplicityProduct
      1 S.coarse.extent layer.coarseState := by
  unfold BinaryEvenSlabLayer.coarseState cutoffOneCoarseParityState
  apply slabBinarySupport_linkMultiplicityProduct_pos
  · omega
  · intro plaquette hmem
    exact cutoffOneCoarseParitySupport_subset_slab hmem
  · exact cutoffOneCoarseParitySupport_nodup
      (binaryScalePair S) layer.state
  · exact cutoffOneCoarseParitySupport_even layer.oddSupport_even

theorem BinaryEvenSlabLayer.coarseState_link_pos
    {S : SlabScalePair} (layer : BinaryEvenSlabLayer S)
    (link : Z4Link) :
    0 < slabExplicitLinkMultiplicity
      1 S.coarse.extent layer.coarseState link := by
  unfold BinaryEvenSlabLayer.coarseState cutoffOneCoarseParityState
  apply slabBinarySupport_linkMultiplicity_pos
  · omega
  · intro plaquette hmem
    exact cutoffOneCoarseParitySupport_subset_slab hmem
  · exact cutoffOneCoarseParitySupport_nodup
      (binaryScalePair S) layer.state
  · exact cutoffOneCoarseParitySupport_even layer.oddSupport_even

theorem BinaryEvenSlabLayer.faceChannel_final
    {S : SlabScalePair} (layer : BinaryEvenSlabLayer S)
    {faceId : Nat}
    (hface : faceId ∈ S.coarse.faceEdges) :
    (layer.faceChannel faceId).2 = layer.coarseState faceId := by
  exact
    (cutoffOneCoarseParityState_face_eq_channel
      (S := binaryScalePair S) rfl layer.state_mem hface).symm

theorem BinaryEvenSlabLayer.faceChannel_fusions
    {S : SlabScalePair} (layer : BinaryEvenSlabLayer S)
    (faceId : Nat) :
    let packet :=
      wholeSlabFinePacket (binaryScalePair S) layer.state faceId
    fusionOK packet.spin0 packet.spin1
        (layer.faceChannel faceId).1.1 = true ∧
      fusionOK packet.spin2 packet.spin3
        (layer.faceChannel faceId).1.2 = true ∧
      fusionOK
        (layer.faceChannel faceId).1.1
        (layer.faceChannel faceId).1.2
        (layer.faceChannel faceId).2 = true := by
  exact binaryPacketParityChannel_fusions _
    (wholeSlabFinePacket_binary
      (S := binaryScalePair S) rfl layer.state_mem faceId)

/-! ## 4. Additive packet/channel assembly -/

def addFaceSpinPacket
    (left right : FaceSpinPacket) : FaceSpinPacket :=
  ⟨left.spin0 + right.spin0,
    left.spin1 + right.spin1,
    left.spin2 + right.spin2,
    left.spin3 + right.spin3⟩

def addPairChannelState
    (left right : PairChannelState) : PairChannelState :=
  ((left.1.1 + right.1.1, left.1.2 + right.1.2),
    left.2 + right.2)

def zeroFaceSpinPacket : FaceSpinPacket := ⟨0, 0, 0, 0⟩

def zeroPairChannelState : PairChannelState := ((0, 0), 0)

def sumFaceSpinPackets : List FaceSpinPacket → FaceSpinPacket
  | [] => zeroFaceSpinPacket
  | head :: tail =>
      addFaceSpinPacket head (sumFaceSpinPackets tail)

def sumPairChannelStates : List PairChannelState → PairChannelState
  | [] => zeroPairChannelState
  | head :: tail =>
      addPairChannelState head (sumPairChannelStates tail)

theorem slabSpinAtPlaquette_add
    (extent : Nat) (left right : EdgeLabelling) (plaquette : Z4Plaq) :
    slabSpinAtPlaquette extent (addEdgeLabelling left right) plaquette =
      slabSpinAtPlaquette extent left plaquette +
        slabSpinAtPlaquette extent right plaquette := by
  unfold slabSpinAtPlaquette addEdgeLabelling
  by_cases hmem : plaquette ∈ boundaryCompleteSlabPlaquettes extent
  · simp [hmem]
  · simp [hmem]

theorem wholeSlabFinePacket_add
    (S : SlabScalePair) (left right : EdgeLabelling) (faceId : Nat) :
    wholeSlabFinePacket S (addEdgeLabelling left right) faceId =
      addFaceSpinPacket
        (wholeSlabFinePacket S left faceId)
        (wholeSlabFinePacket S right faceId) := by
  unfold wholeSlabFinePacket addFaceSpinPacket dyadicFaceSpinPacket
  simp only [slabSpinAtPlaquette_add]

theorem wholeSlabFinePacket_binaryScalePair
    (S : SlabScalePair) (state : EdgeLabelling) (faceId : Nat) :
    wholeSlabFinePacket (binaryScalePair S) state faceId =
      wholeSlabFinePacket S state faceId := rfl

theorem wholeSlabFinePacket_zero
    (S : SlabScalePair) (faceId : Nat) :
    wholeSlabFinePacket S zeroEdgeLabelling faceId =
      zeroFaceSpinPacket := by
  unfold wholeSlabFinePacket zeroFaceSpinPacket dyadicFaceSpinPacket
    slabSpinAtPlaquette zeroEdgeLabelling
  simp

theorem wholeSlabFinePacket_sumLayerStates
    (S : SlabScalePair)
    (layers : List (BinaryEvenSlabLayer S)) (faceId : Nat) :
    wholeSlabFinePacket S (sumLayerStates layers) faceId =
      sumFaceSpinPackets
        (layers.map fun layer =>
          wholeSlabFinePacket (binaryScalePair S) layer.state faceId) := by
  induction layers with
  | nil =>
      exact wholeSlabFinePacket_zero S faceId
  | cons head tail ih =>
      rw [sumLayerStates, wholeSlabFinePacket_add, List.map_cons,
        sumFaceSpinPackets, ih, wholeSlabFinePacket_binaryScalePair]

/-! ## 5. The merged coarse target and its shared-link support -/

def sumLayerCoarseStates {S : SlabScalePair} :
    List (BinaryEvenSlabLayer S) → EdgeLabelling
  | [] => zeroEdgeLabelling
  | head :: tail =>
      addEdgeLabelling head.coarseState
        (sumLayerCoarseStates tail)

theorem sumLayerCoarseStates_bounded
    {S : SlabScalePair} :
    ∀ layers : List (BinaryEvenSlabLayer S),
      SlabFaceLabellingBounded layers.length S.coarse.extent
        (sumLayerCoarseStates layers)
  | [] => by
      intro faceId _
      change 0 ≤ 0
      omega
  | head :: tail => by
      simpa only [List.length_cons, sumLayerCoarseStates,
        Nat.add_comm 1 tail.length] using
        slabFaceLabellingBounded_add
          head.coarseState_bounded
          (sumLayerCoarseStates_bounded tail)

theorem sumLayerCoarseStates_zero_outside
    {S : SlabScalePair} :
    ∀ (layers : List (BinaryEvenSlabLayer S)) (faceId : Nat),
      faceId ∉ S.coarse.faceEdges →
        sumLayerCoarseStates layers faceId = 0
  | [], _, _ => rfl
  | head :: tail, faceId, hface => by
      unfold sumLayerCoarseStates addEdgeLabelling
      have hhead :
          head.coarseState faceId = 0 := by
        unfold BinaryEvenSlabLayer.coarseState
          cutoffOneCoarseParityState
        exact slabBinarySupportLabelling_eq_zero_of_not_physical hface
      rw [hhead, sumLayerCoarseStates_zero_outside tail faceId hface]

theorem BinaryEvenSlabDecomposition.coarseTarget_mem
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (decomposition : BinaryEvenSlabDecomposition S fineState) :
    sumLayerCoarseStates decomposition.layers ∈
      S.coarse.physicalLabellings := by
  unfold SlabPhysicalData.physicalLabellings
  apply boundedEdgeLabellings_complete
  · intro faceId hface
    have hbound :=
      sumLayerCoarseStates_bounded decomposition.layers faceId hface
    have hcount := decomposition.layer_count_le_cutoff
    rw [S.coarse_cutoff]
    omega
  · intro faceId hface
    exact sumLayerCoarseStates_zero_outside
      decomposition.layers faceId hface

theorem sumLayerCoarseStates_link_pos_at_length
    {S : SlabScalePair} :
    ∀ (layers : List (BinaryEvenSlabLayer S)) (link : Z4Link),
      0 < slabExplicitLinkMultiplicity
        layers.length S.coarse.extent
        (sumLayerCoarseStates layers) link
  | [], link => by
      change 0 <
        slabExplicitLinkMultiplicity
          0 S.coarse.extent zeroEdgeLabelling link
      rw [slabExplicitLinkMultiplicity_zero_eq_one]
      omega
  | head :: tail, link => by
      have hsum :=
        slabExplicitLinkMultiplicity_add_pos link
          (head.coarseState_link_pos link)
          (sumLayerCoarseStates_link_pos_at_length tail link)
      simpa only [sumLayerCoarseStates, List.length_cons,
        Nat.add_comm 1 tail.length] using hsum

theorem BinaryEvenSlabDecomposition.coarseTarget_link_pos
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (decomposition : BinaryEvenSlabDecomposition S fineState)
    (link : Z4Link) :
    0 < slabExplicitLinkMultiplicity
      S.coarse.cutoff S.coarse.extent
      (sumLayerCoarseStates decomposition.layers) link := by
  have hlength :
      decomposition.layers.length ≤ S.coarse.cutoff := by
    have hcount := decomposition.layer_count_le_cutoff
    rw [S.coarse_cutoff]
    omega
  have hstable :=
    slabExplicitLinkMultiplicity_cutoff_stable
      hlength
      (sumLayerCoarseStates_bounded decomposition.layers)
      link
  rw [hstable]
  exact sumLayerCoarseStates_link_pos_at_length
    decomposition.layers link

/-! ## 6. The merged face channel -/

def sumLayerFaceChannels {S : SlabScalePair}
    (faceId : Nat) :
    List (BinaryEvenSlabLayer S) → PairChannelState
  | [] => zeroPairChannelState
  | head :: tail =>
      addPairChannelState (head.faceChannel faceId)
        (sumLayerFaceChannels faceId tail)

theorem binaryPacketParityChannel_bounds
    (packet : FaceSpinPacket) :
    (binaryPacketParityChannel packet).1.1 ≤ 1 ∧
      (binaryPacketParityChannel packet).1.2 ≤ 1 ∧
      (binaryPacketParityChannel packet).2 ≤ 1 := by
  unfold binaryPacketParityChannel
  change
    (packet.spin0 + packet.spin1) % 2 ≤ 1 ∧
      (packet.spin2 + packet.spin3) % 2 ≤ 1 ∧
      (packet.spin0 + packet.spin1 +
        packet.spin2 + packet.spin3) % 2 ≤ 1
  exact
    ⟨Nat.lt_succ_iff.mp
        (Nat.mod_lt _ (by omega : 0 < 2)),
      Nat.lt_succ_iff.mp
        (Nat.mod_lt _ (by omega : 0 < 2)),
      Nat.lt_succ_iff.mp
        (Nat.mod_lt _ (by omega : 0 < 2))⟩

theorem sumLayerFaceChannels_fusions
    {S : SlabScalePair} (faceId : Nat) :
    ∀ layers : List (BinaryEvenSlabLayer S),
      let packet :=
        wholeSlabFinePacket S (sumLayerStates layers) faceId
      let channel := sumLayerFaceChannels faceId layers
      fusionOK packet.spin0 packet.spin1 channel.1.1 = true ∧
        fusionOK packet.spin2 packet.spin3 channel.1.2 = true ∧
        fusionOK channel.1.1 channel.1.2 channel.2 = true
  | [] => by
      simp only [sumLayerStates, sumLayerFaceChannels,
        wholeSlabFinePacket_zero, zeroFaceSpinPacket,
        zeroPairChannelState]
      decide
  | head :: tail => by
      have hhead := head.faceChannel_fusions faceId
      have htail := sumLayerFaceChannels_fusions faceId tail
      rw [sumLayerStates, wholeSlabFinePacket_add]
      change
        fusionOK
            ((wholeSlabFinePacket S head.state faceId).spin0 +
              (wholeSlabFinePacket S (sumLayerStates tail) faceId).spin0)
            ((wholeSlabFinePacket S head.state faceId).spin1 +
              (wholeSlabFinePacket S (sumLayerStates tail) faceId).spin1)
            ((head.faceChannel faceId).1.1 +
              (sumLayerFaceChannels faceId tail).1.1) = true ∧
          fusionOK
            ((wholeSlabFinePacket S head.state faceId).spin2 +
              (wholeSlabFinePacket S (sumLayerStates tail) faceId).spin2)
            ((wholeSlabFinePacket S head.state faceId).spin3 +
              (wholeSlabFinePacket S (sumLayerStates tail) faceId).spin3)
            ((head.faceChannel faceId).1.2 +
              (sumLayerFaceChannels faceId tail).1.2) = true ∧
          fusionOK
            ((head.faceChannel faceId).1.1 +
              (sumLayerFaceChannels faceId tail).1.1)
            ((head.faceChannel faceId).1.2 +
              (sumLayerFaceChannels faceId tail).1.2)
            ((head.faceChannel faceId).2 +
              (sumLayerFaceChannels faceId tail).2) = true
      rw [wholeSlabFinePacket_binaryScalePair] at hhead
      exact
        ⟨fusionOK_add hhead.1 htail.1,
          fusionOK_add hhead.2.1 htail.2.1,
          fusionOK_add hhead.2.2 htail.2.2⟩

theorem sumLayerFaceChannels_bounds
    {S : SlabScalePair} (faceId : Nat) :
    ∀ layers : List (BinaryEvenSlabLayer S),
      (sumLayerFaceChannels faceId layers).1.1 ≤ layers.length ∧
        (sumLayerFaceChannels faceId layers).1.2 ≤ layers.length ∧
        (sumLayerFaceChannels faceId layers).2 ≤ layers.length
  | [] => by
      simp only [sumLayerFaceChannels, zeroPairChannelState,
        List.length_nil]
      exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩
  | head :: tail => by
      have hhead :
          (head.faceChannel faceId).1.1 ≤ 1 ∧
            (head.faceChannel faceId).1.2 ≤ 1 ∧
            (head.faceChannel faceId).2 ≤ 1 := by
        unfold BinaryEvenSlabLayer.faceChannel
        exact binaryPacketParityChannel_bounds _
      have htail := sumLayerFaceChannels_bounds faceId tail
      unfold sumLayerFaceChannels addPairChannelState
      change
        (head.faceChannel faceId).1.1 +
              (sumLayerFaceChannels faceId tail).1.1 ≤
            tail.length + 1 ∧
          (head.faceChannel faceId).1.2 +
              (sumLayerFaceChannels faceId tail).1.2 ≤
            tail.length + 1 ∧
          (head.faceChannel faceId).2 +
              (sumLayerFaceChannels faceId tail).2 ≤
            tail.length + 1
      have hleft :
          (head.faceChannel faceId).1.1 +
              (sumLayerFaceChannels faceId tail).1.1 ≤
            1 + tail.length :=
        Nat.add_le_add hhead.1 htail.1
      have hright :
          (head.faceChannel faceId).1.2 +
              (sumLayerFaceChannels faceId tail).1.2 ≤
            1 + tail.length :=
        Nat.add_le_add hhead.2.1 htail.2.1
      have hfinal :
          (head.faceChannel faceId).2 +
              (sumLayerFaceChannels faceId tail).2 ≤
            1 + tail.length :=
        Nat.add_le_add hhead.2.2 htail.2.2
      exact
        ⟨by simpa [Nat.add_comm] using hleft,
          by simpa [Nat.add_comm] using hright,
          by simpa [Nat.add_comm] using hfinal⟩

theorem BinaryEvenSlabDecomposition.faceChannel_mem
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (decomposition : BinaryEvenSlabDecomposition S fineState)
    (faceId : Nat) :
    sumLayerFaceChannels faceId decomposition.layers ∈
      pairChannelStateSpace S.fine.cutoff := by
  apply (mem_pairChannelStateSpace_iff S.fine.cutoff _).mpr
  have hbounds :=
    sumLayerFaceChannels_bounds faceId decomposition.layers
  have hcount := decomposition.layer_count_le_cutoff
  have hleft :
      (sumLayerFaceChannels faceId decomposition.layers).1.1 ≤
        S.fine.cutoff :=
    Nat.le_trans hbounds.1 hcount
  have hright :
      (sumLayerFaceChannels faceId decomposition.layers).1.2 ≤
        S.fine.cutoff :=
    Nat.le_trans hbounds.2.1 hcount
  have hfinal :
      (sumLayerFaceChannels faceId decomposition.layers).2 ≤
        S.fine.cutoff :=
    Nat.le_trans hbounds.2.2 hcount
  exact
    ⟨Nat.le_trans hleft
        (Nat.le_mul_of_pos_left _ (by decide : 0 < 2)),
      Nat.le_trans hright
        (Nat.le_mul_of_pos_left _ (by decide : 0 < 2)),
      Nat.le_trans hfinal
        (Nat.le_mul_of_pos_left _ (by decide : 0 < 4))⟩

theorem sumLayerFaceChannels_final
    {S : SlabScalePair} {faceId : Nat}
    (hface : faceId ∈ S.coarse.faceEdges) :
    ∀ layers : List (BinaryEvenSlabLayer S),
      (sumLayerFaceChannels faceId layers).2 =
        sumLayerCoarseStates layers faceId
  | [] => rfl
  | head :: tail => by
      unfold sumLayerFaceChannels sumLayerCoarseStates
        addPairChannelState addEdgeLabelling
      rw [head.faceChannel_final hface,
        sumLayerFaceChannels_final hface tail]

private theorem fusionInd_eq_one_of_true
    {a b c : Nat} (hfusion : fusionOK a b c = true) :
    fusionInd a b c = 1 := by
  unfold fusionInd
  rw [if_pos hfusion]

theorem packetPairChannelRawWeight_pos_of_fusions
    {w : Q'} (hw : (0 : Q') < w)
    (packet : FaceSpinPacket) (channel : PairChannelState)
    (hfusions :
      fusionOK packet.spin0 packet.spin1 channel.1.1 = true ∧
        fusionOK packet.spin2 packet.spin3 channel.1.2 = true ∧
        fusionOK channel.1.1 channel.1.2 channel.2 = true) :
    (0 : Q') < packetPairChannelRawWeight w packet channel := by
  unfold packetPairChannelRawWeight
  rw [fusionInd_eq_one_of_true hfusions.1,
    fusionInd_eq_one_of_true hfusions.2.1,
    fusionInd_eq_one_of_true hfusions.2.2]
  exact Q'.mul_pos (coeffW_pos hw channel.2) (by decide)

theorem BinaryEvenSlabDecomposition.faceChannel_positive
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (decomposition : BinaryEvenSlabDecomposition S fineState)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (faceId : Nat) :
    (0 : Q') <
      packetPairChannelRawWeight S.coarse.coupling
        (wholeSlabFinePacket S fineState faceId)
        (sumLayerFaceChannels faceId decomposition.layers) := by
  have hfusions :=
    sumLayerFaceChannels_fusions faceId decomposition.layers
  rw [decomposition.reconstruct] at hfusions
  exact packetPairChannelRawWeight_pos_of_fusions hcoarseCoupling _ _
    hfusions

/-! ## 7. Exact joint selection and the remaining geometric input -/

/-- A closed binary-layer decomposition constructs the literal simultaneous
coarse target, face channels, and positive shared-link support. -/
def BinaryEvenSlabDecomposition.toJointChannelSelection
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (decomposition : BinaryEvenSlabDecomposition S fineState)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling) :
    WholeSlabJointChannelSelection S fineState where
  coarseTarget := sumLayerCoarseStates decomposition.layers
  coarseTarget_mem := decomposition.coarseTarget_mem
  faceChannel := fun faceId =>
    sumLayerFaceChannels faceId decomposition.layers
  faceChannel_mem := fun faceId _ =>
    decomposition.faceChannel_mem faceId
  faceChannel_final := fun faceId hface =>
    sumLayerFaceChannels_final
      (faceId := faceId) hface decomposition.layers
  faceChannel_positive := fun faceId _ =>
    decomposition.faceChannel_positive hcoarseCoupling faceId
  coarseLink_positive := fun link _ =>
    decomposition.coarseTarget_link_pos link

/-- **OPEN BINARY-SHEET INPUT.** Every positive higher-cutoff outer fine row
admits an explicit decomposition into at most `K` globally even binary slab
layers.  Unlike the earlier router, this field mentions only the fine
geometry; the coarse target and every fusion channel are derived above. -/
structure SU2OuterBinaryLayerDecomposition
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) : Type where
  decompose :
    ∀ K source,
      K ≠ 1 →
      source ∈
        (su2OuterScalePair
          G g hg candidate hcandidate K).fine.physicalLabellings →
      (0 : Q') <
        (su2OuterScalePair
          G g hg candidate hcandidate K).fine.physicalTerm source →
      BinaryEvenSlabDecomposition
        (su2OuterScalePair
          G g hg candidate hcandidate K) source

def SU2OuterBinaryLayerDecomposition.toJointChannelSelection
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (layers :
      SU2OuterBinaryLayerDecomposition
        G g hg candidate hcandidate) :
    SU2OuterJointChannelSelection
      G g hg candidate hcandidate where
  select := by
    intro K source hK hsource hpositive
    exact
      (layers.decompose K source hK hsource hpositive).toJointChannelSelection
        (by
          change (0 : Q') < candidate
          exact hcandidate)

def SU2OuterBinaryLayerDecomposition.toPositiveRowClosure
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (layers :
      SU2OuterBinaryLayerDecomposition
        G g hg candidate hcandidate) :
    SU2OuterPositiveRowClosure
      G g hg candidate hcandidate :=
  layers.toJointChannelSelection.toPositiveRowClosure

#print axioms binaryScalePair
#print axioms Nat.mod_lt
#print axioms Nat.le_of_lt
#print axioms binaryPacketParityChannel_mem
#print axioms BinaryEvenSlabLayer
#print axioms BinaryEvenSlabDecomposition
#print axioms BinaryEvenSlabLayer.coarseState_link_pos
#print axioms wholeSlabFinePacket_sumLayerStates
#print axioms BinaryEvenSlabDecomposition.coarseTarget_mem
#print axioms sumLayerCoarseStates_link_pos_at_length
#print axioms BinaryEvenSlabDecomposition.coarseTarget_link_pos
#print axioms sumLayerFaceChannels_fusions
#print axioms binaryPacketParityChannel_bounds
#print axioms sumLayerFaceChannels_bounds
#print axioms BinaryEvenSlabDecomposition.faceChannel_mem
#print axioms sumLayerFaceChannels_final
#print axioms BinaryEvenSlabDecomposition.faceChannel_positive
#print axioms BinaryEvenSlabDecomposition.toJointChannelSelection
#print axioms SU2OuterBinaryLayerDecomposition
#print axioms SU2OuterBinaryLayerDecomposition.toJointChannelSelection
#print axioms SU2OuterBinaryLayerDecomposition.toPositiveRowClosure

end YMGap.Continuum.BF4SU2OuterBinaryLayerReduction
