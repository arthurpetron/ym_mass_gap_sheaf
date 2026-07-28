/-
# Arbitrary finite binary multicovers for the SU(2) outer row

The earlier binary-layer reduction imposed the global budget
`layers.length ≤ K`.  That budget is stronger than the finite-cutoff
requirements and is false even for a small positive cutoff-two row.

This module removes that artificial restriction.  A multicover is any finite
sum of globally even cutoff-one sheets which reconstructs the fine labelling.
The retained pair-channel bounds are proved from the reconstructed four-spin
packet itself:

* each pair output is at most the sum of its two input spins, hence at most
  `2*K`;
* the final output is at most the sum of the two pair outputs, hence at most
  `4*K`.

The summed coarse target is bounded by the same final-output estimate.
Coarse-link positivity is first obtained in the additive cutoff equal to the
number of sheets, then transported to the physical cutoff `4*K` by the
already-proved cutoff-independence theorem.  This works in either order of
the two cutoffs and therefore does not reintroduce a sheet-count hypothesis.

Thus every binary multicover constructs a literal enumerated joint carrier.
The remaining input is the genuine integral-cycle decomposition statement
that positive fine intertwiner data admits such a multicover.

## Axiom gate

Finite list recursion, exact natural arithmetic, and exact `Q'` order only.
No `Classical.*`, `sorry`, `native_decide`, custom axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4SU2OuterBinaryLayerReduction
import YMGap.Continuum.BF4SU2OuterJointCarrierEnumeration

namespace YMGap.Continuum.BF4SU2OuterBinaryMulticoverReduction

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4SU2OuterBinaryLayerReduction
open YMGap.Continuum.BF4SU2OuterJointCarrierEnumeration
open YMGap.Continuum.BF4SU2OuterPhysicalMarkovKernelFrontier
open YMGap.Continuum.BF4SU2OuterPositiveRowClosureReduction
open YMGap.Continuum.BF4SU2OuterRawKernelCutoffDiagnostics
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualCutoffOneParitySlabTarget
open YMGap.Continuum.CompactDualCutoffOnePositivePhysicalClosure
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4UnitCubeIncidenceParity

/-! ## 1. The corrected geometric input -/

/-- A finite multicover by globally even cutoff-one sheets.  Unlike
`BinaryEvenSlabDecomposition`, there is no global sheet-count restriction. -/
structure BinaryEvenSlabMulticover
    (S : SlabScalePair) (fineState : EdgeLabelling) : Type where
  layers : List (BinaryEvenSlabLayer S)
  reconstruct : sumLayerStates layers = fineState

/-- Any explicitly closed binary support gives one admissible layer.  The
proof identifies its cutoff-one state with the binary indicator of its own
odd support and transports geometric incidence through the exact local spin
sum. -/
def binaryEvenSlabLayerOfSupport
    (S : SlabScalePair) (support : List Z4Plaq)
    (hsubset :
      ∀ plaquette, plaquette ∈ support →
        plaquette ∈
          boundaryCompleteSlabPlaquettes S.fine.extent)
    (hnodup : support.Nodup)
    (heven : EvenFaceIncidence support) :
    BinaryEvenSlabLayer S where
  state :=
    slabBinarySupportLabelling S.fine.extent support
  state_mem := by
    change slabBinarySupportLabelling S.fine.extent support ∈
      boundedEdgeLabellings 1
        (slabPhysicalFaceEdges S.fine.extent)
    exact slabBinarySupportLabelling_mem (by omega) support
  oddSupport_even := by
    let state :=
      slabBinarySupportLabelling S.fine.extent support
    have hstateMem :
        state ∈
          (binaryScalePair S).fine.physicalLabellings := by
      change state ∈
        boundedEdgeLabellings 1
          (slabPhysicalFaceEdges S.fine.extent)
      exact slabBinarySupportLabelling_mem (by omega) support
    have hstate :=
      cutoffOneFineState_eq_oddSupportLabelling
        (S := binaryScalePair S) rfl hstateMem
    intro link
    have hodd :=
      slabBinarySupport_localExternalSpinSum
        (fun _ hmem => fineOddSlabSupport_subset hmem)
        (fineOddSlabSupport_nodup (binaryScalePair S) state)
        link
    have hsupport :=
      slabBinarySupport_localExternalSpinSum
        hsubset hnodup link
    rw [binaryScalePair_fine_extent] at hstate hodd
    rw [← hstate] at hodd
    change
      faceIncidenceCount link
          (fineOddSlabSupport (binaryScalePair S) state) %
          2 = 0
    rw [← hodd]
    change
      localExternalSpinSum
          (slabIncidentPlaqIds S.fine.extent link).length
          (externalSpinsOfList
            ((slabIncidentPlaqIds S.fine.extent link).map
              (slabBinarySupportLabelling
                S.fine.extent support))) % 2 = 0
    rw [hsupport]
    exact heven link

/-- Every old bounded decomposition is, in particular, a multicover. -/
def BinaryEvenSlabDecomposition.toMulticover
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (decomposition : BinaryEvenSlabDecomposition S fineState) :
    BinaryEvenSlabMulticover S fineState where
  layers := decomposition.layers
  reconstruct := decomposition.reconstruct

/-! ## 2. Local packet bounds replace the false global count bound -/

theorem BinaryEvenSlabMulticover.faceChannel_fusions
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (multicover : BinaryEvenSlabMulticover S fineState)
    (faceId : Nat) :
    let packet := wholeSlabFinePacket S fineState faceId
    let channel := sumLayerFaceChannels faceId multicover.layers
    fusionOK packet.spin0 packet.spin1 channel.1.1 = true ∧
      fusionOK packet.spin2 packet.spin3 channel.1.2 = true ∧
      fusionOK channel.1.1 channel.1.2 channel.2 = true := by
  have hfusions :=
    sumLayerFaceChannels_fusions faceId multicover.layers
  rw [multicover.reconstruct] at hfusions
  exact hfusions

theorem BinaryEvenSlabMulticover.faceChannel_mem
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (multicover : BinaryEvenSlabMulticover S fineState)
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (faceId : Nat) :
    sumLayerFaceChannels faceId multicover.layers ∈
      pairChannelStateSpace S.fine.cutoff := by
  let packet := wholeSlabFinePacket S fineState faceId
  let channel := sumLayerFaceChannels faceId multicover.layers
  have hfusions := multicover.faceChannel_fusions faceId
  have hpacket :=
    (mem_faceSpinPacketStateSpace_iff S.fine.cutoff packet).mp
      (wholeSlabFinePacket_mem hfineMem faceId)
  have hleft : channel.1.1 ≤ packet.spin0 + packet.spin1 :=
    fusionOK_output_le_add hfusions.1
  have hright : channel.1.2 ≤ packet.spin2 + packet.spin3 :=
    fusionOK_output_le_add hfusions.2.1
  have hfinal : channel.2 ≤ channel.1.1 + channel.1.2 :=
    fusionOK_output_le_add hfusions.2.2
  have hleftBound : channel.1.1 ≤ 2 * S.fine.cutoff := by
    exact Nat.le_trans hleft
      (by
        have hadd := Nat.add_le_add hpacket.1 hpacket.2.1
        simpa [Nat.two_mul] using hadd)
  have hrightBound : channel.1.2 ≤ 2 * S.fine.cutoff := by
    exact Nat.le_trans hright
      (by
        have hadd := Nat.add_le_add hpacket.2.2.1 hpacket.2.2.2
        simpa [Nat.two_mul] using hadd)
  have hfinalBound : channel.2 ≤ 4 * S.fine.cutoff := by
    calc
      channel.2 ≤ channel.1.1 + channel.1.2 := hfinal
      _ ≤ 2 * S.fine.cutoff + 2 * S.fine.cutoff :=
        Nat.add_le_add hleftBound hrightBound
      _ = (2 + 2) * S.fine.cutoff :=
        (Nat.add_mul 2 2 S.fine.cutoff).symm
      _ = 4 * S.fine.cutoff := rfl
  apply (mem_pairChannelStateSpace_iff S.fine.cutoff channel).mpr
  exact ⟨hleftBound, hrightBound, hfinalBound⟩

theorem BinaryEvenSlabMulticover.coarseTarget_bounded
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (multicover : BinaryEvenSlabMulticover S fineState)
    (hfineMem : fineState ∈ S.fine.physicalLabellings) :
    SlabFaceLabellingBounded S.coarse.cutoff S.coarse.extent
      (sumLayerCoarseStates multicover.layers) := by
  intro faceId hface
  have hchannelMem := multicover.faceChannel_mem hfineMem faceId
  have hfinal :=
    (mem_pairChannelStateSpace_iff S.fine.cutoff
      (sumLayerFaceChannels faceId multicover.layers)).mp hchannelMem
  rw [← sumLayerFaceChannels_final hface]
  rw [S.coarse_cutoff]
  exact hfinal.2.2

theorem BinaryEvenSlabMulticover.coarseTarget_mem
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (multicover : BinaryEvenSlabMulticover S fineState)
    (hfineMem : fineState ∈ S.fine.physicalLabellings) :
    sumLayerCoarseStates multicover.layers ∈
      S.coarse.physicalLabellings := by
  unfold SlabPhysicalData.physicalLabellings
  apply boundedEdgeLabellings_complete
  · intro faceId hface
    have hbound :=
      multicover.coarseTarget_bounded hfineMem faceId hface
    omega
  · intro faceId hface
    exact sumLayerCoarseStates_zero_outside
      multicover.layers faceId hface

/-! ## 3. Cutoff-independent coarse-link support -/

theorem BinaryEvenSlabMulticover.coarseTarget_link_pos
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (multicover : BinaryEvenSlabMulticover S fineState)
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (link : Z4Link) :
    0 < slabExplicitLinkMultiplicity
      S.coarse.cutoff S.coarse.extent
      (sumLayerCoarseStates multicover.layers) link := by
  have hpositive :
      0 < slabExplicitLinkMultiplicity
        multicover.layers.length S.coarse.extent
        (sumLayerCoarseStates multicover.layers) link :=
    sumLayerCoarseStates_link_pos_at_length multicover.layers link
  by_cases horder : multicover.layers.length ≤ S.coarse.cutoff
  · have hstable :=
      slabExplicitLinkMultiplicity_cutoff_stable
        horder (sumLayerCoarseStates_bounded multicover.layers) link
    rw [hstable]
    exact hpositive
  · have hreverse : S.coarse.cutoff ≤ multicover.layers.length := by
      omega
    have hstable :=
      slabExplicitLinkMultiplicity_cutoff_stable
        hreverse (multicover.coarseTarget_bounded hfineMem) link
    rw [hstable] at hpositive
    exact hpositive

/-! ## 4. Genuine semantic and enumerated joint carriers -/

theorem BinaryEvenSlabMulticover.faceChannel_positive
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (multicover : BinaryEvenSlabMulticover S fineState)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (faceId : Nat) :
    (0 : Q') <
      packetPairChannelRawWeight S.coarse.coupling
        (wholeSlabFinePacket S fineState faceId)
        (sumLayerFaceChannels faceId multicover.layers) := by
  exact packetPairChannelRawWeight_pos_of_fusions
    hcoarseCoupling _ _ (multicover.faceChannel_fusions faceId)

def BinaryEvenSlabMulticover.toJointChannelSelection
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (multicover : BinaryEvenSlabMulticover S fineState)
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling) :
    WholeSlabJointChannelSelection S fineState where
  coarseTarget := sumLayerCoarseStates multicover.layers
  coarseTarget_mem := multicover.coarseTarget_mem hfineMem
  faceChannel := fun faceId =>
    sumLayerFaceChannels faceId multicover.layers
  faceChannel_mem := fun faceId _ =>
    multicover.faceChannel_mem hfineMem faceId
  faceChannel_final := fun faceId hface =>
    sumLayerFaceChannels_final
      (faceId := faceId) hface multicover.layers
  faceChannel_positive := fun faceId _ =>
    multicover.faceChannel_positive hcoarseCoupling faceId
  coarseLink_positive := fun link _ =>
    multicover.coarseTarget_link_pos hfineMem link

/-- The multicover produces an actual member of the executable finite joint
carrier enumeration, not merely a proposition that some carrier exists. -/
def BinaryEvenSlabMulticover.toEnumeratedJointCarrier
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (multicover : BinaryEvenSlabMulticover S fineState)
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling) :
    WholeSlabEnumeratedJointCarrier S fineState :=
  jointSelectionToEnumeratedCarrier
    (multicover.toJointChannelSelection hfineMem hcoarseCoupling)

def BinaryEvenSlabMulticover.toCarrierNonempty
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (multicover : BinaryEvenSlabMulticover S fineState)
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling) :
    WholeSlabJointCarrierNonempty S fineState :=
  (multicover.toEnumeratedJointCarrier
    hfineMem hcoarseCoupling).toNonempty

/-! ## 5. All-row family interface -/

/-- The remaining all-row input after removing the false global sheet budget.
It refers only to the fine cellular geometry.  Every coarse target, face
channel, and coarse intertwiner is constructed above. -/
structure SU2OuterBinaryMulticover
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
      BinaryEvenSlabMulticover
        (su2OuterScalePair
          G g hg candidate hcandidate K) source

def SU2OuterBinaryMulticover.toJointCarrierNonempty
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (multicover :
      SU2OuterBinaryMulticover
        G g hg candidate hcandidate) :
    SU2OuterJointCarrierNonempty
      G g hg candidate hcandidate where
  nonempty := by
    intro K source hK hsource hpositive
    exact
      (multicover.decompose
        K source hK hsource hpositive).toCarrierNonempty
          hsource
          (by
            change (0 : Q') < candidate
            exact hcandidate)

def SU2OuterBinaryMulticover.toPositiveRowClosure
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (multicover :
      SU2OuterBinaryMulticover
        G g hg candidate hcandidate) :
    SU2OuterPositiveRowClosure
      G g hg candidate hcandidate :=
  multicover.toJointCarrierNonempty.toPositiveRowClosure

#print axioms BinaryEvenSlabMulticover
#print axioms binaryEvenSlabLayerOfSupport
#print axioms BinaryEvenSlabDecomposition.toMulticover
#print axioms BinaryEvenSlabMulticover.faceChannel_fusions
#print axioms wholeSlabFinePacket_mem
#print axioms fusionOK_output_le_add
#print axioms mem_faceSpinPacketStateSpace_iff
#print axioms mem_pairChannelStateSpace_iff
#print axioms BinaryEvenSlabMulticover.faceChannel_mem
#print axioms BinaryEvenSlabMulticover.coarseTarget_bounded
#print axioms BinaryEvenSlabMulticover.coarseTarget_mem
#print axioms BinaryEvenSlabMulticover.coarseTarget_link_pos
#print axioms BinaryEvenSlabMulticover.toJointChannelSelection
#print axioms BinaryEvenSlabMulticover.toEnumeratedJointCarrier
#print axioms BinaryEvenSlabMulticover.toCarrierNonempty
#print axioms SU2OuterBinaryMulticover.toJointCarrierNonempty
#print axioms SU2OuterBinaryMulticover.toPositiveRowClosure

end YMGap.Continuum.BF4SU2OuterBinaryMulticoverReduction
