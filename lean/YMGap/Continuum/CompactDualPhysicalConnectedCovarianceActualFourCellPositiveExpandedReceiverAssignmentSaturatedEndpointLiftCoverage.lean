/-
# Factor saturated receiver coverage through one-replica raw endpoint lifts

The assignment-saturated receiver image forgets accepted coarse auxiliary
assignments, but it still asks whether each physical coarse endpoint occurs
in a strictly positive cutoff-one whole-slab raw row.  This module isolates
that remaining task at one replica.

A `PositiveExpandedRawEndpointCoverage` supplies, for every attached coarse
expanded endpoint, one enumerated positive expanded fine source whose literal
whole-slab raw transition to that endpoint's physical labelling is strictly
positive.  This is the exact receiver carrier: unlike the full bounded
Cartesian list, it contains only labellings with an accepted coarse
intertwiner assignment.  Two such lifts assemble constructively into each
source or opposite four-cell path.  It follows that every
assignment-saturated receiver is covered and the unreachable
source-plus-target mass is exactly zero.

The face-positivity premise is factored once more into explicit local data:
one enumerated pair channel at every coarse face, its prescribed final spin,
and the three Boolean fusion guards making its raw character weight strictly
positive.  The stretched channel makes these guards automatic when the
coarse spin equals the sum of the four fine binary spins.  A duplicate-free
even-incidence fine support also supplies its positive Gibbs term and one
accepted fine intertwiner constructively.  The remaining producer is
therefore the exact geometric reverse lift: one closed binary support whose
dyadic four-face block counts equal the attached coarse labelling.

The matched-AF adapter consequently removes the unreachable-mass analytic
field entirely, conditional only on this explicit finite raw-support
coverage at every scale.  The separate covered-calibration, spacing, and raw
mismatch estimates remain unchanged and uninhabited.

No endpoint lift is constructed here.  In particular, the existing
fine-to-coarse parity target provides one positive target per fine row, not
the reverse lift for every attached coarse endpoint required below.  Requiring
all bounded coarse labellings would be unnecessarily strong: that Cartesian
list also contains link-inadmissible zero-mass states.  This is a finite exact
reduction, not a cutoff-uniform contraction, continuum construction, OS/GNS
reconstruction, Hamiltonian gap, or Yang--Mills mass gap.

Constructive contract: proof-carrying finite members, Boolean support, and
exact rational inequalities only; no choice, `Classical`, `native_decide`,
proof hole, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedPositiveOccupationQuadraticCost
import YMGap.Continuum.Z4DyadicSubdivisionClosure

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedEndpointLiftCoverage

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.BF4AFPhysicalSpacingToZero
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4SU2OuterFineWitnessRoutingReduction
open YMGap.Continuum.BF4SU2OuterPositiveRowClosureReduction
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedPaths
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedMatchedAFQuadraticCost
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedNormalizedVariation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedPhysicalCoverage
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverOrientation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedSupportedPaths
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreCarrier
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalMatchedAFTrajectory
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4DyadicModTwoCellularKernel
open YMGap.Continuum.Z4DyadicPlaquetteBlockGeometry
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4DyadicSubdivisionClosure
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4UnitCubeEnumerationParity

local infix:50 " ≈ " => Q'.eqv

local instance endpointLiftPairDecidableEq
    (D : SlabPhysicalData) (root : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair D root) :=
  slabObservableTwoReplicaPairDecidableEq D root

/-! ## 1. One-replica positive raw endpoint coverage -/

/-- One enumerated positive expanded fine source with a strictly positive
literal raw transition to the selected physical coarse endpoint. -/
structure PositiveExpandedRawEndpointLift
    (S : SlabScalePair) (coarseTarget : EdgeLabelling) : Type where
  source : PositiveExpandedPhysicalSource S
  source_mem : source ∈ positiveExpandedPhysicalSources S
  rawWeight_pos :
    (0 : Q') < wholeSlabRecouplingRawWeight
      S source.1.1 coarseTarget

/-- An attached coarse endpoint has a strictly positive complete link
multiplicity: its attachment contains one literal member of the global
coarse-intertwiner witness list. -/
theorem attachedEndpoint_linkMultiplicityProduct_pos
    {S : SlabScalePair}
    (endpoint : SlabExpandedFineSourceEntry S.coarse) :
    0 < slabExplicitLinkMultiplicityProduct
      S.coarse.cutoff S.coarse.extent endpoint.1.1 := by
  have hassignment :=
    (mem_slabExpandedFineSources_iff.mp endpoint.2).2
  have hlength := List.length_pos_of_mem hassignment
  rwa [slabFineFusionWitnesses_length] at hlength

/-- The constructive payload still needed above one attached coarse endpoint:
one enumerated positive fine source for which every local fixed-final face
sum at that endpoint is strictly positive.  The endpoint attachment already
discharges the separate global coarse-link factor. -/
structure PositiveExpandedFaceCompatibleEndpointLift
    (S : SlabScalePair)
    (endpoint : SlabExpandedFineSourceEntry S.coarse) : Type where
  source : PositiveExpandedPhysicalSource S
  source_mem : source ∈ positiveExpandedPhysicalSources S
  faceRawWeight_pos : ∀ coarseFaceId,
    coarseFaceId ∈ S.coarse.faceEdges →
      (0 : Q') < wholeSlabFaceRawWeight
        S source.1.1 endpoint.1.1 coarseFaceId

private theorem qOfNat_pos_of_pos_local {n : Nat} (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  cases n with
  | zero => omega
  | succ n => exact Q'.ofNat_succ_pos n

private theorem positivePhysicalSource_mem_aux_local
    {S : SlabScalePair} (source : PositivePhysicalSource S) :
    ∀ (sources : List EdgeLabelling)
      (hphysical : ∀ item, item ∈ sources →
        item ∈ S.fine.physicalLabellings),
      source.1 ∈ sources →
        source ∈ positivePhysicalSourcesAux S sources hphysical
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hphysical, hmem => by
      simp only [positivePhysicalSourcesAux]
      split
      next hheadPositive =>
        rcases List.mem_cons.mp hmem with hhead | htail
        · subst head
          apply List.mem_cons.mpr
          left
          apply Subtype.ext
          rfl
        · exact List.mem_cons_of_mem _
            (positivePhysicalSource_mem_aux_local source tail
              (fun item hitem =>
                hphysical item (List.mem_cons_of_mem head hitem))
              htail)
      next hheadNotPositive =>
        rcases List.mem_cons.mp hmem with hhead | htail
        · subst head
          exact False.elim (hheadNotPositive source.2.2)
        · exact positivePhysicalSource_mem_aux_local source tail
            (fun item hitem =>
              hphysical item (List.mem_cons_of_mem head hitem))
            htail

private theorem positivePhysicalSource_mem_local
    {S : SlabScalePair} (source : PositivePhysicalSource S) :
    source ∈ positivePhysicalSources S := by
  unfold positivePhysicalSources
  exact positivePhysicalSource_mem_aux_local source
    S.fine.physicalLabellings (fun _ hitem => hitem) source.2.1

private theorem positiveExpandedPhysicalSource_mem_local
    {S : SlabScalePair} (source : PositiveExpandedPhysicalSource S) :
    source ∈ positiveExpandedPhysicalSources S := by
  unfold positiveExpandedPhysicalSources
  apply List.mem_flatMap.mpr
  refine ⟨source.1, positivePhysicalSource_mem_local source.1, ?_⟩
  unfold positiveExpandedPhysicalSourceBlock
  apply List.mem_map.mpr
  exact ⟨source.2, List.mem_attach _ source.2, rfl⟩

private theorem binarySupportPhysicalTerm_pos_local
    {S : SlabScalePair}
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    {support : List Z4Plaq}
    (hsubset : ∀ plaquette, plaquette ∈ support →
      plaquette ∈ boundaryCompleteSlabPlaquettes S.fine.extent)
    (hnodup : support.Nodup)
    (heven : EvenFaceIncidence support) :
    (0 : Q') < S.fine.physicalTerm
      (slabBinarySupportLabelling S.fine.extent support) := by
  have hbounded : SlabFaceLabellingBounded S.fine.cutoff S.fine.extent
      (slabBinarySupportLabelling S.fine.extent support) := by
    intro faceId _
    rw [hfineCutoff]
    exact slabBinarySupportLabelling_le_one
      S.fine.extent support faceId
  have hface : (0 : Q') < slabParametricKPhysicalFaceFactor
      S.fine.coupling S.fine.cutoff S.fine.extent
      (slabBinarySupportLabelling S.fine.extent support) :=
    slabParametricKPhysicalFaceFactor_pos_of_bounded
      S.fine hfineCoupling _ hbounded
  have hlinks : 0 < slabExplicitLinkMultiplicityProduct
      S.fine.cutoff S.fine.extent
      (slabBinarySupportLabelling S.fine.extent support) :=
    slabBinarySupport_linkMultiplicityProduct_pos
      (by rw [hfineCutoff]; omega) hsubset hnodup heven
  unfold SlabPhysicalData.physicalTerm slabParametricKPhysicalTerm
  exact Q'.mul_pos hface (qOfNat_pos_of_pos_local hlinks)

/-- Pointwise face compatibility plus the endpoint's accepted coarse
intertwiner assignment gives a strictly positive literal whole-slab raw
entry. -/
def PositiveExpandedFaceCompatibleEndpointLift.toRawEndpointLift
    {S : SlabScalePair} {endpoint : SlabExpandedFineSourceEntry S.coarse}
    (lift : PositiveExpandedFaceCompatibleEndpointLift S endpoint) :
    PositiveExpandedRawEndpointLift S endpoint.1.1 where
  source := lift.source
  source_mem := lift.source_mem
  rawWeight_pos := by
    unfold wholeSlabRecouplingRawWeight
    exact Q'.mul_pos
      (wholeSlabFaceRawProduct_pos_of_pointwise
        S lift.source.1.1 endpoint.1.1 lift.faceRawWeight_pos)
      (qOfNat_pos_of_pos_local
        (attachedEndpoint_linkMultiplicityProduct_pos endpoint))

/-- Fully discrete local-channel presentation of a face-compatible endpoint
lift.  It retains a concrete pair channel at every coarse face and the three
fusion guards proving that channel is supported. -/
structure PositiveExpandedFusionChannelEndpointLift
    (S : SlabScalePair)
    (endpoint : SlabExpandedFineSourceEntry S.coarse) : Type where
  source : PositiveExpandedPhysicalSource S
  source_mem : source ∈ positiveExpandedPhysicalSources S
  faceChannel : Nat → PairChannelState
  faceChannel_mem : ∀ coarseFaceId,
    coarseFaceId ∈ S.coarse.faceEdges →
      faceChannel coarseFaceId ∈ pairChannelStateSpace S.fine.cutoff
  faceChannel_final : ∀ coarseFaceId,
    coarseFaceId ∈ S.coarse.faceEdges →
      (faceChannel coarseFaceId).2 = endpoint.1.1 coarseFaceId
  faceChannel_fusions : ∀ coarseFaceId,
    coarseFaceId ∈ S.coarse.faceEdges →
      let packet := wholeSlabFinePacket S source.1.1 coarseFaceId
      let channel := faceChannel coarseFaceId
      fusionOK packet.spin0 packet.spin1 channel.1.1 = true ∧
      fusionOK packet.spin2 packet.spin3 channel.1.2 = true ∧
        fusionOK channel.1.1 channel.1.2 channel.2 = true

private theorem faceChannel_mem_of_fusions_local
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (coarseFaceId : Nat) (channel : PairChannelState)
    (hfusions :
      let packet := wholeSlabFinePacket S fineState coarseFaceId
      fusionOK packet.spin0 packet.spin1 channel.1.1 = true ∧
        fusionOK packet.spin2 packet.spin3 channel.1.2 = true ∧
        fusionOK channel.1.1 channel.1.2 channel.2 = true) :
    channel ∈ pairChannelStateSpace S.fine.cutoff := by
  let packet := wholeSlabFinePacket S fineState coarseFaceId
  have hpacket :=
    (mem_faceSpinPacketStateSpace_iff S.fine.cutoff packet).mp
      (wholeSlabFinePacket_mem hfineMem coarseFaceId)
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
  exact (mem_pairChannelStateSpace_iff S.fine.cutoff channel).mpr
    ⟨hleftBound, hrightBound, hfinalBound⟩

private theorem fusionInd_eq_one_of_true_local
    {a b c : Nat} (h : fusionOK a b c = true) :
    fusionInd a b c = 1 := by
  unfold fusionInd
  rw [if_pos h]

private theorem packetPairChannelRawWeight_pos_of_fusions_local
    {w : Q'} (hw : (0 : Q') < w)
    (packet : FaceSpinPacket) (channel : PairChannelState)
    (hfusions :
      fusionOK packet.spin0 packet.spin1 channel.1.1 = true ∧
        fusionOK packet.spin2 packet.spin3 channel.1.2 = true ∧
        fusionOK channel.1.1 channel.1.2 channel.2 = true) :
    (0 : Q') < packetPairChannelRawWeight w packet channel := by
  unfold packetPairChannelRawWeight
  rw [fusionInd_eq_one_of_true_local hfusions.1,
    fusionInd_eq_one_of_true_local hfusions.2.1,
    fusionInd_eq_one_of_true_local hfusions.2.2]
  exact Q'.mul_pos (coeffW_pos hw channel.2) (by decide)

private theorem listQSum_member_le_local {A : Type}
    (value : A → Q') (hvalue : ∀ x, (0 : Q') ≤ value x) :
    ∀ (xs : List A) {x : A}, x ∈ xs →
      value x ≤ listQSum value xs
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, x, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst x
        exact Q'.add_le_self_of_nonneg (value head)
          (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun y _ => hvalue y))
      · have ih := listQSum_member_le_local value hvalue tail htail
        have hmono : listQSum value tail ≤
            value head + listQSum value tail := by
          have hle := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at hle
        exact Q'.le_trans' _ _ _ ih hmono

/-- At positive coarse coupling, explicit supported face channels supply the
pointwise positive fixed-final face sums required by the raw endpoint lift. -/
def PositiveExpandedFusionChannelEndpointLift.toFaceCompatibleEndpointLift
    {S : SlabScalePair} {endpoint : SlabExpandedFineSourceEntry S.coarse}
    (lift : PositiveExpandedFusionChannelEndpointLift S endpoint)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling) :
    PositiveExpandedFaceCompatibleEndpointLift S endpoint where
  source := lift.source
  source_mem := lift.source_mem
  faceRawWeight_pos := fun coarseFaceId hface => by
    let channel := lift.faceChannel coarseFaceId
    let packet := wholeSlabFinePacket S lift.source.1.1 coarseFaceId
    have hfinal := lift.faceChannel_final coarseFaceId hface
    have hselected :
        (0 : Q') <
          (if channel.2 = endpoint.1.1 coarseFaceId then
            packetPairChannelRawWeight S.coarse.coupling packet channel
          else 0) := by
      rw [if_pos hfinal]
      exact packetPairChannelRawWeight_pos_of_fusions_local
        hcoarseCoupling packet channel
        (lift.faceChannel_fusions coarseFaceId hface)
    have hle :
        (if channel.2 = endpoint.1.1 coarseFaceId then
            packetPairChannelRawWeight S.coarse.coupling packet channel
          else 0) ≤
          wholeSlabFaceRawWeight S lift.source.1.1 endpoint.1.1
            coarseFaceId := by
      unfold wholeSlabFaceRawWeight
      apply listQSum_member_le_local
      · intro candidate
        by_cases hcandidate : candidate.2 = endpoint.1.1 coarseFaceId
        · rw [if_pos hcandidate]
          exact packetPairChannelRawWeight_nonnegative
            S.coarse.coupling_nonnegative _ _
        · rw [if_neg hcandidate]
          exact Q'.le_refl' 0
      · exact lift.faceChannel_mem coarseFaceId hface
    exact Q'.pos_of_lt_of_le hselected hle

/-- Purely geometric presentation of an endpoint lift at cutoff one.  The
support is a duplicate-free closed binary surface; local channels record its
required coarse final spins.  Positivity and one accepted fine intertwiner
are reconstructed by the adapter below. -/
structure EvenBinarySupportFusionChannelEndpointLift
    (S : SlabScalePair)
    (endpoint : SlabExpandedFineSourceEntry S.coarse) : Type where
  support : List Z4Plaq
  support_subset : ∀ plaquette, plaquette ∈ support →
    plaquette ∈ boundaryCompleteSlabPlaquettes S.fine.extent
  support_nodup : support.Nodup
  support_even : EvenFaceIncidence support
  faceChannel : Nat → PairChannelState
  faceChannel_final : ∀ coarseFaceId,
    coarseFaceId ∈ S.coarse.faceEdges →
      (faceChannel coarseFaceId).2 = endpoint.1.1 coarseFaceId
  faceChannel_fusions : ∀ coarseFaceId,
    coarseFaceId ∈ S.coarse.faceEdges →
      let packet := wholeSlabFinePacket S
        (slabBinarySupportLabelling S.fine.extent support) coarseFaceId
      let channel := faceChannel coarseFaceId
      fusionOK packet.spin0 packet.spin1 channel.1.1 = true ∧
      fusionOK packet.spin2 packet.spin3 channel.1.2 = true ∧
        fusionOK channel.1.1 channel.1.2 channel.2 = true

private theorem fusionOK_add_eq_true_local (left right : Nat) :
    fusionOK left right (left + right) = true := by
  exact (fusionOK_iff_ladder left right (left + right)).2
    ⟨0, Nat.zero_le _, Nat.zero_le _, by omega⟩

def endpointFaceSpinTotal (packet : FaceSpinPacket) : Nat :=
  packet.spin0 + packet.spin1 + packet.spin2 + packet.spin3

def endpointStretchedPairChannel
    (packet : FaceSpinPacket) : PairChannelState :=
  ((packet.spin0 + packet.spin1, packet.spin2 + packet.spin3),
    endpointFaceSpinTotal packet)

/-- The canonical stretched channel of a four-spin packet satisfies all
three fusion guards. -/
private theorem stretchedPairChannel_fusions_local
    (packet : FaceSpinPacket) :
    let channel := endpointStretchedPairChannel packet
    fusionOK packet.spin0 packet.spin1 channel.1.1 = true ∧
      fusionOK packet.spin2 packet.spin3 channel.1.2 = true ∧
      fusionOK channel.1.1 channel.1.2 channel.2 = true := by
  dsimp only [endpointStretchedPairChannel, endpointFaceSpinTotal]
  exact
    ⟨fusionOK_add_eq_true_local packet.spin0 packet.spin1,
      fusionOK_add_eq_true_local packet.spin2 packet.spin3,
      by
        simpa only [Nat.add_assoc] using
          fusionOK_add_eq_true_local
            (packet.spin0 + packet.spin1)
            (packet.spin2 + packet.spin3)⟩

/-- Exact geometric reverse-lift datum.  Each coarse spin must be the number
of selected cutoff-one fine faces in its four-face dyadic block.  The
stretched pair channel is then forced and supported automatically. -/
structure EvenBinarySupportEndpointLift
    (S : SlabScalePair)
    (endpoint : SlabExpandedFineSourceEntry S.coarse) : Type where
  support : List Z4Plaq
  support_subset : ∀ plaquette, plaquette ∈ support →
    plaquette ∈ boundaryCompleteSlabPlaquettes S.fine.extent
  support_nodup : support.Nodup
  support_even : EvenFaceIncidence support
  faceSpinTotal_eq : ∀ coarseFaceId,
    coarseFaceId ∈ S.coarse.faceEdges →
      endpointFaceSpinTotal
          (wholeSlabFinePacket S
            (slabBinarySupportLabelling S.fine.extent support)
            coarseFaceId) =
        endpoint.1.1 coarseFaceId

private theorem slabSpinAtPlaquette_binarySupport_local
    {extent : Nat} {support : List Z4Plaq} {plaquette : Z4Plaq}
    (hsubset : ∀ face, face ∈ support →
      face ∈ boundaryCompleteSlabPlaquettes extent) :
    slabSpinAtPlaquette extent
        (slabBinarySupportLabelling extent support) plaquette =
      if plaquette ∈ support then 1 else 0 := by
  by_cases hslab : plaquette ∈ boundaryCompleteSlabPlaquettes extent
  · rw [slabSpinAtPlaquette_eq_of_mem hslab]
    have hindex :
        listIndexOf plaquette (boundaryCompleteSlabPlaquettes extent) ∈
          slabPhysicalFaceEdges extent := by
      unfold slabPhysicalFaceEdges
      exact List.mem_range.mpr
        (listIndexOf_lt_of_mem plaquette
          (boundaryCompleteSlabPlaquettes extent) hslab)
    rw [slabBinarySupportLabelling_eq_indicator hindex]
    have hlookup :
        slabPlaquetteAt extent
            (listIndexOf plaquette
              (boundaryCompleteSlabPlaquettes extent)) = plaquette := by
      unfold slabPlaquetteAt
      exact getD_listIndexOf_of_mem fallbackPlaquette plaquette
        (boundaryCompleteSlabPlaquettes extent) hslab
    rw [hlookup]
  · rw [slabSpinAtPlaquette_eq_zero_of_not_mem hslab]
    have hnotSupport : plaquette ∉ support := by
      intro hmem
      exact hslab (hsubset plaquette hmem)
    rw [if_neg hnotSupport]

private theorem wholeSlabFinePacket_dyadicSupportCells_local
    {S : SlabScalePair} (coarseSupport : List Z4Plaq)
    (hcoarseSubset : ∀ face, face ∈ coarseSupport →
      face ∈ boundaryCompleteSlabPlaquettes S.coarse.extent)
    (coarseFaceId : Nat) :
    wholeSlabFinePacket S
        (slabBinarySupportLabelling S.fine.extent
          (dyadicSupportCells coarseSupport)) coarseFaceId =
      ⟨if slabPlaquetteAt S.coarse.extent coarseFaceId ∈ coarseSupport
        then 1 else 0, 0, 0, 0⟩ := by
  have hfineSubset : ∀ fine, fine ∈ dyadicSupportCells coarseSupport →
      fine ∈ boundaryCompleteSlabPlaquettes S.fine.extent := by
    intro fine hfine
    rw [S.fine_extent]
    exact dyadicSupportCells_subset_boundaryCompleteFineSlab
      hcoarseSubset fine hfine
  have hspin :
      slabSpinAtPlaquette S.fine.extent
          (slabBinarySupportLabelling S.fine.extent
            (dyadicSupportCells coarseSupport)) =
        fun fine =>
          (supportCoefficient
            (dyadicSupportCells coarseSupport) fine).toNat := by
    funext fine
    rw [slabSpinAtPlaquette_binarySupport_local hfineSubset]
    unfold supportCoefficient
    by_cases hmem : fine ∈ dyadicSupportCells coarseSupport <;>
      simp [hmem]
  unfold wholeSlabFinePacket
  rw [hspin]
  exact dyadicFaceSpinPacket_dyadicSupportCells coarseSupport
    (slabPlaquetteAt S.coarse.extent coarseFaceId)

/-- A concrete coarse subclass for which literal four-cell subdivision is a
complete exact endpoint lift.  The coarse endpoint is the zero-one indicator
of a duplicate-free closed slab surface.  Literal subdivision then produces
one occupied nondegenerate fine face in each selected coarse fibre. -/
structure ClosedBinaryCoarseEndpointPresentation
    (S : SlabScalePair)
    (endpoint : SlabExpandedFineSourceEntry S.coarse) : Type where
  support : List Z4Plaq
  support_subset : ∀ face, face ∈ support →
    face ∈ boundaryCompleteSlabPlaquettes S.coarse.extent
  support_nodup : support.Nodup
  support_even : EvenFaceIncidence support
  endpoint_spin : ∀ coarseFaceId,
    coarseFaceId ∈ S.coarse.faceEdges →
      (if slabPlaquetteAt S.coarse.extent coarseFaceId ∈ support
        then 1 else 0) = endpoint.1.1 coarseFaceId

/-- Literal four-cell subdivision constructs the exact fine endpoint lift
for every closed binary coarse endpoint presentation. -/
def ClosedBinaryCoarseEndpointPresentation.toEvenBinarySupportEndpointLift
    {S : SlabScalePair}
    {endpoint : SlabExpandedFineSourceEntry S.coarse}
    (presentation : ClosedBinaryCoarseEndpointPresentation S endpoint) :
    EvenBinarySupportEndpointLift S endpoint where
  support := dyadicSupportCells presentation.support
  support_subset := by
    intro fine hfine
    rw [S.fine_extent]
    exact dyadicSupportCells_subset_boundaryCompleteFineSlab
      presentation.support_subset fine hfine
  support_nodup :=
    dyadicSupportCells_nodup presentation.support_nodup
  support_even :=
    dyadicSupportCells_preserves_evenFaceIncidence
      presentation.support_nodup presentation.support_even
  faceSpinTotal_eq := fun coarseFaceId hface => by
    rw [wholeSlabFinePacket_dyadicSupportCells_local
      presentation.support presentation.support_subset coarseFaceId]
    change
      (if slabPlaquetteAt S.coarse.extent coarseFaceId ∈
          presentation.support then 1 else 0) =
        endpoint.1.1 coarseFaceId
    exact presentation.endpoint_spin coarseFaceId hface

/-- Exact dyadic block counts determine canonical supported face channels. -/
def EvenBinarySupportEndpointLift.toFusionChannelLift
    {S : SlabScalePair} {endpoint : SlabExpandedFineSourceEntry S.coarse}
    (lift : EvenBinarySupportEndpointLift S endpoint) :
    EvenBinarySupportFusionChannelEndpointLift S endpoint where
  support := lift.support
  support_subset := lift.support_subset
  support_nodup := lift.support_nodup
  support_even := lift.support_even
  faceChannel := fun coarseFaceId =>
    endpointStretchedPairChannel
      (wholeSlabFinePacket S
        (slabBinarySupportLabelling S.fine.extent lift.support)
        coarseFaceId)
  faceChannel_final := fun coarseFaceId hface => by
    exact lift.faceSpinTotal_eq coarseFaceId hface
  faceChannel_fusions := fun coarseFaceId _ =>
    stretchedPairChannel_fusions_local
      (wholeSlabFinePacket S
        (slabBinarySupportLabelling S.fine.extent lift.support)
        coarseFaceId)

/-- At cutoff one and positive fine coupling, a closed binary support
constructively supplies the enumerated positive source and an accepted fine
intertwiner assignment required by the fusion-channel lift. -/
def EvenBinarySupportFusionChannelEndpointLift.toPositiveExpandedLift
    {S : SlabScalePair} {endpoint : SlabExpandedFineSourceEntry S.coarse}
    (lift : EvenBinarySupportFusionChannelEndpointLift S endpoint)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling) :
    PositiveExpandedFusionChannelEndpointLift S endpoint := by
  let fineState :=
    slabBinarySupportLabelling S.fine.extent lift.support
  have hfineMem : fineState ∈ S.fine.physicalLabellings := by
    unfold SlabPhysicalData.physicalLabellings
      SlabPhysicalData.faceEdges
    exact slabBinarySupportLabelling_mem
      (by rw [hfineCutoff]; omega) lift.support
  have hpositive : (0 : Q') < S.fine.physicalTerm fineState := by
    exact binarySupportPhysicalTerm_pos_local
      hfineCutoff hfineCoupling lift.support_subset
        lift.support_nodup lift.support_even
  let positiveSource : PositivePhysicalSource S :=
    ⟨fineState, hfineMem, hpositive⟩
  let fineWitness :=
    positivePhysicalTermFineFusionWitness
      S.fine fineState hpositive
  let expandedSource : PositiveExpandedPhysicalSource S :=
    ⟨positiveSource, ⟨fineWitness.1, fineWitness.2⟩⟩
  exact
    { source := expandedSource
      source_mem := positiveExpandedPhysicalSource_mem_local expandedSource
      faceChannel := lift.faceChannel
      faceChannel_mem := fun coarseFaceId hface =>
        faceChannel_mem_of_fusions_local hfineMem coarseFaceId
          (lift.faceChannel coarseFaceId)
          (lift.faceChannel_fusions coarseFaceId hface)
      faceChannel_final := lift.faceChannel_final
      faceChannel_fusions := fun coarseFaceId hface => by
        simpa only [expandedSource, positiveSource, fineState] using
          lift.faceChannel_fusions coarseFaceId hface }

/-- The remaining finite combinatorial coverage target: every attached coarse
expanded endpoint has a positive raw preimage in the enumerated fine carrier.
The attachment supplies the accepted coarse intertwiner assignment actually
seen by the receiver cells and excludes irrelevant link-inadmissible bounded
labellings. -/
structure PositiveExpandedRawEndpointCoverage (S : SlabScalePair) : Type where
  lift : ∀ endpoint : SlabExpandedFineSourceEntry S.coarse,
    PositiveExpandedRawEndpointLift S endpoint.1.1

/-- Producer-facing version of endpoint coverage.  It asks only for the
fine source and pointwise local face compatibility; accepted coarse-link
coherence is recovered from the attached endpoint itself. -/
structure PositiveExpandedFaceCompatibleEndpointCoverage
    (S : SlabScalePair) : Type where
  lift : ∀ endpoint : SlabExpandedFineSourceEntry S.coarse,
    PositiveExpandedFaceCompatibleEndpointLift S endpoint

def PositiveExpandedFaceCompatibleEndpointCoverage.toRawEndpointCoverage
    {S : SlabScalePair}
    (coverage : PositiveExpandedFaceCompatibleEndpointCoverage S) :
    PositiveExpandedRawEndpointCoverage S where
  lift := fun endpoint => (coverage.lift endpoint).toRawEndpointLift

/-- The preferred finite producer: explicit supported local channels for
every attached coarse endpoint. -/
structure PositiveExpandedFusionChannelEndpointCoverage
    (S : SlabScalePair) : Type where
  lift : ∀ endpoint : SlabExpandedFineSourceEntry S.coarse,
    PositiveExpandedFusionChannelEndpointLift S endpoint

def PositiveExpandedFusionChannelEndpointCoverage.toFaceCompatibleCoverage
    {S : SlabScalePair}
    (coverage : PositiveExpandedFusionChannelEndpointCoverage S)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling) :
    PositiveExpandedFaceCompatibleEndpointCoverage S where
  lift := fun endpoint =>
    (coverage.lift endpoint).toFaceCompatibleEndpointLift hcoarseCoupling

/-- Geometric endpoint coverage: every attached coarse endpoint is realized
by one closed cutoff-one binary support and explicit supported face channels. -/
structure EvenBinarySupportFusionChannelEndpointCoverage
    (S : SlabScalePair) : Type where
  lift : ∀ endpoint : SlabExpandedFineSourceEntry S.coarse,
    EvenBinarySupportFusionChannelEndpointLift S endpoint

def EvenBinarySupportFusionChannelEndpointCoverage.toPositiveExpandedCoverage
    {S : SlabScalePair}
    (coverage : EvenBinarySupportFusionChannelEndpointCoverage S)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling) :
    PositiveExpandedFusionChannelEndpointCoverage S where
  lift := fun endpoint =>
    (coverage.lift endpoint).toPositiveExpandedLift
      hfineCutoff hfineCoupling

/-- Pure geometric coverage by closed fine binary supports with the exact
four-face dyadic block count prescribed by every attached coarse endpoint. -/
structure EvenBinarySupportEndpointCoverage
    (S : SlabScalePair) : Type where
  lift : ∀ endpoint : SlabExpandedFineSourceEntry S.coarse,
    EvenBinarySupportEndpointLift S endpoint

def EvenBinarySupportEndpointCoverage.toFusionChannelCoverage
    {S : SlabScalePair}
    (coverage : EvenBinarySupportEndpointCoverage S) :
    EvenBinarySupportFusionChannelEndpointCoverage S where
  lift := fun endpoint =>
    (coverage.lift endpoint).toFusionChannelLift

/-! ## 2. Assemble two one-replica lifts into supported four-cell paths -/

private theorem sourceReceiver_physicalPair_mem
    {S : SlabScalePair} {root target : Nat}
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (hreceiver : receiver ∈
      slabObservableFourCellSourcePairs S.coarse root target) :
    (receiver.1.1.1, receiver.2.1.1) ∈
      pushedFaceRawFourCellSourcePairs (S := S) root target := by
  have hcells := (mem_cartesian_iff _ _ receiver).mp hreceiver
  apply (mem_cartesian_iff _ _
    (receiver.1.1.1, receiver.2.1.1)).mpr
  constructor
  · apply List.mem_filter.mpr
    refine ⟨(mem_slabExpandedFineSources_iff.mp
      receiver.1.source_mem_expanded).1, ?_⟩
    apply (Bool.and_eq_true _ _).mpr
    constructor
    · unfold slabPhysicalFacePositiveB
      exact decide_eq_true receiver.1.source_positive
    · simpa only [SlabObservablePositiveSourceEntry.facePositiveB,
        slabPhysicalFacePositiveB] using
        (List.mem_filter.mp hcells.1).2
  · apply List.mem_filter.mpr
    refine ⟨(mem_slabExpandedFineSources_iff.mp receiver.2.2).1, ?_⟩
    simpa only [SlabExpandedFineSourceEntry.facePositiveB,
      slabPhysicalFacePositiveB] using
      (List.mem_filter.mp hcells.2).2

private theorem targetReceiver_swappedPhysicalPair_mem
    {S : SlabScalePair} {root target : Nat}
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (hreceiver : receiver ∈
      slabObservableFourCellTargetPairs S.coarse root target) :
    (receiver.2.1.1, receiver.1.1.1) ∈
      pushedFaceRawFourCellTargetPairs (S := S) root target := by
  have hcells := (mem_cartesian_iff _ _ receiver).mp hreceiver
  apply (mem_cartesian_iff _ _
    (receiver.2.1.1, receiver.1.1.1)).mpr
  constructor
  · apply List.mem_filter.mpr
    refine ⟨(mem_slabExpandedFineSources_iff.mp receiver.2.2).1, ?_⟩
    simpa only [SlabExpandedFineSourceEntry.facePositiveB,
      slabPhysicalFacePositiveB, Bool.and_comm] using
      (List.mem_filter.mp hcells.2).2
  · apply List.mem_filter.mpr
    refine ⟨(mem_slabExpandedFineSources_iff.mp
      receiver.1.source_mem_expanded).1, ?_⟩
    apply (Bool.and_eq_true _ _).mpr
    constructor
    · unfold slabPhysicalFacePositiveB
      exact decide_eq_true receiver.1.source_positive
    · simpa only [SlabObservablePositiveSourceEntry.facePositiveB,
        slabPhysicalFacePositiveB] using
        (List.mem_filter.mp hcells.1).2

/-- Two one-replica endpoint lifts construct an enumerated supported source
path whose physical receiver endpoints are the requested pair. -/
def positiveExpandedFourCellSourceSupportedPathAtReceiver
    {S : SlabScalePair} {root target : Nat}
    (coverage : PositiveExpandedRawEndpointCoverage S)
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (hreceiver : receiver ∈
      slabObservableFourCellSourcePairs S.coarse root target) :
    {supported : PositiveExpandedFourCellSourceSupportedPath S root target //
      supported ∈ positiveExpandedFourCellSourceSupportedPaths
        S root target} := by
  let leftPhysical := receiver.1.1.1
  let rightPhysical := receiver.2.1.1
  have hphysicalPair := sourceReceiver_physicalPair_mem receiver hreceiver
  let leftEndpoint : SlabExpandedFineSourceEntry S.coarse :=
    ⟨receiver.1.1, receiver.1.source_mem_expanded⟩
  let leftLift := coverage.lift leftEndpoint
  let rightLift := coverage.lift receiver.2
  let path : PositiveExpandedPushedPhysicalTwoReplicaPath S :=
    ((leftPhysical, rightPhysical), (leftLift.source, rightLift.source))
  have hsourcePair : (leftLift.source, rightLift.source) ∈
      positiveExpandedPhysicalSourcePairs S := by
    apply (mem_cartesian_iff _ _ _).mpr
    exact ⟨leftLift.source_mem, rightLift.source_mem⟩
  have hpath : path ∈
      positiveExpandedPushedFaceRawFourCellSourcePaths
        S root target := by
    apply (mem_cartesian_iff _ _ path).mpr
    exact ⟨hphysicalPair, hsourcePair⟩
  have hsupport : positiveExpandedPathRawSupportedB S path = true := by
    unfold positiveExpandedPathRawSupportedB
    apply (Bool.and_eq_true _ _).mpr
    exact ⟨decide_eq_true leftLift.rawWeight_pos,
      decide_eq_true rightLift.rawWeight_pos⟩
  have hfiltered : path ∈
      (positiveExpandedPushedFaceRawFourCellSourcePaths
        S root target).filter (positiveExpandedPathRawSupportedB S) :=
    List.mem_filter.mpr ⟨hpath, hsupport⟩
  let item : {candidate // candidate ∈
      (positiveExpandedPushedFaceRawFourCellSourcePaths
        S root target).filter (positiveExpandedPathRawSupportedB S)} :=
    ⟨path, hfiltered⟩
  let supported := positiveExpandedFourCellSourceSupportedPathOfAttached
    S root target item
  refine ⟨supported, ?_⟩
  unfold positiveExpandedFourCellSourceSupportedPaths
  apply List.mem_map.mpr
  exact ⟨item, List.mem_attach _ _, rfl⟩

/-- The analogous two lifts construct the swapped supported path used by the
opposite target-cell receiver orientation. -/
def positiveExpandedFourCellTargetSupportedPathAtReceiver
    {S : SlabScalePair} {root target : Nat}
    (coverage : PositiveExpandedRawEndpointCoverage S)
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (hreceiver : receiver ∈
      slabObservableFourCellTargetPairs S.coarse root target) :
    {supported : PositiveExpandedFourCellTargetSupportedPath S root target //
      supported ∈ positiveExpandedFourCellTargetSupportedPaths
        S root target} := by
  let leftPhysical := receiver.2.1.1
  let rightPhysical := receiver.1.1.1
  have hphysicalPair :=
    targetReceiver_swappedPhysicalPair_mem receiver hreceiver
  let rightEndpoint : SlabExpandedFineSourceEntry S.coarse :=
    ⟨receiver.1.1, receiver.1.source_mem_expanded⟩
  let leftLift := coverage.lift receiver.2
  let rightLift := coverage.lift rightEndpoint
  let path : PositiveExpandedPushedPhysicalTwoReplicaPath S :=
    ((leftPhysical, rightPhysical), (leftLift.source, rightLift.source))
  have hsourcePair : (leftLift.source, rightLift.source) ∈
      positiveExpandedPhysicalSourcePairs S := by
    apply (mem_cartesian_iff _ _ _).mpr
    exact ⟨leftLift.source_mem, rightLift.source_mem⟩
  have hpath : path ∈
      positiveExpandedPushedFaceRawFourCellTargetPaths
        S root target := by
    apply (mem_cartesian_iff _ _ path).mpr
    exact ⟨hphysicalPair, hsourcePair⟩
  have hsupport : positiveExpandedPathRawSupportedB S path = true := by
    unfold positiveExpandedPathRawSupportedB
    apply (Bool.and_eq_true _ _).mpr
    exact ⟨decide_eq_true leftLift.rawWeight_pos,
      decide_eq_true rightLift.rawWeight_pos⟩
  have hfiltered : path ∈
      (positiveExpandedPushedFaceRawFourCellTargetPaths
        S root target).filter (positiveExpandedPathRawSupportedB S) :=
    List.mem_filter.mpr ⟨hpath, hsupport⟩
  let item : {candidate // candidate ∈
      (positiveExpandedPushedFaceRawFourCellTargetPaths
        S root target).filter (positiveExpandedPathRawSupportedB S)} :=
    ⟨path, hfiltered⟩
  let supported := positiveExpandedFourCellTargetSupportedPathOfAttached
    S root target item
  refine ⟨supported, ?_⟩
  unfold positiveExpandedFourCellTargetSupportedPaths
  apply List.mem_map.mpr
  exact ⟨item, List.mem_attach _ _, rfl⟩

/-! ## 3. Full assignment-saturated coverage and zero unreachable mass -/

theorem sourceReceiver_mem_assignmentSaturatedImage_of_endpointCoverage
    {S : SlabScalePair} {root target : Nat}
    (coverage : PositiveExpandedRawEndpointCoverage S)
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (hreceiver : receiver ∈
      slabObservableFourCellSourcePairs S.coarse root target) :
    receiver ∈
      positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage
        S root target := by
  let lift := positiveExpandedFourCellSourceSupportedPathAtReceiver
    coverage receiver hreceiver
  apply
    (mem_positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage_iff_physical
      S root target receiver).mpr
  exact ⟨lift.1, lift.2, rfl, rfl⟩

theorem targetReceiver_mem_assignmentSaturatedImage_of_endpointCoverage
    {S : SlabScalePair} {root target : Nat}
    (coverage : PositiveExpandedRawEndpointCoverage S)
    (receiver : SlabObservableTwoReplicaPair S.coarse root)
    (hreceiver : receiver ∈
      slabObservableFourCellTargetPairs S.coarse root target) :
    receiver ∈
      positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage
        S root target := by
  let lift := positiveExpandedFourCellTargetSupportedPathAtReceiver
    coverage receiver hreceiver
  apply
    (mem_positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage_iff_physical
      S root target receiver).mpr
  exact ⟨lift.1, lift.2, rfl, rfl⟩

private theorem complementFilter_eq_nil_of_subset
    {A : Type} [DecidableEq A] (image : List A) :
    ∀ items : List A,
      (∀ item, item ∈ items → item ∈ image) →
      items.filter (fun item => !(decide (item ∈ image))) = []
  | [], _ => rfl
  | head :: tail, hsubset => by
      have hhead : head ∈ image :=
        hsubset head List.mem_cons_self
      have htail : ∀ item, item ∈ tail → item ∈ image :=
        fun item hitem =>
          hsubset item (List.mem_cons_of_mem head hitem)
      simp only [List.filter_cons, decide_eq_true hhead, Bool.not_true,
        Bool.false_eq_true, if_false]
      exact complementFilter_eq_nil_of_subset image tail htail

/-- Raw lifts over the exact attached coarse endpoint carrier make the
physical unreachable receiver mass exactly zero. -/
theorem actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass_eqv_zero_of_endpointCoverage
    (S : SlabScalePair) (root target : Nat)
    (coverage : PositiveExpandedRawEndpointCoverage S) :
    actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass
        S root target ≈ 0 := by
  have hsource :
      (slabObservableFourCellSourcePairs S.coarse root target).filter
          (fun receiver => !(decide
            (receiver ∈
              positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage
                S root target))) = [] :=
    complementFilter_eq_nil_of_subset
      (positiveExpandedFourCellSourceAssignmentSaturatedReceiverImage
        S root target)
      (slabObservableFourCellSourcePairs S.coarse root target)
      (fun receiver hreceiver =>
        sourceReceiver_mem_assignmentSaturatedImage_of_endpointCoverage
          coverage receiver hreceiver)
  have htarget :
      (slabObservableFourCellTargetPairs S.coarse root target).filter
          (fun receiver => !(decide
            (receiver ∈
              positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage
                S root target))) = [] :=
    complementFilter_eq_nil_of_subset
      (positiveExpandedFourCellTargetAssignmentSaturatedReceiverImage
        S root target)
      (slabObservableFourCellTargetPairs S.coarse root target)
      (fun receiver hreceiver =>
        targetReceiver_mem_assignmentSaturatedImage_of_endpointCoverage
          coverage receiver hreceiver)
  unfold actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass
    actualPositiveExpandedAssignmentSaturatedSourceUnreachableReceiverMass
    actualPositiveExpandedAssignmentSaturatedTargetUnreachableReceiverMass
  rw [hsource, htarget]
  exact Q'.eqv_of_eq (Q'.zero_add' 0)

theorem actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass_le_of_endpointCoverage
    (S : SlabScalePair) (root target : Nat)
    (coverage : PositiveExpandedRawEndpointCoverage S)
    (budget : Q') (hbudget : (0 : Q') ≤ budget) :
    actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass
        S root target ≤ budget := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass_eqv_zero_of_endpointCoverage
        S root target coverage))
    hbudget

/-! ## 4. Matched-AF exact-coverage compiler -/

/-- Producer-facing matched-AF inputs when finite endpoint raw-support
coverage has been constructed at every scale. -/
structure MatchedShiftedAFAssignmentSaturatedCoveredVariationEndpointCoverageQuadraticCostControl
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (C : AFTrajectoryCertificate)
    (coupling : Nat → Q')
    (coupling_pos : ∀ scale, (0 : Q') < coupling scale)
    (coupling_le_window : ∀ scale, coupling scale ≤ law.g₁)
    (identification : ShiftedAFTrajectoryIdentification C coupling)
    (nested : NestedCutoffOneFaceGeometry) : Type where
  start : Nat
  spacingFloor : Q'
  spacingFloor_pos : (0 : Q') < spacingFloor
  mismatchQuadraticCeiling : Q'
  mismatchQuadraticCeiling_pos : (0 : Q') < mismatchQuadraticCeiling
  coveredVariationQuadraticCeiling : Q'
  coveredVariationQuadraticCeiling_pos :
    (0 : Q') < coveredVariationQuadraticCeiling
  spacingQuadratic_lower : ∀ scale : Nat, start ≤ scale →
    spacingFloor * (coupling scale * coupling scale) ≤
      spacing.a (coupling scale)
  rawMismatch_quadratic_le : ∀ scale : Nat, start ≤ scale →
    rawMismatchBudget
        (matchedShiftedAFPhysicalObservableRefinementSchedule
          family law spacing C coupling coupling_pos coupling_le_window
          identification nested)
        scale ≤
      mismatchQuadraticCeiling * (coupling scale * coupling scale)
  coveredVariation_quadratic_le : ∀ scale : Nat, start ≤ scale →
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let root := (schedule.faceMap scale).coarseRoot
    let target := (schedule.faceMap scale).coarseTarget
    actualPositiveExpandedAssignmentSaturatedCoveredCoarseNormalizedVariationL1
          S rfl (schedule.effectiveCoupling_pos scale) root target ≤
      (coveredVariationQuadraticCeiling *
          (coupling scale * coupling scale)) *
        (S.coarse.physicalPartition * S.coarse.physicalPartition)
  endpointCoverage : ∀ scale : Nat, start ≤ scale →
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    EvenBinarySupportEndpointCoverage
      (schedule.scalePair scale)

namespace MatchedShiftedAFAssignmentSaturatedCoveredVariationEndpointCoverageQuadraticCostControl

variable
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {C : AFTrajectoryCertificate}
    {coupling : Nat → Q'}
    {coupling_pos : ∀ scale, (0 : Q') < coupling scale}
    {coupling_le_window : ∀ scale, coupling scale ≤ law.g₁}
    {identification : ShiftedAFTrajectoryIdentification C coupling}
    {nested : NestedCutoffOneFaceGeometry}

/-- Exact endpoint coverage supplies a zero unreachable mass; coefficient
one is a harmless positive ceiling required by the downstream interface. -/
def toCoveredVariationUnreachableMassQuadraticCostControl
    (control :
      MatchedShiftedAFAssignmentSaturatedCoveredVariationEndpointCoverageQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) :
    MatchedShiftedAFAssignmentSaturatedCoveredVariationUnreachableMassQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested where
  start := control.start
  spacingFloor := control.spacingFloor
  spacingFloor_pos := control.spacingFloor_pos
  mismatchQuadraticCeiling := control.mismatchQuadraticCeiling
  mismatchQuadraticCeiling_pos := control.mismatchQuadraticCeiling_pos
  coveredVariationQuadraticCeiling :=
    control.coveredVariationQuadraticCeiling
  coveredVariationQuadraticCeiling_pos :=
    control.coveredVariationQuadraticCeiling_pos
  unreachableMassQuadraticCeiling := 1
  unreachableMassQuadraticCeiling_pos := by decide
  spacingQuadratic_lower := control.spacingQuadratic_lower
  rawMismatch_quadratic_le := control.rawMismatch_quadratic_le
  coveredVariation_quadratic_le := control.coveredVariation_quadratic_le
  unreachableMass_quadratic_le := fun scale hscale => by
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let root := (schedule.faceMap scale).coarseRoot
    let target := (schedule.faceMap scale).coarseTarget
    let fusionCoverage :=
      (control.endpointCoverage scale hscale).toFusionChannelCoverage
    let positiveCoverage :=
      fusionCoverage.toPositiveExpandedCoverage rfl
        (schedule.fineCoupling_pos scale)
    apply
      actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass_le_of_endpointCoverage
        S root target
        (positiveCoverage.toFaceCompatibleCoverage
          (schedule.effectiveCoupling_pos scale)).toRawEndpointCoverage
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide)
        (Q'.mul_nonneg _ _
          (Q'.le_of_lt (coupling_pos scale))
          (Q'.le_of_lt (coupling_pos scale))))
      (Q'.mul_nonneg _ _
        (Q'.le_of_lt
          (slabParametricKPhysicalPartition_pos
            S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent))
        (Q'.le_of_lt
          (slabParametricKPhysicalPartition_pos
            S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent)))

def toCovarianceRawCrossSeparatedLinearRawTransportTail
    (control :
      MatchedShiftedAFAssignmentSaturatedCoveredVariationEndpointCoverageQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) :=
  control.toCoveredVariationUnreachableMassQuadraticCostControl.toCovarianceRawCrossSeparatedLinearRawTransportTail

def toConnectedSeparatedLinearRawTransportTail
    (control :
      MatchedShiftedAFAssignmentSaturatedCoveredVariationEndpointCoverageQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) :=
  control.toCoveredVariationUnreachableMassQuadraticCostControl.toConnectedSeparatedLinearRawTransportTail

theorem fineCovariance_le_anchorRate_add_epsilon
    (control :
      MatchedShiftedAFAssignmentSaturatedCoveredVariationEndpointCoverageQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      control.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    schedule.fineCovariance scale ≤ schedule.anchorRate scale + epsilon :=
  control.toCoveredVariationUnreachableMassQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end MatchedShiftedAFAssignmentSaturatedCoveredVariationEndpointCoverageQuadraticCostControl

#print axioms PositiveExpandedRawEndpointCoverage
#print axioms attachedEndpoint_linkMultiplicityProduct_pos
#print axioms PositiveExpandedFaceCompatibleEndpointLift.toRawEndpointLift
#print axioms PositiveExpandedFaceCompatibleEndpointCoverage.toRawEndpointCoverage
#print axioms PositiveExpandedFusionChannelEndpointLift.toFaceCompatibleEndpointLift
#print axioms PositiveExpandedFusionChannelEndpointCoverage.toFaceCompatibleCoverage
#print axioms EvenBinarySupportFusionChannelEndpointLift.toPositiveExpandedLift
#print axioms EvenBinarySupportFusionChannelEndpointCoverage.toPositiveExpandedCoverage
#print axioms ClosedBinaryCoarseEndpointPresentation
#print axioms ClosedBinaryCoarseEndpointPresentation.toEvenBinarySupportEndpointLift
#print axioms EvenBinarySupportEndpointLift.toFusionChannelLift
#print axioms EvenBinarySupportEndpointCoverage.toFusionChannelCoverage
#print axioms positiveExpandedFourCellSourceSupportedPathAtReceiver
#print axioms positiveExpandedFourCellTargetSupportedPathAtReceiver
#print axioms sourceReceiver_mem_assignmentSaturatedImage_of_endpointCoverage
#print axioms targetReceiver_mem_assignmentSaturatedImage_of_endpointCoverage
#print axioms actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass_eqv_zero_of_endpointCoverage
#print axioms MatchedShiftedAFAssignmentSaturatedCoveredVariationEndpointCoverageQuadraticCostControl.toCoveredVariationUnreachableMassQuadraticCostControl
#print axioms MatchedShiftedAFAssignmentSaturatedCoveredVariationEndpointCoverageQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedEndpointLiftCoverage
