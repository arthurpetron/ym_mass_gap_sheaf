/-
# The joint BF4 carrier strictly enlarges closed binary sheets

The cutoff-two row in `BF4SU2OuterBinaryMulticoverNoGo` has positive
physical weight but no decomposition into closed binary face sheets.  This
file proves that the literal global BF4 joint carrier nevertheless contains
that same row.

The reason is geometric and exact.  None of the seventeen excited fine
plaquettes lies in a retained dyadic coarse-face fibre, so every retained
four-spin packet is the vacuum packet.  The shared coarse vacuum target,
vacuum face channel, and vacuum link intertwiners therefore form a genuine
`WholeSlabJointChannelSelection`.  Completeness of the finite joint-carrier
enumeration turns it into an actual enumerated code.

Thus the carrier enlargement is strict on physical data: it preserves
coherent coarse channel/intertwiner information without demanding a global
colouring by closed binary sheets.

## Axiom gate

Finite exact geometry and rational SU(2) identities only.  No
`Classical.*`, `sorry`, `native_decide`, custom axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4SU2OuterBinaryMulticoverNoGo
import YMGap.Continuum.BF4SU2OuterJointCarrierEnumeration

namespace YMGap.Continuum.BF4SU2OuterJointCarrierStrictEnlargement

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2OuterBinaryLayerCounterexample
open YMGap.Continuum.BF4SU2OuterBinaryLayerReduction
open YMGap.Continuum.BF4SU2OuterBinaryMulticoverReduction
open YMGap.Continuum.BF4SU2OuterBinaryMulticoverNoGo
open YMGap.Continuum.BF4SU2OuterJointCarrierEnumeration
open YMGap.Continuum.BF4SU2OuterPositiveRowClosureReduction
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FusionSupportAddition
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4DyadicModTwoCellularKernel
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence

/-! ## 1. Every retained packet is vacuum -/

/-- Every displayed excited face is dyadically degenerate: at least one of
its two spanning coordinates is even. -/
theorem normalityCounterSupport_degenerate
    (plaquette : Z4Plaq)
    (hplaquette : plaquette ∈ normalityCounterSupport) :
    dyadicPlaquetteNondegenerateB plaquette = false := by
  simp only [normalityCounterSupport, List.mem_cons,
    List.not_mem_nil, or_false] at hplaquette
  rcases hplaquette with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

private theorem normalityCounterPreimage_not_mem_support
    {coarsePlaquette finePlaquette : Z4Plaq}
    (hpreimage :
      finePlaquette ∈ dyadicFacePreimages coarsePlaquette) :
    finePlaquette ∉ normalityCounterSupport := by
  intro hsupport
  have hdegenerate :=
    normalityCounterSupport_degenerate finePlaquette hsupport
  have hnondegenerate :=
    (facePreimage_is_nondegenerate_projection hpreimage).1
  rw [hdegenerate] at hnondegenerate
  cases hnondegenerate

private theorem normalityCounterSpin_zero_of_not_mem_support
    (finePlaquette : Z4Plaq)
    (hnotSupport :
      finePlaquette ∉ normalityCounterSupport) :
    slabSpinAtPlaquette
        3 normalityCounterState finePlaquette = 0 := by
  by_cases hslab :
      finePlaquette ∈ boundaryCompleteSlabPlaquettes 3
  · rw [slabSpinAtPlaquette_eq_of_mem hslab]
    let faceId :=
      listIndexOf finePlaquette
        (boundaryCompleteSlabPlaquettes 3)
    have hphysical :
        faceId ∈ slabPhysicalFaceEdges 3 := by
      unfold faceId slabPhysicalFaceEdges
      exact List.mem_range.mpr
        (listIndexOf_lt_of_mem finePlaquette
          (boundaryCompleteSlabPlaquettes 3) hslab)
    have hlookup :
        slabPlaquetteAt 3 faceId = finePlaquette := by
      unfold faceId slabPlaquetteAt
      exact getD_listIndexOf_of_mem
        fallbackPlaquette finePlaquette
        (boundaryCompleteSlabPlaquettes 3) hslab
    unfold normalityCounterState normalityCounterIndicator
      addEdgeLabelling
    rw [slabBinarySupportLabelling_eq_indicator
      hphysical, hlookup]
    simp [hnotSupport]
  · exact slabSpinAtPlaquette_eq_zero_of_not_mem hslab

private theorem normalityCounterSpin_zero_of_nondegenerate
    (finePlaquette : Z4Plaq)
    (hnondegenerate :
      dyadicPlaquetteNondegenerateB finePlaquette = true) :
    slabSpinAtPlaquette
        3 normalityCounterState finePlaquette = 0 := by
  apply normalityCounterSpin_zero_of_not_mem_support
  intro hsupport
  have hdegenerate :=
    normalityCounterSupport_degenerate
      finePlaquette hsupport
  rw [hdegenerate] at hnondegenerate
  cases hnondegenerate

/-- Exact BF4 geometry: every retained dyadic face packet of the
seventeen-face state is the vacuum packet. -/
theorem normalityCounterRetainedPacket_vacuum_all
    (faceId : Nat) :
    wholeSlabFinePacket
        counterScalePair normalityCounterState faceId =
      zeroFaceSpinPacket := by
  change
    dyadicFaceSpinPacket
        (slabSpinAtPlaquette 3 normalityCounterState)
        (slabPlaquetteAt 1 faceId) =
      zeroFaceSpinPacket
  unfold dyadicFaceSpinPacket zeroFaceSpinPacket
  obtain ⟨⟨a, b, c, d⟩, plane⟩ :=
    slabPlaquetteAt 1 faceId
  cases plane <;>
    simp only [dyadicFacePreimages, List.getD_cons_zero,
      List.getD_cons_succ] <;>
    rw [normalityCounterSpin_zero_of_nondegenerate _ (by
          simp [dyadicPlaquetteNondegenerateB,
            vertexCoord, dirsOf]),
      normalityCounterSpin_zero_of_nondegenerate _ (by
          simp [dyadicPlaquetteNondegenerateB,
            vertexCoord, dirsOf]),
      normalityCounterSpin_zero_of_nondegenerate _ (by
          simp [dyadicPlaquetteNondegenerateB,
            vertexCoord, dirsOf]),
      normalityCounterSpin_zero_of_nondegenerate _ (by
          simp [dyadicPlaquetteNondegenerateB,
            vertexCoord, dirsOf])]

theorem normalityCounterRetainedPacket_vacuum
    (faceId : Nat)
    (_hface : faceId ∈ counterScalePair.coarse.faceEdges) :
    wholeSlabFinePacket
        counterScalePair normalityCounterState faceId =
      zeroFaceSpinPacket :=
  normalityCounterRetainedPacket_vacuum_all faceId

/-! ## 2. A literal coherent joint selection -/

def normalityCounterVacuumFaceChannel :
    Nat → PairChannelState :=
  fun _ => zeroPairChannelState

/-- The physical no-multicover row has a coherent joint-carrier witness:
vacuum coarse target, vacuum final channels, and positive vacuum link
intertwiners. -/
def normalityCounterJointSelection :
    WholeSlabJointChannelSelection
      counterScalePair normalityCounterState where
  coarseTarget := zeroEdgeLabelling
  coarseTarget_mem :=
    zeroEdgeLabelling_mem_slab counterScalePair.coarse
  faceChannel := normalityCounterVacuumFaceChannel
  faceChannel_mem := by
    intro faceId hface
    unfold normalityCounterVacuumFaceChannel
      zeroPairChannelState
    apply
      (mem_pairChannelStateSpace_iff
        counterScalePair.fine.cutoff
        ((0, 0), 0)).mpr
    exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩
  faceChannel_final := by
    intro faceId hface
    rfl
  faceChannel_positive := by
    intro faceId hface
    rw [normalityCounterRetainedPacket_vacuum faceId hface]
    unfold normalityCounterVacuumFaceChannel
      zeroPairChannelState zeroFaceSpinPacket
      packetPairChannelRawWeight
    simp only [coeffW_zero,
      fusionInd_zero_diag_self]
    decide
  coarseLink_positive := by
    intro coarseLink hlink
    rw [slabExplicitLinkMultiplicity_zero_eq_one]
    omega

theorem normalityCounterJointSelection_rawWeight_pos :
    (0 : Q') <
      wholeSlabRecouplingRawWeight
        counterScalePair normalityCounterState
        normalityCounterJointSelection.coarseTarget :=
  normalityCounterJointSelection.rawWeight_pos

/-! ## 3. Strict carrier enlargement -/

def normalityCounterEnumeratedJointCarrier :
    WholeSlabEnumeratedJointCarrier
      counterScalePair normalityCounterState :=
  jointSelectionToEnumeratedCarrier
    normalityCounterJointSelection

theorem normalityCounterJointCarrierCodes_length_pos :
    0 <
      (wholeSlabJointCarrierCodes
        counterScalePair normalityCounterState).length :=
  List.length_pos_of_mem
    normalityCounterEnumeratedJointCarrier.code_mem

/-- The same positive physical row is absent from the closed-sheet
multicover carrier and present in the global joint carrier. -/
theorem normalityCounter_strict_carrier_separation :
    (BinaryEvenSlabMulticover
        counterScalePair normalityCounterState → False) ∧
      0 <
        (wholeSlabJointCarrierCodes
          counterScalePair normalityCounterState).length :=
  ⟨normalityCounterState_no_multicover,
    normalityCounterJointCarrierCodes_length_pos⟩

#print axioms normalityCounterRetainedPacket_vacuum_all
#print axioms normalityCounterSupport_degenerate
#print axioms normalityCounterPreimage_not_mem_support
#print axioms normalityCounterSpin_zero_of_not_mem_support
#print axioms normalityCounterSpin_zero_of_nondegenerate
#print axioms normalityCounterJointSelection
#print axioms normalityCounterJointSelection_rawWeight_pos
#print axioms normalityCounterEnumeratedJointCarrier
#print axioms normalityCounterJointCarrierCodes_length_pos
#print axioms normalityCounter_strict_carrier_separation

end YMGap.Continuum.BF4SU2OuterJointCarrierStrictEnlargement
