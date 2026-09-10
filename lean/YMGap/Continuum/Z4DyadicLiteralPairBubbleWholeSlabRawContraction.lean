/-
# Literal dyadic pair-bubble contraction in the whole-slab raw kernel

This file instantiates the isolated packet profile with an actual finite fine
support.  A lower or upper dyadic pair bubble is encoded by the slab's binary
support labelling.  Under the already identified spatial margin, the support
lies in the doubled fine slab.  Its packet is the pair-bubble packet over the
selected coarse face and the vacuum packet over every other physical coarse
face.

The whole-slab contraction compiler then proves that the complete globally
link-glued raw kernel row agrees pointwise with the vacuum fine-source row on
every bounded coarse target.  Finite congruence also identifies the complete
unnormalized row masses.  This is the first literal whole-slab cancellation
of the closed pair-bubble generator; it is not a cancellation in an arbitrary
non-vacuum background or for a general strand component.

Constructive contract: finite cubical support, exact rational algebra, and
finite SU(2) fusion data only; no `Classical`, choice, `native_decide`, proof
hole, noncomputable declaration, trusted external computation, or new axiom.
-/

import YMGap.Continuum.Z4DyadicPairBubbleWholeSlabRawContraction
import YMGap.Continuum.Z4DyadicSpinFourEndpointLift

namespace YMGap.Continuum.Z4DyadicLiteralPairBubbleWholeSlabRawContraction

set_option autoImplicit false
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicClosedPairBubble
open YMGap.Continuum.Z4DyadicModTwoCellularKernel
open YMGap.Continuum.Z4DyadicPairBubbleWholeSlabRawContraction
open YMGap.Continuum.Z4DyadicSpinFourEndpointLift
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Literal fine support and its packet profile -/

/-- Binary physical fine-state encoding of one translated dyadic pair
bubble. -/
def literalPairBubbleFineState
    (S : SlabScalePair) (targetFaceId : Nat) (upper : Bool) :
    EdgeLabelling :=
  slabBinarySupportLabelling S.fine.extent
    (dyadicPairBubble
      (slabPlaquetteAt S.coarse.extent targetFaceId) upper)

/-- A binary geometric support contained in the slab is read literally by
`slabSpinAtPlaquette`, including its zero extension away from the slab. -/
theorem slabSpinAtPlaquette_binarySupport_eq_supportCoefficient
    {extent : Nat} {support : List Z4Plaq}
    (hsubset : ∀ face, face ∈ support →
      face ∈ boundaryCompleteSlabPlaquettes extent) :
    slabSpinAtPlaquette extent
        (slabBinarySupportLabelling extent support) =
      fun face => (supportCoefficient support face).toNat := by
  funext face
  by_cases hslab : face ∈ boundaryCompleteSlabPlaquettes extent
  · rw [slabSpinAtPlaquette_eq_of_mem hslab]
    have hindex :
        listIndexOf face (boundaryCompleteSlabPlaquettes extent) ∈
          slabPhysicalFaceEdges extent := by
      unfold slabPhysicalFaceEdges
      exact List.mem_range.mpr
        (listIndexOf_lt_of_mem face
          (boundaryCompleteSlabPlaquettes extent) hslab)
    rw [slabBinarySupportLabelling_eq_indicator hindex]
    have hlookup :
        slabPlaquetteAt extent
            (listIndexOf face
              (boundaryCompleteSlabPlaquettes extent)) = face := by
      unfold slabPlaquetteAt
      exact getD_listIndexOf_of_mem fallbackPlaquette face
        (boundaryCompleteSlabPlaquettes extent) hslab
    rw [hlookup]
    unfold supportCoefficient
    by_cases hmem : face ∈ support <;> simp [hmem]
  · rw [slabSpinAtPlaquette_eq_zero_of_not_mem hslab]
    have hnotSupport : face ∉ support := by
      intro hmem
      exact hslab (hsubset face hmem)
    unfold supportCoefficient
    rw [decide_eq_false hnotSupport]
    rfl

/-- Exact coarse packet profile of the literal pair-bubble state. -/
theorem literalPairBubbleFineState_packet_eq
    (S : SlabScalePair) (targetFaceId : Nat) (upper : Bool)
    (htarget : targetFaceId ∈ S.coarse.faceEdges)
    (hsubset : ∀ fine,
      fine ∈ dyadicPairBubble
        (slabPlaquetteAt S.coarse.extent targetFaceId) upper →
      fine ∈ boundaryCompleteSlabPlaquettes S.fine.extent)
    (faceId : Nat) (hface : faceId ∈ S.coarse.faceEdges) :
    wholeSlabFinePacket S
        (literalPairBubbleFineState S targetFaceId upper) faceId =
      if faceId = targetFaceId then
        pairBubblePacket upper
      else (⟨0, 0, 0, 0⟩ : FaceSpinPacket) := by
  have hspin :=
    slabSpinAtPlaquette_binarySupport_eq_supportCoefficient hsubset
  unfold wholeSlabFinePacket literalPairBubbleFineState
  rw [hspin]
  rw [dyadicFaceSpinPacket_pairBubble]
  by_cases heq : faceId = targetFaceId
  · subst faceId
    rw [if_pos rfl, if_pos rfl]
  · have hfacePhysical :
        faceId ∈ slabPhysicalFaceEdges S.coarse.extent := by
      simpa only [SlabPhysicalData.faceEdges] using hface
    have htargetPhysical :
        targetFaceId ∈ slabPhysicalFaceEdges S.coarse.extent := by
      simpa only [SlabPhysicalData.faceEdges] using htarget
    have hplaquette :
        slabPlaquetteAt S.coarse.extent faceId ≠
          slabPlaquetteAt S.coarse.extent targetFaceId := by
      intro hplaquette
      exact heq
        (slabPlaquetteAt_injective_on_physical
          hfacePhysical htargetPhysical hplaquette)
    rw [if_neg hplaquette, if_neg heq]

/-- The literal fine state inhabits the actual fine Cartesian carrier at
cutoff one. -/
theorem literalPairBubbleFineState_mem
    (S : SlabScalePair) (targetFaceId : Nat) (upper : Bool)
    (hfineCutoff : S.fine.cutoff = 1) :
    literalPairBubbleFineState S targetFaceId upper ∈
      S.fine.physicalLabellings := by
  unfold literalPairBubbleFineState SlabPhysicalData.physicalLabellings
    SlabPhysicalData.faceEdges
  rw [hfineCutoff]
  exact slabBinarySupportLabelling_mem (by decide)
    (dyadicPairBubble
      (slabPlaquetteAt S.coarse.extent targetFaceId) upper)

/-- The spatial-margin theorem supplies the complete whole-slab packet
profile with no additional packet assumption. -/
def literalPairBubbleWholeSlabPacketProfileOfMargin
    (S : SlabScalePair) (targetFaceId : Nat) (upper : Bool)
    (htarget : targetFaceId ∈ S.coarse.faceEdges)
    (hmargin : pairBubbleCoarseMargin S.coarse.extent
      (slabPlaquetteAt S.coarse.extent targetFaceId)) :
    IsolatedPairBubbleWholeSlabPacketProfile S
      (literalPairBubbleFineState S targetFaceId upper)
      targetFaceId upper := by
  have htargetPhysical :
      targetFaceId ∈ slabPhysicalFaceEdges S.coarse.extent := by
    simpa only [SlabPhysicalData.faceEdges] using htarget
  have hcoarse := slabPlaquetteAt_mem htargetPhysical
  have hsubset : ∀ fine,
      fine ∈ dyadicPairBubble
        (slabPlaquetteAt S.coarse.extent targetFaceId) upper →
      fine ∈ boundaryCompleteSlabPlaquettes S.fine.extent := by
    intro fine hfine
    rw [S.fine_extent]
    exact dyadicPairBubble_subset_boundaryCompleteFineSlab_of_margin
      hcoarse hmargin hfine
  exact
    { target_mem := htarget
      packet_eq := literalPairBubbleFineState_packet_eq
        S targetFaceId upper htarget hsubset }

/-! ## 2. Pointwise and summed whole-slab raw contraction -/

/-- The actual literal pair-bubble row agrees pointwise with the vacuum row
on every bounded coarse target. -/
theorem wholeSlabRecouplingRawWeight_literalPairBubble_eqv_vacuum
    (S : SlabScalePair) (targetFaceId : Nat) (upper : Bool)
    (coarseState : EdgeLabelling)
    (hfineCutoff : S.fine.cutoff = 1)
    (htarget : targetFaceId ∈ S.coarse.faceEdges)
    (hmargin : pairBubbleCoarseMargin S.coarse.extent
      (slabPlaquetteAt S.coarse.extent targetFaceId))
    (hcoarseBounded : SlabFaceLabellingBounded
      S.coarse.cutoff S.coarse.extent coarseState) :
    wholeSlabRecouplingRawWeight S
        (literalPairBubbleFineState S targetFaceId upper) coarseState ≈
      wholeSlabRecouplingRawWeight S zeroEdgeLabelling coarseState := by
  exact wholeSlabRecouplingRawWeight_isolatedPairBubble_eqv_vacuum
    S (literalPairBubbleFineState S targetFaceId upper) coarseState
    targetFaceId upper hfineCutoff
    (literalPairBubbleWholeSlabPacketProfileOfMargin
      S targetFaceId upper htarget hmargin)
    hcoarseBounded

/-- Complete unnormalized raw row mass, before packaging a coherent-source
witness and dividing by the row partition. -/
def wholeSlabUnnormalizedRawRowMass
    (S : SlabScalePair) (fineState : EdgeLabelling) : Q' :=
  listQSum (wholeSlabRecouplingRawWeight S fineState)
    S.coarse.physicalLabellings

/-- The literal pair-bubble and vacuum fine sources have exactly the same
complete whole-slab raw row mass. -/
theorem wholeSlabUnnormalizedRawRowMass_literalPairBubble_eqv_vacuum
    (S : SlabScalePair) (targetFaceId : Nat) (upper : Bool)
    (hfineCutoff : S.fine.cutoff = 1)
    (htarget : targetFaceId ∈ S.coarse.faceEdges)
    (hmargin : pairBubbleCoarseMargin S.coarse.extent
      (slabPlaquetteAt S.coarse.extent targetFaceId)) :
    wholeSlabUnnormalizedRawRowMass S
        (literalPairBubbleFineState S targetFaceId upper) ≈
      wholeSlabUnnormalizedRawRowMass S zeroEdgeLabelling := by
  unfold wholeSlabUnnormalizedRawRowMass
  apply listQSum_congr_on
  intro coarseState hcoarse
  have hsound := boundedEdgeLabellings_sound
    S.coarse.cutoff S.coarse.faceEdges coarseState hcoarse
  have hbounded : SlabFaceLabellingBounded
      S.coarse.cutoff S.coarse.extent coarseState := by
    intro faceId hface
    have hface' : faceId ∈ S.coarse.faceEdges := by
      simpa only [SlabPhysicalData.faceEdges] using hface
    exact Nat.le_of_lt_succ (hsound.1 faceId hface')
  exact wholeSlabRecouplingRawWeight_literalPairBubble_eqv_vacuum
    S targetFaceId upper coarseState hfineCutoff htarget hmargin hbounded

#print axioms slabSpinAtPlaquette_binarySupport_eq_supportCoefficient
#print axioms literalPairBubbleFineState_packet_eq
#print axioms literalPairBubbleFineState_mem
#print axioms literalPairBubbleWholeSlabPacketProfileOfMargin
#print axioms wholeSlabRecouplingRawWeight_literalPairBubble_eqv_vacuum
#print axioms wholeSlabUnnormalizedRawRowMass_literalPairBubble_eqv_vacuum

end YMGap.Continuum.Z4DyadicLiteralPairBubbleWholeSlabRawContraction
