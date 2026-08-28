/-
# The aligned pivot carrier pairs within the two cut components

The equal-rank pivot carrier has auxiliary word `(0,1)`.  Its canonical
physical partner operation pairs positions `0 <-> 1` and `2 <-> 3`.
Transport that proof-independent local computation to every accepted
membership witness and then to the literal slab face identifiers.  Against
the aligned diagonal geometry, the first pair lies in the near cube and the
second in the far cube.

Constructive contract: explicit finite terminal enumeration only; no choice,
`Classical`, `native_decide`, `sorry`, new axiom, noncomputable declaration,
or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
import YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabPivotCarrier

namespace YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabPivotPairing

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Continuum.CanonicalLinkPhysicalTerminalPartner
open YMGap.Continuum.CanonicalLinkEdgeOccurrenceMultiplicity
open YMGap.Continuum.CanonicalLinkStrandStep
open YMGap.Continuum.CanonicalLinkStrandTerminal
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.SU2CanonicalLeftCarrierWitnessReconstruction
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchCutCarrier
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabWholeProductPositivity
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

theorem alignedDiagonalSwitchLeftPhysical_bounded :
    SlabFaceLabellingBounded 1 5 alignedDiagonalSwitchLeftPhysical := by
  intro faceId _
  exact slabBinarySupportLabelling_le_one
    5 alignedDiagonalSwitchSurface faceId

theorem alignedDiagonalPivotLeftAuxiliary_mem :
    alignedDiagonalPivotLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5 alignedDiagonalSwitchLeftPhysical
        alignedDiagonalSwitchPivot :=
  valenceFiveLeftAuxiliary_mem_slabLinkFusionWitnesses
    alignedDiagonalSwitchLeftPhysical_bounded
    alignedDiagonalSwitchPivot_degree_five
    alignedDiagonalPivotLeftSource

/-! ## 1. Proof-independent canonical pairing -/

def alignedDiagonalPivotLeftAllowed :
    YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
      5
      (slabLinkExternalSpins 5 alignedDiagonalSwitchLeftPhysical
        alignedDiagonalSwitchPivot)
      alignedDiagonalPivotLeftAuxiliary = true := by
  decide

def alignedDiagonalPivot_degree_le : 5 ≤
    YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff.linkIncidenceBound := by
  decide

def alignedDiagonalPivotCanonicalPhysicalTerminals :
    List (CanonicalPhysicalStrandPort
      (slabLinkExternalSpins 5 alignedDiagonalSwitchLeftPhysical
        alignedDiagonalSwitchPivot)
      alignedDiagonalPivotLeftAuxiliary
      alignedDiagonalPivotLeftAllowed) :=
  (allResolvedNetworkPorts
    (canonicalLinkResolvedStrandNetwork 5
      (slabLinkExternalSpins 5 alignedDiagonalSwitchLeftPhysical
        alignedDiagonalSwitchPivot)
      alignedDiagonalPivotLeftAuxiliary
      alignedDiagonalPivotLeftAllowed)).filterMap fun occurrence =>
        if hphysical : occurrence.edgeId < 5 then
          some ⟨occurrence, hphysical⟩
        else none

abbrev AlignedDiagonalPivotResolvedPort := ResolvedNetworkPort
  (canonicalLinkResolvedStrandNetwork 5
    (slabLinkExternalSpins 5 alignedDiagonalSwitchLeftPhysical
      alignedDiagonalSwitchPivot)
    alignedDiagonalPivotLeftAuxiliary alignedDiagonalPivotLeftAllowed)

def alignedDiagonalPivotPortZero : AlignedDiagonalPivotResolvedPort where
  vertexIndex := ⟨0, by decide⟩
  port := .onA ⟨0, by decide⟩

def alignedDiagonalPivotPortOne : AlignedDiagonalPivotResolvedPort where
  vertexIndex := ⟨0, by decide⟩
  port := .onB ⟨0, by decide⟩

def alignedDiagonalPivotPortTwo : AlignedDiagonalPivotResolvedPort where
  vertexIndex := ⟨1, by decide⟩
  port := .onB ⟨0, by decide⟩

def alignedDiagonalPivotPortThree : AlignedDiagonalPivotResolvedPort where
  vertexIndex := ⟨2, by decide⟩
  port := .onB ⟨0, by decide⟩

def alignedDiagonalPivotTerminalZero : CanonicalPhysicalStrandPort
    (slabLinkExternalSpins 5 alignedDiagonalSwitchLeftPhysical
      alignedDiagonalSwitchPivot)
    alignedDiagonalPivotLeftAuxiliary alignedDiagonalPivotLeftAllowed :=
  ⟨alignedDiagonalPivotPortZero, by decide⟩

def alignedDiagonalPivotTerminalOne : CanonicalPhysicalStrandPort
    (slabLinkExternalSpins 5 alignedDiagonalSwitchLeftPhysical
      alignedDiagonalSwitchPivot)
    alignedDiagonalPivotLeftAuxiliary alignedDiagonalPivotLeftAllowed :=
  ⟨alignedDiagonalPivotPortOne, by decide⟩

def alignedDiagonalPivotTerminalTwo : CanonicalPhysicalStrandPort
    (slabLinkExternalSpins 5 alignedDiagonalSwitchLeftPhysical
      alignedDiagonalSwitchPivot)
    alignedDiagonalPivotLeftAuxiliary alignedDiagonalPivotLeftAllowed :=
  ⟨alignedDiagonalPivotPortTwo, by decide⟩

def alignedDiagonalPivotTerminalThree : CanonicalPhysicalStrandPort
    (slabLinkExternalSpins 5 alignedDiagonalSwitchLeftPhysical
      alignedDiagonalSwitchPivot)
    alignedDiagonalPivotLeftAuxiliary alignedDiagonalPivotLeftAllowed :=
  ⟨alignedDiagonalPivotPortThree, by decide⟩

theorem alignedDiagonalPivotZeroMate_eq_one :
    alignedDiagonalPivotTerminalZero.1.localMate =
      alignedDiagonalPivotTerminalOne.1 := by
  apply ResolvedNetworkPort.address_injective
  decide

def alignedDiagonalPivotZeroToOnePath : CanonicalStrandPathToPhysical
    alignedDiagonalPivot_degree_le alignedDiagonalPivotLeftAllowed
    alignedDiagonalPivotTerminalZero.1.localMate
    alignedDiagonalPivotTerminalOne := by
  rw [alignedDiagonalPivotZeroMate_eq_one]
  exact .stop alignedDiagonalPivotTerminalOne

def alignedDiagonalPivotTwoMate_internal :
    alignedDiagonalPivotTerminalTwo.1.localMate.edgeId ∈
      canonicalInternalFusionEdges 5 := by
  decide

theorem alignedDiagonalPivotTwoMate_advance_eq_three :
    canonicalInternalAdvancePort alignedDiagonalPivot_degree_le
      alignedDiagonalPivotLeftAllowed
      alignedDiagonalPivotTerminalTwo.1.localMate
      alignedDiagonalPivotTwoMate_internal =
        alignedDiagonalPivotTerminalThree.1 := by
  apply ResolvedNetworkPort.address_injective
  decide

def alignedDiagonalPivotTwoToThreePath : CanonicalStrandPathToPhysical
    alignedDiagonalPivot_degree_le alignedDiagonalPivotLeftAllowed
    alignedDiagonalPivotTerminalTwo.1.localMate
    alignedDiagonalPivotTerminalThree := by
  refine .advance alignedDiagonalPivotTerminalTwo.1.localMate
    alignedDiagonalPivotTwoMate_internal
    alignedDiagonalPivotTerminalThree ?_
  rw [alignedDiagonalPivotTwoMate_advance_eq_three]
  exact .stop alignedDiagonalPivotTerminalThree

theorem alignedDiagonalPivotPartner_zero_eq_one :
    canonicalPhysicalStrandPartner alignedDiagonalPivot_degree_le
      alignedDiagonalPivotLeftAllowed alignedDiagonalPivotTerminalZero =
        alignedDiagonalPivotTerminalOne :=
  canonicalStrandPath_terminal_unique
    (canonicalPhysicalStrandPartner_path alignedDiagonalPivot_degree_le
      alignedDiagonalPivotLeftAllowed alignedDiagonalPivotTerminalZero)
    alignedDiagonalPivotZeroToOnePath

theorem alignedDiagonalPivotPartner_two_eq_three :
    canonicalPhysicalStrandPartner alignedDiagonalPivot_degree_le
      alignedDiagonalPivotLeftAllowed alignedDiagonalPivotTerminalTwo =
        alignedDiagonalPivotTerminalThree :=
  canonicalStrandPath_terminal_unique
    (canonicalPhysicalStrandPartner_path alignedDiagonalPivot_degree_le
      alignedDiagonalPivotLeftAllowed alignedDiagonalPivotTerminalTwo)
    alignedDiagonalPivotTwoToThreePath

theorem alignedDiagonalPivotPartner_one_eq_zero :
    canonicalPhysicalStrandPartner alignedDiagonalPivot_degree_le
      alignedDiagonalPivotLeftAllowed alignedDiagonalPivotTerminalOne =
        alignedDiagonalPivotTerminalZero := by
  rw [← alignedDiagonalPivotPartner_zero_eq_one]
  exact canonicalPhysicalStrandPartner_involutive
    alignedDiagonalPivot_degree_le alignedDiagonalPivotLeftAllowed
    alignedDiagonalPivotTerminalZero

theorem alignedDiagonalPivotPartner_three_eq_two :
    canonicalPhysicalStrandPartner alignedDiagonalPivot_degree_le
      alignedDiagonalPivotLeftAllowed alignedDiagonalPivotTerminalThree =
        alignedDiagonalPivotTerminalTwo := by
  rw [← alignedDiagonalPivotPartner_two_eq_three]
  exact canonicalPhysicalStrandPartner_involutive
    alignedDiagonalPivot_degree_le alignedDiagonalPivotLeftAllowed
    alignedDiagonalPivotTerminalTwo

theorem alignedDiagonalPivotCanonicalPhysicalTerminals_eq :
    alignedDiagonalPivotCanonicalPhysicalTerminals =
      [alignedDiagonalPivotTerminalZero,
       alignedDiagonalPivotTerminalOne,
       alignedDiagonalPivotTerminalTwo,
       alignedDiagonalPivotTerminalThree] := by
  decide

def alignedDiagonalPivotCanonicalEdgeIdPairs : List (Nat × Nat) :=
  alignedDiagonalPivotCanonicalPhysicalTerminals.map fun terminal =>
    (terminal.1.edgeId,
      (canonicalPhysicalStrandPartner alignedDiagonalPivot_degree_le
        alignedDiagonalPivotLeftAllowed terminal).1.edgeId)

theorem alignedDiagonalPivotCanonicalEdgeIdPairs_eq :
    alignedDiagonalPivotCanonicalEdgeIdPairs =
      [(0, 1), (1, 0), (2, 3), (3, 2)] := by
  unfold alignedDiagonalPivotCanonicalEdgeIdPairs
  rw [alignedDiagonalPivotCanonicalPhysicalTerminals_eq]
  simp only [List.map_cons, List.map_nil]
  rw [alignedDiagonalPivotPartner_zero_eq_one,
    alignedDiagonalPivotPartner_one_eq_zero,
    alignedDiagonalPivotPartner_two_eq_three,
    alignedDiagonalPivotPartner_three_eq_two]
  decide

/-! ## 2. Transport to every accepted membership proof -/

def alignedDiagonalPivotActualEdgeIdPairs
    (hmem : alignedDiagonalPivotLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5 alignedDiagonalSwitchLeftPhysical
        alignedDiagonalSwitchPivot) : List (Nat × Nat) :=
  (slabLinkPhysicalStrandTerminals 1 5 alignedDiagonalSwitchLeftPhysical
    alignedDiagonalSwitchPivot alignedDiagonalPivotLeftAuxiliary hmem).map
      fun terminal =>
        (terminal.1.edgeId,
          (slabLinkPhysicalStrandPartner 1 5
            alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
            alignedDiagonalPivotLeftAuxiliary hmem terminal).1.edgeId)

theorem alignedDiagonalPivotActualEdgeIdPairs_eq
    (hmem : alignedDiagonalPivotLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5 alignedDiagonalSwitchLeftPhysical
        alignedDiagonalSwitchPivot) :
    alignedDiagonalPivotActualEdgeIdPairs hmem =
      [(0, 1), (1, 0), (2, 3), (3, 2)] := by
  unfold alignedDiagonalPivotActualEdgeIdPairs
    slabLinkPhysicalStrandTerminals slabLinkPhysicalStrandPartner
  simp only [alignedDiagonalSwitchPivot_degree_five]
  change alignedDiagonalPivotCanonicalEdgeIdPairs =
    [(0, 1), (1, 0), (2, 3), (3, 2)]
  exact alignedDiagonalPivotCanonicalEdgeIdPairs_eq

theorem alignedDiagonalPivotActual_partner_position_pair
    (hmem : alignedDiagonalPivotLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5 alignedDiagonalSwitchLeftPhysical
        alignedDiagonalSwitchPivot)
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
      alignedDiagonalPivotLeftAuxiliary hmem) :
    (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5
          alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
          alignedDiagonalPivotLeftAuxiliary hmem terminal).1.edgeId) =
        (0, 1) ∨
    (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5
          alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
          alignedDiagonalPivotLeftAuxiliary hmem terminal).1.edgeId) =
        (1, 0) ∨
    (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5
          alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
          alignedDiagonalPivotLeftAuxiliary hmem terminal).1.edgeId) =
        (2, 3) ∨
    (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5
          alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
          alignedDiagonalPivotLeftAuxiliary hmem terminal).1.edgeId) =
        (3, 2) := by
  have hpairs := alignedDiagonalPivotActualEdgeIdPairs_eq hmem
  have hterminal : terminal ∈
      slabLinkPhysicalStrandTerminals 1 5
        alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
        alignedDiagonalPivotLeftAuxiliary hmem :=
    SlabLinkPhysicalStrandTerminal.mem_all 1 5
      alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
      alignedDiagonalPivotLeftAuxiliary hmem terminal
  have hpair :
      (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5
          alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
          alignedDiagonalPivotLeftAuxiliary hmem terminal).1.edgeId) ∈
        alignedDiagonalPivotActualEdgeIdPairs hmem := by
    unfold alignedDiagonalPivotActualEdgeIdPairs
    exact List.mem_map.mpr ⟨terminal, hterminal, rfl⟩
  rw [hpairs] at hpair
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using hpair

theorem alignedDiagonalPivot_incidentFaceIds :
    slabIncidentPlaqIds 5 alignedDiagonalSwitchPivot =
      [33, 199, 231, 232, 233] := by
  decide

theorem alignedDiagonalPivotActual_partner_faceId_pair
    (hmem : alignedDiagonalPivotLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5 alignedDiagonalSwitchLeftPhysical
        alignedDiagonalSwitchPivot)
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
      alignedDiagonalPivotLeftAuxiliary hmem) :
    let partner := slabLinkPhysicalStrandPartner 1 5
      alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
      alignedDiagonalPivotLeftAuxiliary hmem terminal
    let sourceFace := (slabLinkPhysicalTerminalOccurrence 1 5
      alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
      alignedDiagonalPivotLeftAuxiliary hmem terminal).faceId
    let targetFace := (slabLinkPhysicalTerminalOccurrence 1 5
      alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
      alignedDiagonalPivotLeftAuxiliary hmem partner).faceId
    (sourceFace, targetFace) = (33, 199) ∨
    (sourceFace, targetFace) = (199, 33) ∨
    (sourceFace, targetFace) = (231, 232) ∨
    (sourceFace, targetFace) = (232, 231) := by
  dsimp only
  let partner := slabLinkPhysicalStrandPartner 1 5
    alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
    alignedDiagonalPivotLeftAuxiliary hmem terminal
  have hpair := alignedDiagonalPivotActual_partner_position_pair
    hmem terminal
  rcases hpair with h01 | h10 | h23 | h32
  · left
    have hs : terminal.1.edgeId = 0 := by
      simpa only using congrArg Prod.fst h01
    have ht : partner.1.edgeId = 1 := by
      simpa only [partner] using congrArg Prod.snd h01
    apply Prod.ext
    · change (slabIncidentPlaqIds 5 alignedDiagonalSwitchPivot).get
          ⟨terminal.1.edgeId, terminal.2⟩ = 33
      simp [alignedDiagonalPivot_incidentFaceIds, hs]
    · change (slabIncidentPlaqIds 5 alignedDiagonalSwitchPivot).get
          ⟨partner.1.edgeId, partner.2⟩ = 199
      simp [alignedDiagonalPivot_incidentFaceIds, ht]
  · right; left
    have hs : terminal.1.edgeId = 1 := by
      simpa only using congrArg Prod.fst h10
    have ht : partner.1.edgeId = 0 := by
      simpa only [partner] using congrArg Prod.snd h10
    apply Prod.ext
    · change (slabIncidentPlaqIds 5 alignedDiagonalSwitchPivot).get
          ⟨terminal.1.edgeId, terminal.2⟩ = 199
      simp [alignedDiagonalPivot_incidentFaceIds, hs]
    · change (slabIncidentPlaqIds 5 alignedDiagonalSwitchPivot).get
          ⟨partner.1.edgeId, partner.2⟩ = 33
      simp [alignedDiagonalPivot_incidentFaceIds, ht]
  · right; right; left
    have hs : terminal.1.edgeId = 2 := by
      simpa only using congrArg Prod.fst h23
    have ht : partner.1.edgeId = 3 := by
      simpa only [partner] using congrArg Prod.snd h23
    apply Prod.ext
    · change (slabIncidentPlaqIds 5 alignedDiagonalSwitchPivot).get
          ⟨terminal.1.edgeId, terminal.2⟩ = 231
      simp [alignedDiagonalPivot_incidentFaceIds, hs]
    · change (slabIncidentPlaqIds 5 alignedDiagonalSwitchPivot).get
          ⟨partner.1.edgeId, partner.2⟩ = 232
      simp [alignedDiagonalPivot_incidentFaceIds, ht]
  · right; right; right
    have hs : terminal.1.edgeId = 3 := by
      simpa only using congrArg Prod.fst h32
    have ht : partner.1.edgeId = 2 := by
      simpa only [partner] using congrArg Prod.snd h32
    apply Prod.ext
    · change (slabIncidentPlaqIds 5 alignedDiagonalSwitchPivot).get
          ⟨terminal.1.edgeId, terminal.2⟩ = 232
      simp [alignedDiagonalPivot_incidentFaceIds, hs]
    · change (slabIncidentPlaqIds 5 alignedDiagonalSwitchPivot).get
          ⟨partner.1.edgeId, partner.2⟩ = 231
      simp [alignedDiagonalPivot_incidentFaceIds, ht]

theorem alignedDiagonalPivotTerminal_pair_same_side
    (hmem : alignedDiagonalPivotLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5 alignedDiagonalSwitchLeftPhysical
        alignedDiagonalSwitchPivot)
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
      alignedDiagonalPivotLeftAuxiliary hmem) :
    let partner := slabLinkPhysicalStrandPartner 1 5
      alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
      alignedDiagonalPivotLeftAuxiliary hmem terminal
    let sourceFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
        alignedDiagonalPivotLeftAuxiliary hmem terminal).faceId
    let targetFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
        alignedDiagonalPivotLeftAuxiliary hmem partner).faceId
    (sourceFace ∈ alignedDiagonalNearSurface ∧
      targetFace ∈ alignedDiagonalNearSurface) ∨
    (sourceFace ∈ alignedDiagonalFarSurface ∧
      targetFace ∈ alignedDiagonalFarSurface) := by
  dsimp only
  have hfaces := alignedDiagonalPivotActual_partner_faceId_pair hmem terminal
  rcases hfaces with hnear | hnear | hfar | hfar
  · left
    have hs : (slabLinkPhysicalTerminalOccurrence 1 5
        alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
        alignedDiagonalPivotLeftAuxiliary hmem terminal).faceId = 33 := by
      simpa only using congrArg Prod.fst hnear
    have ht : (slabLinkPhysicalTerminalOccurrence 1 5
        alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
        alignedDiagonalPivotLeftAuxiliary hmem
        (slabLinkPhysicalStrandPartner 1 5
          alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
          alignedDiagonalPivotLeftAuxiliary hmem terminal)).faceId = 199 := by
      simpa only using congrArg Prod.snd hnear
    rw [hs, ht]
    constructor <;> decide
  · left
    have hs : (slabLinkPhysicalTerminalOccurrence 1 5
        alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
        alignedDiagonalPivotLeftAuxiliary hmem terminal).faceId = 199 := by
      simpa only using congrArg Prod.fst hnear
    have ht : (slabLinkPhysicalTerminalOccurrence 1 5
        alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
        alignedDiagonalPivotLeftAuxiliary hmem
        (slabLinkPhysicalStrandPartner 1 5
          alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
          alignedDiagonalPivotLeftAuxiliary hmem terminal)).faceId = 33 := by
      simpa only using congrArg Prod.snd hnear
    rw [hs, ht]
    constructor <;> decide
  · right
    have hs : (slabLinkPhysicalTerminalOccurrence 1 5
        alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
        alignedDiagonalPivotLeftAuxiliary hmem terminal).faceId = 231 := by
      simpa only using congrArg Prod.fst hfar
    have ht : (slabLinkPhysicalTerminalOccurrence 1 5
        alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
        alignedDiagonalPivotLeftAuxiliary hmem
        (slabLinkPhysicalStrandPartner 1 5
          alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
          alignedDiagonalPivotLeftAuxiliary hmem terminal)).faceId = 232 := by
      simpa only using congrArg Prod.snd hfar
    rw [hs, ht]
    constructor <;> decide
  · right
    have hs : (slabLinkPhysicalTerminalOccurrence 1 5
        alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
        alignedDiagonalPivotLeftAuxiliary hmem terminal).faceId = 232 := by
      simpa only using congrArg Prod.fst hfar
    have ht : (slabLinkPhysicalTerminalOccurrence 1 5
        alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
        alignedDiagonalPivotLeftAuxiliary hmem
        (slabLinkPhysicalStrandPartner 1 5
          alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchPivot
          alignedDiagonalPivotLeftAuxiliary hmem terminal)).faceId = 231 := by
      simpa only using congrArg Prod.snd hfar
    rw [hs, ht]
    constructor <;> decide

#print axioms alignedDiagonalPivotLeftAuxiliary_mem
#print axioms alignedDiagonalPivotCanonicalEdgeIdPairs_eq
#print axioms alignedDiagonalPivotActualEdgeIdPairs_eq
#print axioms alignedDiagonalPivotActual_partner_faceId_pair
#print axioms alignedDiagonalPivotTerminal_pair_same_side

end YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabPivotPairing
