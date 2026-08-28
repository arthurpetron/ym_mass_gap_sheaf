/-
# The reflected bent pivot carrier preserves both geometric lobes

The selected equal-rank carrier has auxiliary word `(1,0)`.  Its canonical
physical partner involution pairs positions `0 <-> 2` and `3 <-> 4` in the
ordered external word `[1,0,1,1,1]`.  These are respectively the two near
faces and the two far faces at the unique pivot.

Constructive contract: explicit finite terminal enumeration only; no choice,
`Classical`, `native_decide`, `sorry`, new axiom, noncomputable declaration,
or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabWholeProductPositivity

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotPairing

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
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabWholeProductPositivity

theorem reflectedBentSwitchLeftPhysical_bounded :
    SlabFaceLabellingBounded 1 5 reflectedBentSwitchLeftPhysical := by
  intro faceId _
  exact slabBinarySupportLabelling_le_one
    5
    YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile.reflectedBentSwitchSurface
    faceId

theorem reflectedBentPivotLeftAuxiliary_mem :
    reflectedBentPivotLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5 reflectedBentSwitchLeftPhysical
        reflectedBentSwitchPivot :=
  valenceFiveLeftAuxiliary_mem_slabLinkFusionWitnesses
    reflectedBentSwitchLeftPhysical_bounded
    reflectedBentSwitchPivot_degree_five
    reflectedBentPivotLeftSource

def reflectedBentPivotLeftAllowed :
    YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
      5
      (slabLinkExternalSpins 5 reflectedBentSwitchLeftPhysical
        reflectedBentSwitchPivot)
      reflectedBentPivotLeftAuxiliary = true := by
  decide

def reflectedBentPivot_degree_le : 5 ≤
    YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff.linkIncidenceBound := by
  decide

def reflectedBentPivotCanonicalPhysicalTerminals :
    List (CanonicalPhysicalStrandPort
      (slabLinkExternalSpins 5 reflectedBentSwitchLeftPhysical
        reflectedBentSwitchPivot)
      reflectedBentPivotLeftAuxiliary
      reflectedBentPivotLeftAllowed) :=
  (allResolvedNetworkPorts
    (canonicalLinkResolvedStrandNetwork 5
      (slabLinkExternalSpins 5 reflectedBentSwitchLeftPhysical
        reflectedBentSwitchPivot)
      reflectedBentPivotLeftAuxiliary
      reflectedBentPivotLeftAllowed)).filterMap fun occurrence =>
        if hphysical : occurrence.edgeId < 5 then
          some ⟨occurrence, hphysical⟩
        else none

def reflectedBentPivotCanonicalEdgeIdPairs : List (Nat × Nat) :=
  reflectedBentPivotCanonicalPhysicalTerminals.map fun terminal =>
    (terminal.1.edgeId,
      (canonicalPhysicalStrandPartner reflectedBentPivot_degree_le
        reflectedBentPivotLeftAllowed terminal).1.edgeId)

theorem reflectedBentPivotCanonicalEdgeIdPairs_eq :
    reflectedBentPivotCanonicalEdgeIdPairs =
      [(0, 2), (2, 0), (3, 4), (4, 3)] := by
  decide

/-! ## 2. Transport to accepted production membership -/

def reflectedBentPivotActualEdgeIdPairs
    (hmem : reflectedBentPivotLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5 reflectedBentSwitchLeftPhysical
        reflectedBentSwitchPivot) : List (Nat × Nat) :=
  (slabLinkPhysicalStrandTerminals 1 5 reflectedBentSwitchLeftPhysical
    reflectedBentSwitchPivot reflectedBentPivotLeftAuxiliary hmem).map
      fun terminal =>
        (terminal.1.edgeId,
          (slabLinkPhysicalStrandPartner 1 5
            reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
            reflectedBentPivotLeftAuxiliary hmem terminal).1.edgeId)

theorem reflectedBentPivotActualEdgeIdPairs_eq
    (hmem : reflectedBentPivotLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5 reflectedBentSwitchLeftPhysical
        reflectedBentSwitchPivot) :
    reflectedBentPivotActualEdgeIdPairs hmem =
      [(0, 2), (2, 0), (3, 4), (4, 3)] := by
  unfold reflectedBentPivotActualEdgeIdPairs
    slabLinkPhysicalStrandTerminals slabLinkPhysicalStrandPartner
  simp only [reflectedBentSwitchPivot_degree_five]
  change reflectedBentPivotCanonicalEdgeIdPairs =
    [(0, 2), (2, 0), (3, 4), (4, 3)]
  exact reflectedBentPivotCanonicalEdgeIdPairs_eq

theorem reflectedBentPivotActual_partner_position_pair
    (hmem : reflectedBentPivotLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5 reflectedBentSwitchLeftPhysical
        reflectedBentSwitchPivot)
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
      reflectedBentPivotLeftAuxiliary hmem) :
    (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5
          reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
          reflectedBentPivotLeftAuxiliary hmem terminal).1.edgeId) =
        (0, 2) ∨
    (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5
          reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
          reflectedBentPivotLeftAuxiliary hmem terminal).1.edgeId) =
        (2, 0) ∨
    (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5
          reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
          reflectedBentPivotLeftAuxiliary hmem terminal).1.edgeId) =
        (3, 4) ∨
    (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5
          reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
          reflectedBentPivotLeftAuxiliary hmem terminal).1.edgeId) =
        (4, 3) := by
  have hpairs := reflectedBentPivotActualEdgeIdPairs_eq hmem
  have hterminal : terminal ∈
      slabLinkPhysicalStrandTerminals 1 5
        reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
        reflectedBentPivotLeftAuxiliary hmem :=
    SlabLinkPhysicalStrandTerminal.mem_all 1 5
      reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
      reflectedBentPivotLeftAuxiliary hmem terminal
  have hpair :
      (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5
          reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
          reflectedBentPivotLeftAuxiliary hmem terminal).1.edgeId) ∈
        reflectedBentPivotActualEdgeIdPairs hmem := by
    unfold reflectedBentPivotActualEdgeIdPairs
    exact List.mem_map.mpr ⟨terminal, hterminal, rfl⟩
  rw [hpairs] at hpair
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using hpair

theorem reflectedBentPivot_incidentFaceIds :
    slabIncidentPlaqIds 5 reflectedBentSwitchPivot =
      [13, 41, 45, 46, 47] := by
  decide

theorem reflectedBentPivotActual_partner_faceId_pair
    (hmem : reflectedBentPivotLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5 reflectedBentSwitchLeftPhysical
        reflectedBentSwitchPivot)
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
      reflectedBentPivotLeftAuxiliary hmem) :
    let partner := slabLinkPhysicalStrandPartner 1 5
      reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
      reflectedBentPivotLeftAuxiliary hmem terminal
    let sourceFace := (slabLinkPhysicalTerminalOccurrence 1 5
      reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
      reflectedBentPivotLeftAuxiliary hmem terminal).faceId
    let targetFace := (slabLinkPhysicalTerminalOccurrence 1 5
      reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
      reflectedBentPivotLeftAuxiliary hmem partner).faceId
    (sourceFace, targetFace) = (13, 45) ∨
    (sourceFace, targetFace) = (45, 13) ∨
    (sourceFace, targetFace) = (46, 47) ∨
    (sourceFace, targetFace) = (47, 46) := by
  dsimp only
  let partner := slabLinkPhysicalStrandPartner 1 5
    reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
    reflectedBentPivotLeftAuxiliary hmem terminal
  have hpair := reflectedBentPivotActual_partner_position_pair hmem terminal
  rcases hpair with h02 | h20 | h34 | h43
  · left
    have hs : terminal.1.edgeId = 0 := by
      simpa only using congrArg Prod.fst h02
    have ht : partner.1.edgeId = 2 := by
      simpa only [partner] using congrArg Prod.snd h02
    apply Prod.ext
    · change (slabIncidentPlaqIds 5 reflectedBentSwitchPivot).get
          ⟨terminal.1.edgeId, terminal.2⟩ = 13
      simp [reflectedBentPivot_incidentFaceIds, hs]
    · change (slabIncidentPlaqIds 5 reflectedBentSwitchPivot).get
          ⟨partner.1.edgeId, partner.2⟩ = 45
      simp [reflectedBentPivot_incidentFaceIds, ht]
  · right; left
    have hs : terminal.1.edgeId = 2 := by
      simpa only using congrArg Prod.fst h20
    have ht : partner.1.edgeId = 0 := by
      simpa only [partner] using congrArg Prod.snd h20
    apply Prod.ext
    · change (slabIncidentPlaqIds 5 reflectedBentSwitchPivot).get
          ⟨terminal.1.edgeId, terminal.2⟩ = 45
      simp [reflectedBentPivot_incidentFaceIds, hs]
    · change (slabIncidentPlaqIds 5 reflectedBentSwitchPivot).get
          ⟨partner.1.edgeId, partner.2⟩ = 13
      simp [reflectedBentPivot_incidentFaceIds, ht]
  · right; right; left
    have hs : terminal.1.edgeId = 3 := by
      simpa only using congrArg Prod.fst h34
    have ht : partner.1.edgeId = 4 := by
      simpa only [partner] using congrArg Prod.snd h34
    apply Prod.ext
    · change (slabIncidentPlaqIds 5 reflectedBentSwitchPivot).get
          ⟨terminal.1.edgeId, terminal.2⟩ = 46
      simp [reflectedBentPivot_incidentFaceIds, hs]
    · change (slabIncidentPlaqIds 5 reflectedBentSwitchPivot).get
          ⟨partner.1.edgeId, partner.2⟩ = 47
      simp [reflectedBentPivot_incidentFaceIds, ht]
  · right; right; right
    have hs : terminal.1.edgeId = 4 := by
      simpa only using congrArg Prod.fst h43
    have ht : partner.1.edgeId = 3 := by
      simpa only [partner] using congrArg Prod.snd h43
    apply Prod.ext
    · change (slabIncidentPlaqIds 5 reflectedBentSwitchPivot).get
          ⟨terminal.1.edgeId, terminal.2⟩ = 47
      simp [reflectedBentPivot_incidentFaceIds, hs]
    · change (slabIncidentPlaqIds 5 reflectedBentSwitchPivot).get
          ⟨partner.1.edgeId, partner.2⟩ = 46
      simp [reflectedBentPivot_incidentFaceIds, ht]

theorem reflectedBentPivotTerminal_pair_same_side
    (hmem : reflectedBentPivotLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5 reflectedBentSwitchLeftPhysical
        reflectedBentSwitchPivot)
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
      reflectedBentPivotLeftAuxiliary hmem) :
    let partner := slabLinkPhysicalStrandPartner 1 5
      reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
      reflectedBentPivotLeftAuxiliary hmem terminal
    let sourceFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
        reflectedBentPivotLeftAuxiliary hmem terminal).faceId
    let targetFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
        reflectedBentPivotLeftAuxiliary hmem partner).faceId
    (sourceFace ∈
        YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchCutCarrier.reflectedBentNearSurface ∧
      targetFace ∈
        YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchCutCarrier.reflectedBentNearSurface) ∨
    (sourceFace ∈
        YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchCutCarrier.reflectedBentFarSurface ∧
      targetFace ∈
        YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchCutCarrier.reflectedBentFarSurface) := by
  dsimp only
  have hfaces := reflectedBentPivotActual_partner_faceId_pair hmem terminal
  rcases hfaces with hnear | hnear | hfar | hfar
  · left
    have hs : (slabLinkPhysicalTerminalOccurrence 1 5
        reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
        reflectedBentPivotLeftAuxiliary hmem terminal).faceId = 13 := by
      simpa only using congrArg Prod.fst hnear
    have ht : (slabLinkPhysicalTerminalOccurrence 1 5
        reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
        reflectedBentPivotLeftAuxiliary hmem
        (slabLinkPhysicalStrandPartner 1 5
          reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
          reflectedBentPivotLeftAuxiliary hmem terminal)).faceId = 45 := by
      simpa only using congrArg Prod.snd hnear
    rw [hs, ht]
    constructor <;> decide
  · left
    have hs : (slabLinkPhysicalTerminalOccurrence 1 5
        reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
        reflectedBentPivotLeftAuxiliary hmem terminal).faceId = 45 := by
      simpa only using congrArg Prod.fst hnear
    have ht : (slabLinkPhysicalTerminalOccurrence 1 5
        reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
        reflectedBentPivotLeftAuxiliary hmem
        (slabLinkPhysicalStrandPartner 1 5
          reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
          reflectedBentPivotLeftAuxiliary hmem terminal)).faceId = 13 := by
      simpa only using congrArg Prod.snd hnear
    rw [hs, ht]
    constructor <;> decide
  · right
    have hs : (slabLinkPhysicalTerminalOccurrence 1 5
        reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
        reflectedBentPivotLeftAuxiliary hmem terminal).faceId = 46 := by
      simpa only using congrArg Prod.fst hfar
    have ht : (slabLinkPhysicalTerminalOccurrence 1 5
        reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
        reflectedBentPivotLeftAuxiliary hmem
        (slabLinkPhysicalStrandPartner 1 5
          reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
          reflectedBentPivotLeftAuxiliary hmem terminal)).faceId = 47 := by
      simpa only using congrArg Prod.snd hfar
    rw [hs, ht]
    constructor <;> decide
  · right
    have hs : (slabLinkPhysicalTerminalOccurrence 1 5
        reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
        reflectedBentPivotLeftAuxiliary hmem terminal).faceId = 47 := by
      simpa only using congrArg Prod.fst hfar
    have ht : (slabLinkPhysicalTerminalOccurrence 1 5
        reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
        reflectedBentPivotLeftAuxiliary hmem
        (slabLinkPhysicalStrandPartner 1 5
          reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
          reflectedBentPivotLeftAuxiliary hmem terminal)).faceId = 46 := by
      simpa only using congrArg Prod.snd hfar
    rw [hs, ht]
    constructor <;> decide

#print axioms reflectedBentPivotLeftAuxiliary_mem
#print axioms reflectedBentPivotCanonicalEdgeIdPairs_eq
#print axioms reflectedBentPivotActualEdgeIdPairs_eq
#print axioms reflectedBentPivotActual_partner_faceId_pair
#print axioms reflectedBentPivotTerminal_pair_same_side

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotPairing
