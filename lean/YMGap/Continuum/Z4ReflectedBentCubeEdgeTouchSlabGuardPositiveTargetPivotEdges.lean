/-
# Exact pivot edges of the realized positive guarded target

At the unique active pivot, the realized left auxiliary is the explicit
component-preserving `(1,0)` carrier.  Recompute its physical terminal pairs
over the grafted field, using equality of the local external word with the
fixed reflected pattern.

Constructive contract: finite terminal enumeration and exact incident-face
lookup only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPivotPairing

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPivotEdges

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Continuum.CanonicalLinkPhysicalTerminalPartner
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchCutCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTarget
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPivotPairing
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealization
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotPairing
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile

/-! ## 1. Project terminal pairing to ordinary finite data -/

def canonicalPhysicalPartnerEdgeIdPairs
    (degree : Nat) (external auxiliary : SlabLabelling)
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true) :
    List (Nat × Nat) :=
  ((allResolvedNetworkPorts
      (canonicalLinkResolvedStrandNetwork degree external auxiliary hallowed)).filterMap
        fun occurrence =>
          if hphysical : occurrence.edgeId < degree then
            some ⟨occurrence, hphysical⟩
          else none).map fun terminal =>
    (terminal.1.edgeId,
      (canonicalPhysicalStrandPartner hdegree hallowed terminal).1.edgeId)

theorem canonicalPhysicalPartnerEdgeIdPairs_eq_of_external_eq
    (degree : Nat) (leftExternal rightExternal auxiliary : SlabLabelling)
    (hdegree : degree ≤ linkIncidenceBound)
    (hexternal : leftExternal = rightExternal)
    (leftAllowed :
      canonicalLinkConditionalAllowedB degree leftExternal auxiliary = true)
    (rightAllowed :
      canonicalLinkConditionalAllowedB degree rightExternal auxiliary = true) :
    canonicalPhysicalPartnerEdgeIdPairs degree leftExternal auxiliary
        hdegree leftAllowed =
      canonicalPhysicalPartnerEdgeIdPairs degree rightExternal auxiliary
        hdegree rightAllowed := by
  cases hexternal
  rfl

theorem canonicalPhysicalPartnerEdgeIdPairs_eq_of_auxiliary_eq
    (degree : Nat) (external leftAuxiliary rightAuxiliary : SlabLabelling)
    (hdegree : degree ≤ linkIncidenceBound)
    (hauxiliary : leftAuxiliary = rightAuxiliary)
    (leftAllowed : canonicalLinkConditionalAllowedB degree external
      leftAuxiliary = true)
    (rightAllowed : canonicalLinkConditionalAllowedB degree external
      rightAuxiliary = true) :
    canonicalPhysicalPartnerEdgeIdPairs degree external leftAuxiliary
        hdegree leftAllowed =
      canonicalPhysicalPartnerEdgeIdPairs degree external rightAuxiliary
        hdegree rightAllowed := by
  cases hauxiliary
  rfl

def slabLinkPhysicalPartnerEdgeIdPairs
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈
      slabLinkFusionWitnesses K extent physical link) :
    List (Nat × Nat) :=
  (slabLinkPhysicalStrandTerminals
    K extent physical link auxiliary hmem).map fun terminal =>
      (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner K extent physical link
          auxiliary hmem terminal).1.edgeId)

theorem slabLinkPhysicalPartnerEdgeIdPairs_eq_canonical
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈
      slabLinkFusionWitnesses K extent physical link) :
    slabLinkPhysicalPartnerEdgeIdPairs K extent physical link
        auxiliary hmem =
      canonicalPhysicalPartnerEdgeIdPairs
        (slabIncidentPlaqIds extent link).length
        (slabLinkExternalSpins extent physical link) auxiliary
        (slabIncidentPlaqIds_length_le_six extent link)
        (slabLinkFusionWitness_mem_allowed
          K extent physical link auxiliary hmem) := by
  rfl

/-- After projection to edge identifiers, the accepted terminal pairing
depends on the physical field only through its local external spin word. -/
theorem slabLinkPhysicalPartnerEdgeIdPairs_eq_of_externalSpins_eq
    (K extent : Nat) (leftPhysical rightPhysical : SlabLabelling)
    (link : SlabLink) (auxiliary : SlabLabelling)
    (hspins : slabLinkExternalSpins extent leftPhysical link =
      slabLinkExternalSpins extent rightPhysical link)
    (left_mem : auxiliary ∈
      slabLinkFusionWitnesses K extent leftPhysical link)
    (right_mem : auxiliary ∈
      slabLinkFusionWitnesses K extent rightPhysical link) :
    slabLinkPhysicalPartnerEdgeIdPairs K extent leftPhysical link
        auxiliary left_mem =
      slabLinkPhysicalPartnerEdgeIdPairs K extent rightPhysical link
        auxiliary right_mem := by
  rw [slabLinkPhysicalPartnerEdgeIdPairs_eq_canonical,
    slabLinkPhysicalPartnerEdgeIdPairs_eq_canonical]
  exact canonicalPhysicalPartnerEdgeIdPairs_eq_of_external_eq
    (slabIncidentPlaqIds extent link).length
    (slabLinkExternalSpins extent leftPhysical link)
    (slabLinkExternalSpins extent rightPhysical link)
    auxiliary (slabIncidentPlaqIds_length_le_six extent link)
    hspins _ _

theorem slabLinkPhysicalPartnerEdgeIdPairs_eq_of_auxiliary_eq
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (leftAuxiliary rightAuxiliary : SlabLabelling)
    (hauxiliary : leftAuxiliary = rightAuxiliary)
    (left_mem : leftAuxiliary ∈
      slabLinkFusionWitnesses K extent physical link)
    (right_mem : rightAuxiliary ∈
      slabLinkFusionWitnesses K extent physical link) :
    slabLinkPhysicalPartnerEdgeIdPairs K extent physical link
        leftAuxiliary left_mem =
      slabLinkPhysicalPartnerEdgeIdPairs K extent physical link
        rightAuxiliary right_mem := by
  rw [slabLinkPhysicalPartnerEdgeIdPairs_eq_canonical,
    slabLinkPhysicalPartnerEdgeIdPairs_eq_canonical]
  exact canonicalPhysicalPartnerEdgeIdPairs_eq_of_auxiliary_eq
    (slabIncidentPlaqIds extent link).length
    (slabLinkExternalSpins extent physical link)
    leftAuxiliary rightAuxiliary
    (slabIncidentPlaqIds_length_le_six extent link)
    hauxiliary _ _

/-! ## 2. Reuse the exact reflected pivot computation -/

def reflectedBentGuardGraftPivotActualEdgeIdPairs
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (hmem : reflectedBentPivotLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        reflectedBentSwitchPivot) : List (Nat × Nat) :=
  slabLinkPhysicalPartnerEdgeIdPairs 1 5
    (reflectedBentGuardGraftLeftPhysical D hextent state)
    reflectedBentSwitchPivot reflectedBentPivotLeftAuxiliary hmem

theorem reflectedBentGuardGraftPivotActualEdgeIdPairs_eq
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (hmem : reflectedBentPivotLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        reflectedBentSwitchPivot) :
    reflectedBentGuardGraftPivotActualEdgeIdPairs
        D hextent state hmem =
      [(0, 2), (2, 0), (3, 4), (4, 3)] := by
  let pattern_mem := reflectedBentPivotLeftAuxiliary_mem
  calc
    reflectedBentGuardGraftPivotActualEdgeIdPairs D hextent state hmem =
        slabLinkPhysicalPartnerEdgeIdPairs 1 5
          reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
          reflectedBentPivotLeftAuxiliary pattern_mem :=
      slabLinkPhysicalPartnerEdgeIdPairs_eq_of_externalSpins_eq
        1 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        reflectedBentSwitchLeftPhysical reflectedBentSwitchPivot
        reflectedBentPivotLeftAuxiliary
        (reflectedBentGuardGraftLeftExternalSpins_eq_pattern_at_pivot
          D hextent state) hmem pattern_mem
    _ = [(0, 2), (2, 0), (3, 4), (4, 3)] := by
      exact reflectedBentPivotActualEdgeIdPairs_eq pattern_mem

/-- A concrete projected edge-pair list classifies every physical terminal,
without transporting the dependent terminal subtype itself. -/
theorem slabLinkPhysicalPartner_position_pair_of_edgeIdPairs_eq
    (K extent : Nat) (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hmem : auxiliary ∈
      slabLinkFusionWitnesses K extent physical link)
    (hpairs : slabLinkPhysicalPartnerEdgeIdPairs K extent physical link
      auxiliary hmem = [(0, 2), (2, 0), (3, 4), (4, 3)])
    (terminal : SlabLinkPhysicalStrandTerminal K extent physical link
      auxiliary hmem) :
    let partner := slabLinkPhysicalStrandPartner K extent physical link
      auxiliary hmem terminal
    (terminal.1.edgeId, partner.1.edgeId) = (0, 2) ∨
    (terminal.1.edgeId, partner.1.edgeId) = (2, 0) ∨
    (terminal.1.edgeId, partner.1.edgeId) = (3, 4) ∨
    (terminal.1.edgeId, partner.1.edgeId) = (4, 3) := by
  dsimp only
  have hterminal : terminal ∈
      slabLinkPhysicalStrandTerminals K extent physical link auxiliary hmem :=
    SlabLinkPhysicalStrandTerminal.mem_all K extent physical link
      auxiliary hmem terminal
  have hpair :
      (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner K extent physical link auxiliary hmem
          terminal).1.edgeId) ∈
        slabLinkPhysicalPartnerEdgeIdPairs K extent physical link
          auxiliary hmem := by
    unfold slabLinkPhysicalPartnerEdgeIdPairs
    exact List.mem_map.mpr ⟨terminal, hterminal, rfl⟩
  rw [hpairs] at hpair
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using hpair

/-- At the reflected pivot, the four possible ordinary position pairs determine
the four corresponding incident-face pairs for any physical field and accepted
auxiliary. -/
theorem reflectedBentPivot_partner_faceId_pair_of_position_pair
    (physical auxiliary : SlabLabelling)
    (hmem : auxiliary ∈
      slabLinkFusionWitnesses 1 5 physical reflectedBentSwitchPivot)
    (terminal : SlabLinkPhysicalStrandTerminal 1 5 physical
      reflectedBentSwitchPivot auxiliary hmem)
    (hposition :
      let partner := slabLinkPhysicalStrandPartner 1 5 physical
        reflectedBentSwitchPivot auxiliary hmem terminal
      (terminal.1.edgeId, partner.1.edgeId) = (0, 2) ∨
      (terminal.1.edgeId, partner.1.edgeId) = (2, 0) ∨
      (terminal.1.edgeId, partner.1.edgeId) = (3, 4) ∨
      (terminal.1.edgeId, partner.1.edgeId) = (4, 3)) :
    let partner := slabLinkPhysicalStrandPartner 1 5 physical
      reflectedBentSwitchPivot auxiliary hmem terminal
    let sourceFace := (slabLinkPhysicalTerminalOccurrence 1 5 physical
      reflectedBentSwitchPivot auxiliary hmem terminal).faceId
    let targetFace := (slabLinkPhysicalTerminalOccurrence 1 5 physical
      reflectedBentSwitchPivot auxiliary hmem partner).faceId
    (sourceFace, targetFace) = (13, 45) ∨
    (sourceFace, targetFace) = (45, 13) ∨
    (sourceFace, targetFace) = (46, 47) ∨
    (sourceFace, targetFace) = (47, 46) := by
  dsimp only at hposition ⊢
  let partner := slabLinkPhysicalStrandPartner 1 5 physical
    reflectedBentSwitchPivot auxiliary hmem terminal
  rcases hposition with h02 | h20 | h34 | h43
  · left
    have hs : terminal.1.edgeId = 0 := congrArg Prod.fst h02
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
    have hs : terminal.1.edgeId = 2 := congrArg Prod.fst h20
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
    have hs : terminal.1.edgeId = 3 := congrArg Prod.fst h34
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
    have hs : terminal.1.edgeId = 4 := congrArg Prod.fst h43
    have ht : partner.1.edgeId = 3 := by
      simpa only [partner] using congrArg Prod.snd h43
    apply Prod.ext
    · change (slabIncidentPlaqIds 5 reflectedBentSwitchPivot).get
          ⟨terminal.1.edgeId, terminal.2⟩ = 47
      simp [reflectedBentPivot_incidentFaceIds, hs]
    · change (slabIncidentPlaqIds 5 reflectedBentSwitchPivot).get
          ⟨partner.1.edgeId, partner.2⟩ = 46
      simp [reflectedBentPivot_incidentFaceIds, ht]

theorem reflectedBentGuardGraftPivotActual_partner_position_pair
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (hmem : reflectedBentPivotLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        reflectedBentSwitchPivot)
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      reflectedBentSwitchPivot reflectedBentPivotLeftAuxiliary hmem) :
    let partner := slabLinkPhysicalStrandPartner 1 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      reflectedBentSwitchPivot reflectedBentPivotLeftAuxiliary hmem terminal
    (terminal.1.edgeId, partner.1.edgeId) = (0, 2) ∨
    (terminal.1.edgeId, partner.1.edgeId) = (2, 0) ∨
    (terminal.1.edgeId, partner.1.edgeId) = (3, 4) ∨
    (terminal.1.edgeId, partner.1.edgeId) = (4, 3) := by
  dsimp only
  have hpairs := reflectedBentGuardGraftPivotActualEdgeIdPairs_eq
    D hextent state hmem
  have hterminal : terminal ∈
      slabLinkPhysicalStrandTerminals 1 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        reflectedBentSwitchPivot reflectedBentPivotLeftAuxiliary hmem :=
    SlabLinkPhysicalStrandTerminal.mem_all 1 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      reflectedBentSwitchPivot reflectedBentPivotLeftAuxiliary hmem terminal
  have hpair :
      (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          reflectedBentSwitchPivot reflectedBentPivotLeftAuxiliary hmem
          terminal).1.edgeId) ∈
        reflectedBentGuardGraftPivotActualEdgeIdPairs
          D hextent state hmem := by
    unfold reflectedBentGuardGraftPivotActualEdgeIdPairs
      slabLinkPhysicalPartnerEdgeIdPairs
    exact List.mem_map.mpr ⟨terminal, hterminal, rfl⟩
  rw [hpairs] at hpair
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using hpair

theorem reflectedBentGuardGraftPivotActual_partner_faceId_pair
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (hmem : reflectedBentPivotLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        reflectedBentSwitchPivot)
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      reflectedBentSwitchPivot reflectedBentPivotLeftAuxiliary hmem) :
    let partner := slabLinkPhysicalStrandPartner 1 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      reflectedBentSwitchPivot reflectedBentPivotLeftAuxiliary hmem terminal
    let sourceFace := (slabLinkPhysicalTerminalOccurrence 1 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      reflectedBentSwitchPivot reflectedBentPivotLeftAuxiliary hmem
      terminal).faceId
    let targetFace := (slabLinkPhysicalTerminalOccurrence 1 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      reflectedBentSwitchPivot reflectedBentPivotLeftAuxiliary hmem
      partner).faceId
    (sourceFace, targetFace) = (13, 45) ∨
    (sourceFace, targetFace) = (45, 13) ∨
    (sourceFace, targetFace) = (46, 47) ∨
    (sourceFace, targetFace) = (47, 46) := by
  dsimp only
  let partner := slabLinkPhysicalStrandPartner 1 5
    (reflectedBentGuardGraftLeftPhysical D hextent state)
    reflectedBentSwitchPivot reflectedBentPivotLeftAuxiliary hmem terminal
  have hpair := reflectedBentGuardGraftPivotActual_partner_position_pair
    D hextent state hmem terminal
  rcases hpair with h02 | h20 | h34 | h43
  · left
    have hs : terminal.1.edgeId = 0 := congrArg Prod.fst h02
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
    have hs : terminal.1.edgeId = 2 := congrArg Prod.fst h20
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
    have hs : terminal.1.edgeId = 3 := congrArg Prod.fst h34
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
    have hs : terminal.1.edgeId = 4 := congrArg Prod.fst h43
    have ht : partner.1.edgeId = 3 := by
      simpa only [partner] using congrArg Prod.snd h43
    apply Prod.ext
    · change (slabIncidentPlaqIds 5 reflectedBentSwitchPivot).get
          ⟨terminal.1.edgeId, terminal.2⟩ = 47
      simp [reflectedBentPivot_incidentFaceIds, hs]
    · change (slabIncidentPlaqIds 5 reflectedBentSwitchPivot).get
          ⟨partner.1.edgeId, partner.2⟩ = 46
      simp [reflectedBentPivot_incidentFaceIds, ht]

theorem reflectedBentConcretePivotFacePair_same_side
    {sourceFaceId targetFaceId : Nat}
    (hpair : (sourceFaceId, targetFaceId) = (13, 45) ∨
      (sourceFaceId, targetFaceId) = (45, 13) ∨
      (sourceFaceId, targetFaceId) = (46, 47) ∨
      (sourceFaceId, targetFaceId) = (47, 46)) :
    (slabPlaquetteAt 5 sourceFaceId ∈ reflectedBentNearSurface ∧
      slabPlaquetteAt 5 targetFaceId ∈ reflectedBentNearSurface) ∨
    (slabPlaquetteAt 5 sourceFaceId ∈ reflectedBentFarSurface ∧
      slabPlaquetteAt 5 targetFaceId ∈ reflectedBentFarSurface) := by
  rcases hpair with hpair | hpair | hpair | hpair
  · have hs := congrArg Prod.fst hpair
    have ht := congrArg Prod.snd hpair
    simp only at hs ht
    subst sourceFaceId
    subst targetFaceId
    left
    constructor <;> decide
  · have hs := congrArg Prod.fst hpair
    have ht := congrArg Prod.snd hpair
    simp only at hs ht
    subst sourceFaceId
    subst targetFaceId
    left
    constructor <;> decide
  · have hs := congrArg Prod.fst hpair
    have ht := congrArg Prod.snd hpair
    simp only at hs ht
    subst sourceFaceId
    subst targetFaceId
    right
    constructor <;> decide
  · have hs := congrArg Prod.fst hpair
    have ht := congrArg Prod.snd hpair
    simp only at hs ht
    subst sourceFaceId
    subst targetFaceId
    right
    constructor <;> decide

theorem reflectedBentGuardGraftPivotTerminal_pair_same_side
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (hmem : reflectedBentPivotLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        reflectedBentSwitchPivot)
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      reflectedBentSwitchPivot reflectedBentPivotLeftAuxiliary hmem) :
    let partner := slabLinkPhysicalStrandPartner 1 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      reflectedBentSwitchPivot reflectedBentPivotLeftAuxiliary hmem terminal
    let sourceFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        reflectedBentSwitchPivot reflectedBentPivotLeftAuxiliary hmem
        terminal).faceId
    let targetFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        reflectedBentSwitchPivot reflectedBentPivotLeftAuxiliary hmem
        partner).faceId
    (sourceFace ∈ reflectedBentNearSurface ∧
      targetFace ∈ reflectedBentNearSurface) ∨
    (sourceFace ∈ reflectedBentFarSurface ∧
      targetFace ∈ reflectedBentFarSurface) := by
  dsimp only
  exact reflectedBentConcretePivotFacePair_same_side
    (reflectedBentGuardGraftPivotActual_partner_faceId_pair
      D hextent state hmem terminal)

theorem reflectedBentGuardGraftRealizedPivotTerminal_pair_same_side
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      reflectedBentSwitchPivot
      (reflectedBentGuardGraftRealizedLeftAuxiliary
        D hcutoff hextent state reflectedBentGuardGraftPivotLinked)
      (reflectedBentGuardGraftRealizedLeftAuxiliary_mem
        D hcutoff hextent state reflectedBentGuardGraftPivotLinked)) :
    let partner := slabLinkPhysicalStrandPartner 1 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      reflectedBentSwitchPivot
      (reflectedBentGuardGraftRealizedLeftAuxiliary
        D hcutoff hextent state reflectedBentGuardGraftPivotLinked)
      (reflectedBentGuardGraftRealizedLeftAuxiliary_mem
        D hcutoff hextent state reflectedBentGuardGraftPivotLinked)
      terminal
    let sourceFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        reflectedBentSwitchPivot
        (reflectedBentGuardGraftRealizedLeftAuxiliary
          D hcutoff hextent state reflectedBentGuardGraftPivotLinked)
        (reflectedBentGuardGraftRealizedLeftAuxiliary_mem
          D hcutoff hextent state reflectedBentGuardGraftPivotLinked)
        terminal).faceId
    let targetFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        reflectedBentSwitchPivot
        (reflectedBentGuardGraftRealizedLeftAuxiliary
          D hcutoff hextent state reflectedBentGuardGraftPivotLinked)
        (reflectedBentGuardGraftRealizedLeftAuxiliary_mem
          D hcutoff hextent state reflectedBentGuardGraftPivotLinked)
        partner).faceId
    (sourceFace ∈ reflectedBentNearSurface ∧
      targetFace ∈ reflectedBentNearSurface) ∨
    (sourceFace ∈ reflectedBentFarSurface ∧
      targetFace ∈ reflectedBentFarSurface) := by
  let realizedAuxiliary := reflectedBentGuardGraftRealizedLeftAuxiliary
    D hcutoff hextent state reflectedBentGuardGraftPivotLinked
  let realized_mem := reflectedBentGuardGraftRealizedLeftAuxiliary_mem
    D hcutoff hextent state reflectedBentGuardGraftPivotLinked
  let pivot_mem := reflectedBentGuardGraftPivotLeftAuxiliary_mem
    D hextent state
  have hpairs :
      slabLinkPhysicalPartnerEdgeIdPairs 1 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          reflectedBentSwitchPivot realizedAuxiliary realized_mem =
        [(0, 2), (2, 0), (3, 4), (4, 3)] := by
    calc
      _ = slabLinkPhysicalPartnerEdgeIdPairs 1 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          reflectedBentSwitchPivot reflectedBentPivotLeftAuxiliary
          pivot_mem :=
        slabLinkPhysicalPartnerEdgeIdPairs_eq_of_auxiliary_eq
          1 5 (reflectedBentGuardGraftLeftPhysical D hextent state)
          reflectedBentSwitchPivot realizedAuxiliary
          reflectedBentPivotLeftAuxiliary
          (reflectedBentGuardGraftRealizedLeftAuxiliary_eq_pivot
            D hcutoff hextent state)
          realized_mem pivot_mem
      _ = [(0, 2), (2, 0), (3, 4), (4, 3)] :=
        reflectedBentGuardGraftPivotActualEdgeIdPairs_eq
          D hextent state pivot_mem
  have hposition :=
    slabLinkPhysicalPartner_position_pair_of_edgeIdPairs_eq
      1 5 (reflectedBentGuardGraftLeftPhysical D hextent state)
      reflectedBentSwitchPivot realizedAuxiliary realized_mem hpairs terminal
  exact reflectedBentConcretePivotFacePair_same_side
    (reflectedBentPivot_partner_faceId_pair_of_position_pair
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      realizedAuxiliary realized_mem terminal hposition)

#print axioms slabLinkPhysicalPartnerEdgeIdPairs_eq_of_externalSpins_eq
#print axioms reflectedBentGuardGraftPivotActualEdgeIdPairs_eq
#print axioms reflectedBentGuardGraftPivotActual_partner_faceId_pair
#print axioms reflectedBentGuardGraftPivotTerminal_pair_same_side
#print axioms reflectedBentGuardGraftRealizedPivotTerminal_pair_same_side

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPivotEdges
