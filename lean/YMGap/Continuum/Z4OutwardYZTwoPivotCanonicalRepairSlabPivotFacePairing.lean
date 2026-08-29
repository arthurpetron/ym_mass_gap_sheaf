/-
# Actual two-pivot repair strands preserve the two geometric lobes

Transport the two explicit canonical carrier involutions to arbitrary proofs
of accepted production membership.  In the literal corrected-slab face
orders, the spatial pivot pairs face identifiers `33 <-> 231` and
`199 <-> 232`; the temporal pivot pairs `37 <-> 235` and `203 <-> 236`.
Each displayed pair lies wholly in one of the two repair lobes.

Constructive contract: proof-independent transport of explicit finite
terminal lists only; no choice, `Classical`, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabPivotPairing

namespace YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabPivotFacePairing

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairCutCarrier
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabPivotPairing
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabSwitchingProfile

/-! ## 1. Spatial pivot -/

def outwardYZCanonicalRepairSpatialActualEdgeIdPairs
    (hmem : outwardYZCanonicalRepairSpatialLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchSpatialPivot) : List (Nat × Nat) :=
  (slabLinkPhysicalStrandTerminals 1 5
    outwardYZCanonicalRepairSwitchLeftPhysical
    outwardYZCanonicalRepairSwitchSpatialPivot
    outwardYZCanonicalRepairSpatialLeftAuxiliary hmem).map fun terminal =>
      (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5
          outwardYZCanonicalRepairSwitchLeftPhysical
          outwardYZCanonicalRepairSwitchSpatialPivot
          outwardYZCanonicalRepairSpatialLeftAuxiliary hmem terminal).1.edgeId)

theorem outwardYZCanonicalRepairSpatialActualEdgeIdPairs_exact
    (hmem : outwardYZCanonicalRepairSpatialLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchSpatialPivot) :
    outwardYZCanonicalRepairSpatialActualEdgeIdPairs hmem =
      [(0, 2), (1, 3), (2, 0), (3, 1)] := by
  unfold outwardYZCanonicalRepairSpatialActualEdgeIdPairs
    slabLinkPhysicalStrandTerminals slabLinkPhysicalStrandPartner
  simp only [outwardYZCanonicalRepairSwitchSpatialPivot_degree_five]
  change outwardYZCanonicalRepairSpatialCanonicalEdgeIdPairs =
    [(0, 2), (1, 3), (2, 0), (3, 1)]
  exact outwardYZCanonicalRepairSpatialCanonicalEdgeIdPairs_exact

theorem outwardYZCanonicalRepairSpatialActual_partner_position_pair
    (hmem : outwardYZCanonicalRepairSpatialLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchSpatialPivot)
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchSpatialPivot
      outwardYZCanonicalRepairSpatialLeftAuxiliary hmem) :
    (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5
          outwardYZCanonicalRepairSwitchLeftPhysical
          outwardYZCanonicalRepairSwitchSpatialPivot
          outwardYZCanonicalRepairSpatialLeftAuxiliary hmem terminal).1.edgeId) =
        (0, 2) ∨
    (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5
          outwardYZCanonicalRepairSwitchLeftPhysical
          outwardYZCanonicalRepairSwitchSpatialPivot
          outwardYZCanonicalRepairSpatialLeftAuxiliary hmem terminal).1.edgeId) =
        (1, 3) ∨
    (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5
          outwardYZCanonicalRepairSwitchLeftPhysical
          outwardYZCanonicalRepairSwitchSpatialPivot
          outwardYZCanonicalRepairSpatialLeftAuxiliary hmem terminal).1.edgeId) =
        (2, 0) ∨
    (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5
          outwardYZCanonicalRepairSwitchLeftPhysical
          outwardYZCanonicalRepairSwitchSpatialPivot
          outwardYZCanonicalRepairSpatialLeftAuxiliary hmem terminal).1.edgeId) =
        (3, 1) := by
  have hpairs := outwardYZCanonicalRepairSpatialActualEdgeIdPairs_exact hmem
  have hterminal : terminal ∈
      slabLinkPhysicalStrandTerminals 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchSpatialPivot
        outwardYZCanonicalRepairSpatialLeftAuxiliary hmem :=
    SlabLinkPhysicalStrandTerminal.mem_all 1 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchSpatialPivot
      outwardYZCanonicalRepairSpatialLeftAuxiliary hmem terminal
  have hpair :
      (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5
          outwardYZCanonicalRepairSwitchLeftPhysical
          outwardYZCanonicalRepairSwitchSpatialPivot
          outwardYZCanonicalRepairSpatialLeftAuxiliary hmem terminal).1.edgeId) ∈
        outwardYZCanonicalRepairSpatialActualEdgeIdPairs hmem := by
    unfold outwardYZCanonicalRepairSpatialActualEdgeIdPairs
    exact List.mem_map.mpr ⟨terminal, hterminal, rfl⟩
  rw [hpairs] at hpair
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using hpair

theorem outwardYZCanonicalRepairSpatialPivot_incidentFaceIds :
    slabIncidentPlaqIds 5 outwardYZCanonicalRepairSwitchSpatialPivot =
      [33, 199, 231, 232, 233] := by
  decide

theorem outwardYZCanonicalRepairSpatialActual_partner_faceId_pair
    (hmem : outwardYZCanonicalRepairSpatialLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchSpatialPivot)
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchSpatialPivot
      outwardYZCanonicalRepairSpatialLeftAuxiliary hmem) :
    let partner := slabLinkPhysicalStrandPartner 1 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchSpatialPivot
      outwardYZCanonicalRepairSpatialLeftAuxiliary hmem terminal
    let sourceFace := (slabLinkPhysicalTerminalOccurrence 1 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchSpatialPivot
      outwardYZCanonicalRepairSpatialLeftAuxiliary hmem terminal).faceId
    let targetFace := (slabLinkPhysicalTerminalOccurrence 1 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchSpatialPivot
      outwardYZCanonicalRepairSpatialLeftAuxiliary hmem partner).faceId
    (sourceFace, targetFace) = (33, 231) ∨
    (sourceFace, targetFace) = (199, 232) ∨
    (sourceFace, targetFace) = (231, 33) ∨
    (sourceFace, targetFace) = (232, 199) := by
  dsimp only
  let partner := slabLinkPhysicalStrandPartner 1 5
    outwardYZCanonicalRepairSwitchLeftPhysical
    outwardYZCanonicalRepairSwitchSpatialPivot
    outwardYZCanonicalRepairSpatialLeftAuxiliary hmem terminal
  have hpair :=
    outwardYZCanonicalRepairSpatialActual_partner_position_pair hmem terminal
  rcases hpair with h02 | h13 | h20 | h31
  · left
    have hs : terminal.1.edgeId = 0 := by
      simpa only using congrArg Prod.fst h02
    have ht : partner.1.edgeId = 2 := by
      simpa only [partner] using congrArg Prod.snd h02
    apply Prod.ext
    · change (slabIncidentPlaqIds 5
          outwardYZCanonicalRepairSwitchSpatialPivot).get
            ⟨terminal.1.edgeId, terminal.2⟩ = 33
      simp [outwardYZCanonicalRepairSpatialPivot_incidentFaceIds, hs]
    · change (slabIncidentPlaqIds 5
          outwardYZCanonicalRepairSwitchSpatialPivot).get
            ⟨partner.1.edgeId, partner.2⟩ = 231
      simp [outwardYZCanonicalRepairSpatialPivot_incidentFaceIds, ht]
  · right; left
    have hs : terminal.1.edgeId = 1 := by
      simpa only using congrArg Prod.fst h13
    have ht : partner.1.edgeId = 3 := by
      simpa only [partner] using congrArg Prod.snd h13
    apply Prod.ext
    · change (slabIncidentPlaqIds 5
          outwardYZCanonicalRepairSwitchSpatialPivot).get
            ⟨terminal.1.edgeId, terminal.2⟩ = 199
      simp [outwardYZCanonicalRepairSpatialPivot_incidentFaceIds, hs]
    · change (slabIncidentPlaqIds 5
          outwardYZCanonicalRepairSwitchSpatialPivot).get
            ⟨partner.1.edgeId, partner.2⟩ = 232
      simp [outwardYZCanonicalRepairSpatialPivot_incidentFaceIds, ht]
  · right; right; left
    have hs : terminal.1.edgeId = 2 := by
      simpa only using congrArg Prod.fst h20
    have ht : partner.1.edgeId = 0 := by
      simpa only [partner] using congrArg Prod.snd h20
    apply Prod.ext
    · change (slabIncidentPlaqIds 5
          outwardYZCanonicalRepairSwitchSpatialPivot).get
            ⟨terminal.1.edgeId, terminal.2⟩ = 231
      simp [outwardYZCanonicalRepairSpatialPivot_incidentFaceIds, hs]
    · change (slabIncidentPlaqIds 5
          outwardYZCanonicalRepairSwitchSpatialPivot).get
            ⟨partner.1.edgeId, partner.2⟩ = 33
      simp [outwardYZCanonicalRepairSpatialPivot_incidentFaceIds, ht]
  · right; right; right
    have hs : terminal.1.edgeId = 3 := by
      simpa only using congrArg Prod.fst h31
    have ht : partner.1.edgeId = 1 := by
      simpa only [partner] using congrArg Prod.snd h31
    apply Prod.ext
    · change (slabIncidentPlaqIds 5
          outwardYZCanonicalRepairSwitchSpatialPivot).get
            ⟨terminal.1.edgeId, terminal.2⟩ = 232
      simp [outwardYZCanonicalRepairSpatialPivot_incidentFaceIds, hs]
    · change (slabIncidentPlaqIds 5
          outwardYZCanonicalRepairSwitchSpatialPivot).get
            ⟨partner.1.edgeId, partner.2⟩ = 199
      simp [outwardYZCanonicalRepairSpatialPivot_incidentFaceIds, ht]

theorem outwardYZCanonicalRepairSpatialTerminal_pair_same_side
    (hmem : outwardYZCanonicalRepairSpatialLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchSpatialPivot)
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchSpatialPivot
      outwardYZCanonicalRepairSpatialLeftAuxiliary hmem) :
    let partner := slabLinkPhysicalStrandPartner 1 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchSpatialPivot
      outwardYZCanonicalRepairSpatialLeftAuxiliary hmem terminal
    let sourceFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchSpatialPivot
        outwardYZCanonicalRepairSpatialLeftAuxiliary hmem terminal).faceId
    let targetFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchSpatialPivot
        outwardYZCanonicalRepairSpatialLeftAuxiliary hmem partner).faceId
    (sourceFace ∈ outwardYZCanonicalRepairTargetLobe ∧
        targetFace ∈ outwardYZCanonicalRepairTargetLobe) ∨
      (sourceFace ∈ outwardYZCanonicalRepairRootLobe ∧
        targetFace ∈ outwardYZCanonicalRepairRootLobe) := by
  dsimp only
  have hfaces :=
    outwardYZCanonicalRepairSpatialActual_partner_faceId_pair hmem terminal
  rcases hfaces with htarget | hroot | htarget | hroot
  · left
    have hs := congrArg Prod.fst htarget
    have ht := congrArg Prod.snd htarget
    simp only at hs ht
    rw [hs, ht]
    constructor <;> decide
  · right
    have hs := congrArg Prod.fst hroot
    have ht := congrArg Prod.snd hroot
    simp only at hs ht
    rw [hs, ht]
    constructor <;> decide
  · left
    have hs := congrArg Prod.fst htarget
    have ht := congrArg Prod.snd htarget
    simp only at hs ht
    rw [hs, ht]
    constructor <;> decide
  · right
    have hs := congrArg Prod.fst hroot
    have ht := congrArg Prod.snd hroot
    simp only at hs ht
    rw [hs, ht]
    constructor <;> decide

/-! ## 2. Temporal pivot -/

def outwardYZCanonicalRepairTemporalActualEdgeIdPairs
    (hmem : outwardYZCanonicalRepairTemporalLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchTemporalPivot) : List (Nat × Nat) :=
  (slabLinkPhysicalStrandTerminals 1 5
    outwardYZCanonicalRepairSwitchLeftPhysical
    outwardYZCanonicalRepairSwitchTemporalPivot
    outwardYZCanonicalRepairTemporalLeftAuxiliary hmem).map fun terminal =>
      (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5
          outwardYZCanonicalRepairSwitchLeftPhysical
          outwardYZCanonicalRepairSwitchTemporalPivot
          outwardYZCanonicalRepairTemporalLeftAuxiliary hmem terminal).1.edgeId)

theorem outwardYZCanonicalRepairTemporalActualEdgeIdPairs_exact
    (hmem : outwardYZCanonicalRepairTemporalLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchTemporalPivot) :
    outwardYZCanonicalRepairTemporalActualEdgeIdPairs hmem =
      [(0, 3), (1, 4), (3, 0), (4, 1)] := by
  unfold outwardYZCanonicalRepairTemporalActualEdgeIdPairs
    slabLinkPhysicalStrandTerminals slabLinkPhysicalStrandPartner
  simp only [outwardYZCanonicalRepairSwitchTemporalPivot_degree_five]
  change outwardYZCanonicalRepairTemporalCanonicalEdgeIdPairs =
    [(0, 3), (1, 4), (3, 0), (4, 1)]
  exact outwardYZCanonicalRepairTemporalCanonicalEdgeIdPairs_exact

theorem outwardYZCanonicalRepairTemporalActual_partner_position_pair
    (hmem : outwardYZCanonicalRepairTemporalLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchTemporalPivot)
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchTemporalPivot
      outwardYZCanonicalRepairTemporalLeftAuxiliary hmem) :
    (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5
          outwardYZCanonicalRepairSwitchLeftPhysical
          outwardYZCanonicalRepairSwitchTemporalPivot
          outwardYZCanonicalRepairTemporalLeftAuxiliary hmem terminal).1.edgeId) =
        (0, 3) ∨
    (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5
          outwardYZCanonicalRepairSwitchLeftPhysical
          outwardYZCanonicalRepairSwitchTemporalPivot
          outwardYZCanonicalRepairTemporalLeftAuxiliary hmem terminal).1.edgeId) =
        (1, 4) ∨
    (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5
          outwardYZCanonicalRepairSwitchLeftPhysical
          outwardYZCanonicalRepairSwitchTemporalPivot
          outwardYZCanonicalRepairTemporalLeftAuxiliary hmem terminal).1.edgeId) =
        (3, 0) ∨
    (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5
          outwardYZCanonicalRepairSwitchLeftPhysical
          outwardYZCanonicalRepairSwitchTemporalPivot
          outwardYZCanonicalRepairTemporalLeftAuxiliary hmem terminal).1.edgeId) =
        (4, 1) := by
  have hpairs := outwardYZCanonicalRepairTemporalActualEdgeIdPairs_exact hmem
  have hterminal : terminal ∈
      slabLinkPhysicalStrandTerminals 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchTemporalPivot
        outwardYZCanonicalRepairTemporalLeftAuxiliary hmem :=
    SlabLinkPhysicalStrandTerminal.mem_all 1 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchTemporalPivot
      outwardYZCanonicalRepairTemporalLeftAuxiliary hmem terminal
  have hpair :
      (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5
          outwardYZCanonicalRepairSwitchLeftPhysical
          outwardYZCanonicalRepairSwitchTemporalPivot
          outwardYZCanonicalRepairTemporalLeftAuxiliary hmem terminal).1.edgeId) ∈
        outwardYZCanonicalRepairTemporalActualEdgeIdPairs hmem := by
    unfold outwardYZCanonicalRepairTemporalActualEdgeIdPairs
    exact List.mem_map.mpr ⟨terminal, hterminal, rfl⟩
  rw [hpairs] at hpair
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using hpair

theorem outwardYZCanonicalRepairTemporalPivot_incidentFaceIds :
    slabIncidentPlaqIds 5 outwardYZCanonicalRepairSwitchTemporalPivot =
      [37, 203, 233, 235, 236] := by
  decide

theorem outwardYZCanonicalRepairTemporalActual_partner_faceId_pair
    (hmem : outwardYZCanonicalRepairTemporalLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchTemporalPivot)
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchTemporalPivot
      outwardYZCanonicalRepairTemporalLeftAuxiliary hmem) :
    let partner := slabLinkPhysicalStrandPartner 1 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchTemporalPivot
      outwardYZCanonicalRepairTemporalLeftAuxiliary hmem terminal
    let sourceFace := (slabLinkPhysicalTerminalOccurrence 1 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchTemporalPivot
      outwardYZCanonicalRepairTemporalLeftAuxiliary hmem terminal).faceId
    let targetFace := (slabLinkPhysicalTerminalOccurrence 1 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchTemporalPivot
      outwardYZCanonicalRepairTemporalLeftAuxiliary hmem partner).faceId
    (sourceFace, targetFace) = (37, 235) ∨
    (sourceFace, targetFace) = (203, 236) ∨
    (sourceFace, targetFace) = (235, 37) ∨
    (sourceFace, targetFace) = (236, 203) := by
  dsimp only
  let partner := slabLinkPhysicalStrandPartner 1 5
    outwardYZCanonicalRepairSwitchLeftPhysical
    outwardYZCanonicalRepairSwitchTemporalPivot
    outwardYZCanonicalRepairTemporalLeftAuxiliary hmem terminal
  have hpair :=
    outwardYZCanonicalRepairTemporalActual_partner_position_pair hmem terminal
  rcases hpair with h03 | h14 | h30 | h41
  · left
    have hs : terminal.1.edgeId = 0 := by
      simpa only using congrArg Prod.fst h03
    have ht : partner.1.edgeId = 3 := by
      simpa only [partner] using congrArg Prod.snd h03
    apply Prod.ext
    · change (slabIncidentPlaqIds 5
          outwardYZCanonicalRepairSwitchTemporalPivot).get
            ⟨terminal.1.edgeId, terminal.2⟩ = 37
      simp [outwardYZCanonicalRepairTemporalPivot_incidentFaceIds, hs]
    · change (slabIncidentPlaqIds 5
          outwardYZCanonicalRepairSwitchTemporalPivot).get
            ⟨partner.1.edgeId, partner.2⟩ = 235
      simp [outwardYZCanonicalRepairTemporalPivot_incidentFaceIds, ht]
  · right; left
    have hs : terminal.1.edgeId = 1 := by
      simpa only using congrArg Prod.fst h14
    have ht : partner.1.edgeId = 4 := by
      simpa only [partner] using congrArg Prod.snd h14
    apply Prod.ext
    · change (slabIncidentPlaqIds 5
          outwardYZCanonicalRepairSwitchTemporalPivot).get
            ⟨terminal.1.edgeId, terminal.2⟩ = 203
      simp [outwardYZCanonicalRepairTemporalPivot_incidentFaceIds, hs]
    · change (slabIncidentPlaqIds 5
          outwardYZCanonicalRepairSwitchTemporalPivot).get
            ⟨partner.1.edgeId, partner.2⟩ = 236
      simp [outwardYZCanonicalRepairTemporalPivot_incidentFaceIds, ht]
  · right; right; left
    have hs : terminal.1.edgeId = 3 := by
      simpa only using congrArg Prod.fst h30
    have ht : partner.1.edgeId = 0 := by
      simpa only [partner] using congrArg Prod.snd h30
    apply Prod.ext
    · change (slabIncidentPlaqIds 5
          outwardYZCanonicalRepairSwitchTemporalPivot).get
            ⟨terminal.1.edgeId, terminal.2⟩ = 235
      simp [outwardYZCanonicalRepairTemporalPivot_incidentFaceIds, hs]
    · change (slabIncidentPlaqIds 5
          outwardYZCanonicalRepairSwitchTemporalPivot).get
            ⟨partner.1.edgeId, partner.2⟩ = 37
      simp [outwardYZCanonicalRepairTemporalPivot_incidentFaceIds, ht]
  · right; right; right
    have hs : terminal.1.edgeId = 4 := by
      simpa only using congrArg Prod.fst h41
    have ht : partner.1.edgeId = 1 := by
      simpa only [partner] using congrArg Prod.snd h41
    apply Prod.ext
    · change (slabIncidentPlaqIds 5
          outwardYZCanonicalRepairSwitchTemporalPivot).get
            ⟨terminal.1.edgeId, terminal.2⟩ = 236
      simp [outwardYZCanonicalRepairTemporalPivot_incidentFaceIds, hs]
    · change (slabIncidentPlaqIds 5
          outwardYZCanonicalRepairSwitchTemporalPivot).get
            ⟨partner.1.edgeId, partner.2⟩ = 203
      simp [outwardYZCanonicalRepairTemporalPivot_incidentFaceIds, ht]

theorem outwardYZCanonicalRepairTemporalTerminal_pair_same_side
    (hmem : outwardYZCanonicalRepairTemporalLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchTemporalPivot)
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchTemporalPivot
      outwardYZCanonicalRepairTemporalLeftAuxiliary hmem) :
    let partner := slabLinkPhysicalStrandPartner 1 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchTemporalPivot
      outwardYZCanonicalRepairTemporalLeftAuxiliary hmem terminal
    let sourceFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchTemporalPivot
        outwardYZCanonicalRepairTemporalLeftAuxiliary hmem terminal).faceId
    let targetFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchTemporalPivot
        outwardYZCanonicalRepairTemporalLeftAuxiliary hmem partner).faceId
    (sourceFace ∈ outwardYZCanonicalRepairTargetLobe ∧
        targetFace ∈ outwardYZCanonicalRepairTargetLobe) ∨
      (sourceFace ∈ outwardYZCanonicalRepairRootLobe ∧
        targetFace ∈ outwardYZCanonicalRepairRootLobe) := by
  dsimp only
  have hfaces :=
    outwardYZCanonicalRepairTemporalActual_partner_faceId_pair hmem terminal
  rcases hfaces with htarget | hroot | htarget | hroot
  · left
    have hs := congrArg Prod.fst htarget
    have ht := congrArg Prod.snd htarget
    simp only at hs ht
    rw [hs, ht]
    constructor <;> decide
  · right
    have hs := congrArg Prod.fst hroot
    have ht := congrArg Prod.snd hroot
    simp only at hs ht
    rw [hs, ht]
    constructor <;> decide
  · left
    have hs := congrArg Prod.fst htarget
    have ht := congrArg Prod.snd htarget
    simp only at hs ht
    rw [hs, ht]
    constructor <;> decide
  · right
    have hs := congrArg Prod.fst hroot
    have ht := congrArg Prod.snd hroot
    simp only at hs ht
    rw [hs, ht]
    constructor <;> decide

#print axioms outwardYZCanonicalRepairSpatialActualEdgeIdPairs_exact
#print axioms outwardYZCanonicalRepairSpatialActual_partner_faceId_pair
#print axioms outwardYZCanonicalRepairSpatialTerminal_pair_same_side
#print axioms outwardYZCanonicalRepairTemporalActualEdgeIdPairs_exact
#print axioms outwardYZCanonicalRepairTemporalActual_partner_faceId_pair
#print axioms outwardYZCanonicalRepairTemporalTerminal_pair_same_side

end YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabPivotFacePairing
