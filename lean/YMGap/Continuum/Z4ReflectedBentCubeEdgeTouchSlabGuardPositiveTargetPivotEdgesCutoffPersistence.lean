/-
# Exact reflected pivot edges at every ambient cutoff

The projected physical-terminal pairing depends on the cutoff only through an
acceptance proof.  Its canonical resolved network is determined by the local
external word and auxiliary labelling.  Combine this cutoff independence with
the ambient realization of the explicit pivot carrier to recover the same
four pivot edge pairs at every cutoff.

Constructive contract: canonical resolved-network equality and finite
incident-face lookup only; no `Classical`, choice, `native_decide`, `sorry`,
new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPivotEdges
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPivotPairingCutoffPersistence

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPivotEdgesCutoffPersistence

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFineIntertwinerCutoffPersistence
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchCutCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTarget
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPivotEdges
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPivotPairing
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPivotPairingCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealizationCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotPairing
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile

/-! ## 1. The projected terminal pairing is cutoff independent -/

theorem slabLinkPhysicalPartnerEdgeIdPairs_eq_of_cutoff
    (leftCutoff rightCutoff extent : Nat)
    (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (left_mem : auxiliary ∈
      slabLinkFusionWitnesses leftCutoff extent physical link)
    (right_mem : auxiliary ∈
      slabLinkFusionWitnesses rightCutoff extent physical link) :
    slabLinkPhysicalPartnerEdgeIdPairs leftCutoff extent physical link
        auxiliary left_mem =
      slabLinkPhysicalPartnerEdgeIdPairs rightCutoff extent physical link
        auxiliary right_mem := by
  rw [slabLinkPhysicalPartnerEdgeIdPairs_eq_canonical,
    slabLinkPhysicalPartnerEdgeIdPairs_eq_canonical]

/-! ## 2. Position pairs give the same four incident-face pairs for any K -/

theorem reflectedBentPivot_partner_faceId_pair_of_position_pair_at_cutoff
    (K : Nat) (physical auxiliary : SlabLabelling)
    (hmem : auxiliary ∈
      slabLinkFusionWitnesses K 5 physical reflectedBentSwitchPivot)
    (terminal : SlabLinkPhysicalStrandTerminal K 5 physical
      reflectedBentSwitchPivot auxiliary hmem)
    (hposition :
      let partner := slabLinkPhysicalStrandPartner K 5 physical
        reflectedBentSwitchPivot auxiliary hmem terminal
      (terminal.1.edgeId, partner.1.edgeId) = (0, 2) ∨
      (terminal.1.edgeId, partner.1.edgeId) = (2, 0) ∨
      (terminal.1.edgeId, partner.1.edgeId) = (3, 4) ∨
      (terminal.1.edgeId, partner.1.edgeId) = (4, 3)) :
    let partner := slabLinkPhysicalStrandPartner K 5 physical
      reflectedBentSwitchPivot auxiliary hmem terminal
    let sourceFace := (slabLinkPhysicalTerminalOccurrence K 5 physical
      reflectedBentSwitchPivot auxiliary hmem terminal).faceId
    let targetFace := (slabLinkPhysicalTerminalOccurrence K 5 physical
      reflectedBentSwitchPivot auxiliary hmem partner).faceId
    (sourceFace, targetFace) = (13, 45) ∨
    (sourceFace, targetFace) = (45, 13) ∨
    (sourceFace, targetFace) = (46, 47) ∨
    (sourceFace, targetFace) = (47, 46) := by
  dsimp only at hposition ⊢
  let partner := slabLinkPhysicalStrandPartner K 5 physical
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

/-! ## 3. The realized ambient pivot preserves each lobe -/

theorem reflectedBentGuardGraftRealizedPivotTerminal_pair_same_side_at_cutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (terminal : SlabLinkPhysicalStrandTerminal D.cutoff 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      reflectedBentSwitchPivot
      (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff
        D hcutoff hextent state reflectedBentGuardGraftPivotLinked)
      (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff_mem
        D hcutoff hextent state reflectedBentGuardGraftPivotLinked)) :
    let partner := slabLinkPhysicalStrandPartner D.cutoff 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      reflectedBentSwitchPivot
      (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff
        D hcutoff hextent state reflectedBentGuardGraftPivotLinked)
      (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff_mem
        D hcutoff hextent state reflectedBentGuardGraftPivotLinked)
      terminal
    let sourceFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence D.cutoff 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        reflectedBentSwitchPivot
        (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff
          D hcutoff hextent state reflectedBentGuardGraftPivotLinked)
        (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff_mem
          D hcutoff hextent state reflectedBentGuardGraftPivotLinked)
        terminal).faceId
    let targetFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence D.cutoff 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        reflectedBentSwitchPivot
        (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff
          D hcutoff hextent state reflectedBentGuardGraftPivotLinked)
        (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff_mem
          D hcutoff hextent state reflectedBentGuardGraftPivotLinked)
        partner).faceId
    (sourceFace ∈ reflectedBentNearSurface ∧
      targetFace ∈ reflectedBentNearSurface) ∨
    (sourceFace ∈ reflectedBentFarSurface ∧
      targetFace ∈ reflectedBentFarSurface) := by
  let realizedAuxiliary :=
    reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff
      D hcutoff hextent state reflectedBentGuardGraftPivotLinked
  let realized_mem :=
    reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff_mem
      D hcutoff hextent state reflectedBentGuardGraftPivotLinked
  let pivot_mem_one := reflectedBentGuardGraftPivotLeftAuxiliary_mem
    D hextent state
  let pivot_mem := slabLinkFusionWitnesses_mem_of_cutoff_le hcutoff
    (reflectedBentGuardGraftLeftPhysical D hextent state)
    reflectedBentSwitchPivot reflectedBentPivotLeftAuxiliary pivot_mem_one
  have hpairs :
      slabLinkPhysicalPartnerEdgeIdPairs D.cutoff 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          reflectedBentSwitchPivot realizedAuxiliary realized_mem =
        [(0, 2), (2, 0), (3, 4), (4, 3)] := by
    calc
      _ = slabLinkPhysicalPartnerEdgeIdPairs D.cutoff 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          reflectedBentSwitchPivot reflectedBentPivotLeftAuxiliary
          pivot_mem :=
        slabLinkPhysicalPartnerEdgeIdPairs_eq_of_auxiliary_eq
          D.cutoff 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          reflectedBentSwitchPivot realizedAuxiliary
          reflectedBentPivotLeftAuxiliary
          (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff_eq_pivot
            D hcutoff hextent state)
          realized_mem pivot_mem
      _ = slabLinkPhysicalPartnerEdgeIdPairs 1 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          reflectedBentSwitchPivot reflectedBentPivotLeftAuxiliary
          pivot_mem_one :=
        slabLinkPhysicalPartnerEdgeIdPairs_eq_of_cutoff
          D.cutoff 1 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          reflectedBentSwitchPivot reflectedBentPivotLeftAuxiliary
          pivot_mem pivot_mem_one
      _ = [(0, 2), (2, 0), (3, 4), (4, 3)] :=
        reflectedBentGuardGraftPivotActualEdgeIdPairs_eq
          D hextent state pivot_mem_one
  have hposition :=
    slabLinkPhysicalPartner_position_pair_of_edgeIdPairs_eq
      D.cutoff 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      reflectedBentSwitchPivot realizedAuxiliary realized_mem hpairs terminal
  exact reflectedBentConcretePivotFacePair_same_side
    (reflectedBentPivot_partner_faceId_pair_of_position_pair_at_cutoff
      D.cutoff
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      realizedAuxiliary realized_mem terminal hposition)

#print axioms slabLinkPhysicalPartnerEdgeIdPairs_eq_of_cutoff
#print axioms reflectedBentPivot_partner_faceId_pair_of_position_pair_at_cutoff
#print axioms reflectedBentGuardGraftRealizedPivotTerminal_pair_same_side_at_cutoff

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPivotEdgesCutoffPersistence
