/-
# The concrete outward Y/Z pivot carrier pairs across the cut

The selected degree-five production carrier has external word
`[1,1,1,1,0]` and auxiliary word `(2,1)`.  Its three trivalent vertices
therefore route the four physical strands as `0 <-> 2` and `1 <-> 3`.
Together with the literal pivot face order `Z,Y,Y,Z,0`, both pairs cross the
geometric cut.  This module therefore identifies the selected carrier as a
connected channel and rules it out as the sought disconnection witness.

Constructive contract: explicit finite terminal enumeration only; no choice,
`Classical`, `native_decide`, `sorry`, new axiom, noncomputable declaration,
or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
import YMGap.Continuum.Z4OutwardYZEdgeTouchSlabPivotCarrier

namespace YMGap.Continuum.Z4OutwardYZEdgeTouchSlabPivotPairing

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CanonicalLinkEdgeOccurrenceMultiplicity
open YMGap.Continuum.CanonicalLinkPhysicalTerminalPartner
open YMGap.Continuum.CanonicalLinkStrandStep
open YMGap.Continuum.CanonicalLinkStrandTerminal
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.SU2CanonicalLeftCarrierWitnessReconstruction
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabWholeProductPositivity

theorem outwardYZSwitchLeftPhysical_bounded :
    SlabFaceLabellingBounded 1 5 outwardYZSwitchLeftPhysical := by
  intro faceId _
  exact slabBinarySupportLabelling_le_one
    5 outwardYZSwitchSurface faceId

theorem outwardYZPivotLeftAuxiliary_mem :
    outwardYZPivotLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5 outwardYZSwitchLeftPhysical
        outwardYZSwitchPivot :=
  valenceFiveLeftAuxiliary_mem_slabLinkFusionWitnesses
    outwardYZSwitchLeftPhysical_bounded
    outwardYZSwitchPivot_degree_five
    outwardYZPivotLeftSource

/-! ## The proof-independent local pairing computation -/

def outwardYZPivotLeftAllowed :
    YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
      5
      (slabLinkExternalSpins 5 outwardYZSwitchLeftPhysical
        outwardYZSwitchPivot)
      outwardYZPivotLeftAuxiliary = true := by
  decide

def outwardYZPivotCanonicalPhysicalTerminals :
    List (CanonicalPhysicalStrandPort
      (slabLinkExternalSpins 5 outwardYZSwitchLeftPhysical
        outwardYZSwitchPivot)
      outwardYZPivotLeftAuxiliary outwardYZPivotLeftAllowed) :=
  (allResolvedNetworkPorts
    (canonicalLinkResolvedStrandNetwork 5
      (slabLinkExternalSpins 5 outwardYZSwitchLeftPhysical
        outwardYZSwitchPivot)
      outwardYZPivotLeftAuxiliary outwardYZPivotLeftAllowed)).filterMap
        fun occurrence =>
          if hphysical : occurrence.edgeId < 5 then
            some ⟨occurrence, hphysical⟩
          else none

def outwardYZPivot_degree_le : 5 ≤
    YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff.linkIncidenceBound := by
  decide

def outwardYZPivotCanonicalEdgeIdPairs : List (Nat × Nat) :=
  outwardYZPivotCanonicalPhysicalTerminals.map fun terminal =>
    (terminal.1.edgeId,
      (canonicalPhysicalStrandPartner outwardYZPivot_degree_le
        outwardYZPivotLeftAllowed terminal).1.edgeId)

abbrev OutwardYZPivotResolvedPort := ResolvedNetworkPort
  (canonicalLinkResolvedStrandNetwork 5
    (slabLinkExternalSpins 5 outwardYZSwitchLeftPhysical
      outwardYZSwitchPivot)
    outwardYZPivotLeftAuxiliary outwardYZPivotLeftAllowed)

def outwardYZPivotPortZero : OutwardYZPivotResolvedPort where
  vertexIndex := ⟨0, by decide⟩
  port := .onA ⟨0, by decide⟩

def outwardYZPivotPortOne : OutwardYZPivotResolvedPort where
  vertexIndex := ⟨0, by decide⟩
  port := .onB ⟨0, by decide⟩

def outwardYZPivotPortTwo : OutwardYZPivotResolvedPort where
  vertexIndex := ⟨1, by decide⟩
  port := .onB ⟨0, by decide⟩

def outwardYZPivotPortThree : OutwardYZPivotResolvedPort where
  vertexIndex := ⟨2, by decide⟩
  port := .onB ⟨0, by decide⟩

def outwardYZPivotPortSeven : OutwardYZPivotResolvedPort where
  vertexIndex := ⟨1, by decide⟩
  port := .onC ⟨0, by decide⟩

def outwardYZPivotTerminalZero : CanonicalPhysicalStrandPort
    (slabLinkExternalSpins 5 outwardYZSwitchLeftPhysical
      outwardYZSwitchPivot)
    outwardYZPivotLeftAuxiliary outwardYZPivotLeftAllowed :=
  ⟨outwardYZPivotPortZero, by decide⟩

def outwardYZPivotTerminalOne : CanonicalPhysicalStrandPort
    (slabLinkExternalSpins 5 outwardYZSwitchLeftPhysical
      outwardYZSwitchPivot)
    outwardYZPivotLeftAuxiliary outwardYZPivotLeftAllowed :=
  ⟨outwardYZPivotPortOne, by decide⟩

def outwardYZPivotTerminalTwo : CanonicalPhysicalStrandPort
    (slabLinkExternalSpins 5 outwardYZSwitchLeftPhysical
      outwardYZSwitchPivot)
    outwardYZPivotLeftAuxiliary outwardYZPivotLeftAllowed :=
  ⟨outwardYZPivotPortTwo, by decide⟩

def outwardYZPivotTerminalThree : CanonicalPhysicalStrandPort
    (slabLinkExternalSpins 5 outwardYZSwitchLeftPhysical
      outwardYZSwitchPivot)
    outwardYZPivotLeftAuxiliary outwardYZPivotLeftAllowed :=
  ⟨outwardYZPivotPortThree, by decide⟩

def outwardYZPivotZeroMate_internal :
    outwardYZPivotTerminalZero.1.localMate.edgeId ∈
      canonicalInternalFusionEdges 5 := by
  decide

theorem outwardYZPivotZeroMate_advance_eq :
    canonicalInternalAdvancePort outwardYZPivot_degree_le outwardYZPivotLeftAllowed
      outwardYZPivotTerminalZero.1.localMate
      outwardYZPivotZeroMate_internal = outwardYZPivotTerminalTwo.1 := by
  apply ResolvedNetworkPort.address_injective
  decide

def outwardYZPivotZeroToTwoPath : CanonicalStrandPathToPhysical
    outwardYZPivot_degree_le outwardYZPivotLeftAllowed
    outwardYZPivotTerminalZero.1.localMate
    outwardYZPivotTerminalTwo := by
  refine .advance outwardYZPivotTerminalZero.1.localMate
    outwardYZPivotZeroMate_internal
    outwardYZPivotTerminalTwo ?_
  rw [outwardYZPivotZeroMate_advance_eq]
  exact .stop outwardYZPivotTerminalTwo

def outwardYZPivotOneMate_internal :
    outwardYZPivotTerminalOne.1.localMate.edgeId ∈
      canonicalInternalFusionEdges 5 := by
  decide

theorem outwardYZPivotOneMate_advance_eq :
    canonicalInternalAdvancePort outwardYZPivot_degree_le outwardYZPivotLeftAllowed
      outwardYZPivotTerminalOne.1.localMate
      outwardYZPivotOneMate_internal = outwardYZPivotPortSeven := by
  apply ResolvedNetworkPort.address_injective
  decide

def outwardYZPivotPortSeven_internal :
    outwardYZPivotPortSeven.edgeId ∈ canonicalInternalFusionEdges 5 := by
  decide

theorem outwardYZPivotPortSeven_advance_eq :
    canonicalInternalAdvancePort outwardYZPivot_degree_le outwardYZPivotLeftAllowed
      outwardYZPivotPortSeven outwardYZPivotPortSeven_internal =
        outwardYZPivotTerminalThree.1 := by
  apply ResolvedNetworkPort.address_injective
  decide

def outwardYZPivotOneToThreePath : CanonicalStrandPathToPhysical
    outwardYZPivot_degree_le outwardYZPivotLeftAllowed
    outwardYZPivotTerminalOne.1.localMate
    outwardYZPivotTerminalThree := by
  refine .advance outwardYZPivotTerminalOne.1.localMate
    outwardYZPivotOneMate_internal outwardYZPivotTerminalThree ?_
  rw [outwardYZPivotOneMate_advance_eq]
  refine .advance outwardYZPivotPortSeven
    outwardYZPivotPortSeven_internal outwardYZPivotTerminalThree ?_
  rw [outwardYZPivotPortSeven_advance_eq]
  exact .stop outwardYZPivotTerminalThree

theorem outwardYZPivotPartner_zero_eq_two :
    canonicalPhysicalStrandPartner outwardYZPivot_degree_le
      outwardYZPivotLeftAllowed outwardYZPivotTerminalZero =
        outwardYZPivotTerminalTwo :=
  canonicalStrandPath_terminal_unique
    (canonicalPhysicalStrandPartner_path outwardYZPivot_degree_le
      outwardYZPivotLeftAllowed outwardYZPivotTerminalZero)
    outwardYZPivotZeroToTwoPath

theorem outwardYZPivotPartner_one_eq_three :
    canonicalPhysicalStrandPartner outwardYZPivot_degree_le
      outwardYZPivotLeftAllowed outwardYZPivotTerminalOne =
        outwardYZPivotTerminalThree :=
  canonicalStrandPath_terminal_unique
    (canonicalPhysicalStrandPartner_path outwardYZPivot_degree_le
      outwardYZPivotLeftAllowed outwardYZPivotTerminalOne)
    outwardYZPivotOneToThreePath

theorem outwardYZPivotPartner_two_eq_zero :
    canonicalPhysicalStrandPartner outwardYZPivot_degree_le
      outwardYZPivotLeftAllowed outwardYZPivotTerminalTwo =
        outwardYZPivotTerminalZero := by
  rw [← outwardYZPivotPartner_zero_eq_two]
  exact canonicalPhysicalStrandPartner_involutive outwardYZPivot_degree_le
    outwardYZPivotLeftAllowed outwardYZPivotTerminalZero

theorem outwardYZPivotPartner_three_eq_one :
    canonicalPhysicalStrandPartner outwardYZPivot_degree_le
      outwardYZPivotLeftAllowed outwardYZPivotTerminalThree =
        outwardYZPivotTerminalOne := by
  rw [← outwardYZPivotPartner_one_eq_three]
  exact canonicalPhysicalStrandPartner_involutive outwardYZPivot_degree_le
    outwardYZPivotLeftAllowed outwardYZPivotTerminalOne

theorem outwardYZPivotCanonicalPhysicalTerminals_eq :
    outwardYZPivotCanonicalPhysicalTerminals =
      [outwardYZPivotTerminalZero, outwardYZPivotTerminalOne,
       outwardYZPivotTerminalTwo, outwardYZPivotTerminalThree] := by
  decide

theorem outwardYZPivotCanonicalEdgeIdPairs_eq :
    outwardYZPivotCanonicalEdgeIdPairs =
      [(0, 2), (1, 3), (2, 0), (3, 1)] := by
  unfold outwardYZPivotCanonicalEdgeIdPairs
  rw [outwardYZPivotCanonicalPhysicalTerminals_eq]
  simp only [List.map_cons, List.map_nil]
  rw [outwardYZPivotPartner_zero_eq_two,
    outwardYZPivotPartner_one_eq_three,
    outwardYZPivotPartner_two_eq_zero,
    outwardYZPivotPartner_three_eq_one]
  decide

/-! ## Transport to every literal accepted membership proof -/

def outwardYZPivotActualEdgeIdPairs
    (hmem : outwardYZPivotLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5 outwardYZSwitchLeftPhysical
        outwardYZSwitchPivot) : List (Nat × Nat) :=
  (slabLinkPhysicalStrandTerminals 1 5 outwardYZSwitchLeftPhysical
    outwardYZSwitchPivot outwardYZPivotLeftAuxiliary hmem).map
      fun terminal =>
        (terminal.1.edgeId,
          (slabLinkPhysicalStrandPartner 1 5 outwardYZSwitchLeftPhysical
            outwardYZSwitchPivot outwardYZPivotLeftAuxiliary hmem
            terminal).1.edgeId)

theorem outwardYZPivotActualEdgeIdPairs_eq
    (hmem : outwardYZPivotLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5 outwardYZSwitchLeftPhysical
        outwardYZSwitchPivot) :
    outwardYZPivotActualEdgeIdPairs hmem =
      [(0, 2), (1, 3), (2, 0), (3, 1)] := by
  unfold outwardYZPivotActualEdgeIdPairs slabLinkPhysicalStrandTerminals
    slabLinkPhysicalStrandPartner
  simp only [outwardYZSwitchPivot_degree_five]
  change outwardYZPivotCanonicalEdgeIdPairs =
    [(0, 2), (1, 3), (2, 0), (3, 1)]
  exact outwardYZPivotCanonicalEdgeIdPairs_eq

/-- Equal-rank source realization does not preserve the native target-tree
pairing.  This is the exact basis-coherence obstruction at the pivot. -/
theorem outwardYZPivotActualEdgeIdPairs_ne_native
    (hmem : outwardYZPivotLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5 outwardYZSwitchLeftPhysical
        outwardYZSwitchPivot) :
    outwardYZPivotActualEdgeIdPairs hmem ≠
      outwardYZPivotNativeRightEdgeIdPairs := by
  rw [outwardYZPivotActualEdgeIdPairs_eq]
  decide

/-- Every actual pivot terminal lies in one of the two written carrier pairs.
In the actual geometric order, positions zero and three are Z faces while
positions one and two are Y faces. -/
theorem outwardYZPivotActual_partner_position_pair
    (hmem : outwardYZPivotLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5 outwardYZSwitchLeftPhysical
        outwardYZSwitchPivot)
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      outwardYZSwitchLeftPhysical outwardYZSwitchPivot
      outwardYZPivotLeftAuxiliary hmem) :
    (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5 outwardYZSwitchLeftPhysical
          outwardYZSwitchPivot outwardYZPivotLeftAuxiliary hmem
          terminal).1.edgeId) = (0, 2) ∨
    (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5 outwardYZSwitchLeftPhysical
          outwardYZSwitchPivot outwardYZPivotLeftAuxiliary hmem
          terminal).1.edgeId) = (1, 3) ∨
    (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5 outwardYZSwitchLeftPhysical
          outwardYZSwitchPivot outwardYZPivotLeftAuxiliary hmem
          terminal).1.edgeId) = (2, 0) ∨
    (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5 outwardYZSwitchLeftPhysical
          outwardYZSwitchPivot outwardYZPivotLeftAuxiliary hmem
          terminal).1.edgeId) = (3, 1) := by
  have hpairs := outwardYZPivotActualEdgeIdPairs_eq hmem
  have hterminal : terminal ∈
      slabLinkPhysicalStrandTerminals 1 5 outwardYZSwitchLeftPhysical
        outwardYZSwitchPivot outwardYZPivotLeftAuxiliary hmem :=
    SlabLinkPhysicalStrandTerminal.mem_all 1 5
      outwardYZSwitchLeftPhysical outwardYZSwitchPivot
      outwardYZPivotLeftAuxiliary hmem terminal
  have hpair :
      (terminal.1.edgeId,
        (slabLinkPhysicalStrandPartner 1 5 outwardYZSwitchLeftPhysical
          outwardYZSwitchPivot outwardYZPivotLeftAuxiliary hmem
          terminal).1.edgeId) ∈ outwardYZPivotActualEdgeIdPairs hmem := by
    unfold outwardYZPivotActualEdgeIdPairs
    exact List.mem_map.mpr ⟨terminal, hterminal, rfl⟩
  rw [hpairs] at hpair
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using hpair

theorem outwardYZPivot_incidentFaceIds :
    slabIncidentPlaqIds 5 outwardYZSwitchPivot =
      [33, 199, 231, 232, 233] := by
  decide

/-- The position pairing is the literal global face-ID pairing. -/
theorem outwardYZPivotActual_partner_faceId_pair
    (hmem : outwardYZPivotLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5 outwardYZSwitchLeftPhysical
        outwardYZSwitchPivot)
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      outwardYZSwitchLeftPhysical outwardYZSwitchPivot
      outwardYZPivotLeftAuxiliary hmem) :
    let partner := slabLinkPhysicalStrandPartner 1 5
      outwardYZSwitchLeftPhysical outwardYZSwitchPivot
      outwardYZPivotLeftAuxiliary hmem terminal
    let sourceFace := (slabLinkPhysicalTerminalOccurrence 1 5
      outwardYZSwitchLeftPhysical outwardYZSwitchPivot
      outwardYZPivotLeftAuxiliary hmem terminal).faceId
    let targetFace := (slabLinkPhysicalTerminalOccurrence 1 5
      outwardYZSwitchLeftPhysical outwardYZSwitchPivot
      outwardYZPivotLeftAuxiliary hmem partner).faceId
    (sourceFace, targetFace) = (33, 231) ∨
    (sourceFace, targetFace) = (199, 232) ∨
    (sourceFace, targetFace) = (231, 33) ∨
    (sourceFace, targetFace) = (232, 199) := by
  dsimp only
  let partner := slabLinkPhysicalStrandPartner 1 5
    outwardYZSwitchLeftPhysical outwardYZSwitchPivot
    outwardYZPivotLeftAuxiliary hmem terminal
  have hpair := outwardYZPivotActual_partner_position_pair hmem terminal
  rcases hpair with h02 | h13 | h20 | h31
  · left
    have hs : terminal.1.edgeId = 0 := by
      simpa only using congrArg Prod.fst h02
    have ht : partner.1.edgeId = 2 := by
      simpa only [partner] using congrArg Prod.snd h02
    apply Prod.ext
    · change (slabIncidentPlaqIds 5 outwardYZSwitchPivot).get
          ⟨terminal.1.edgeId, terminal.2⟩ = 33
      simp [outwardYZPivot_incidentFaceIds, hs]
    · change (slabIncidentPlaqIds 5 outwardYZSwitchPivot).get
          ⟨partner.1.edgeId, partner.2⟩ = 231
      simp [outwardYZPivot_incidentFaceIds, ht]
  · right; left
    have hs : terminal.1.edgeId = 1 := by
      simpa only using congrArg Prod.fst h13
    have ht : partner.1.edgeId = 3 := by
      simpa only [partner] using congrArg Prod.snd h13
    apply Prod.ext
    · change (slabIncidentPlaqIds 5 outwardYZSwitchPivot).get
          ⟨terminal.1.edgeId, terminal.2⟩ = 199
      simp [outwardYZPivot_incidentFaceIds, hs]
    · change (slabIncidentPlaqIds 5 outwardYZSwitchPivot).get
          ⟨partner.1.edgeId, partner.2⟩ = 232
      simp [outwardYZPivot_incidentFaceIds, ht]
  · right; right; left
    have hs : terminal.1.edgeId = 2 := by
      simpa only using congrArg Prod.fst h20
    have ht : partner.1.edgeId = 0 := by
      simpa only [partner] using congrArg Prod.snd h20
    apply Prod.ext
    · change (slabIncidentPlaqIds 5 outwardYZSwitchPivot).get
          ⟨terminal.1.edgeId, terminal.2⟩ = 231
      simp [outwardYZPivot_incidentFaceIds, hs]
    · change (slabIncidentPlaqIds 5 outwardYZSwitchPivot).get
          ⟨partner.1.edgeId, partner.2⟩ = 33
      simp [outwardYZPivot_incidentFaceIds, ht]
  · right; right; right
    have hs : terminal.1.edgeId = 3 := by
      simpa only using congrArg Prod.fst h31
    have ht : partner.1.edgeId = 1 := by
      simpa only [partner] using congrArg Prod.snd h31
    apply Prod.ext
    · change (slabIncidentPlaqIds 5 outwardYZSwitchPivot).get
          ⟨terminal.1.edgeId, terminal.2⟩ = 232
      simp [outwardYZPivot_incidentFaceIds, hs]
    · change (slabIncidentPlaqIds 5 outwardYZSwitchPivot).get
          ⟨partner.1.edgeId, partner.2⟩ = 199
      simp [outwardYZPivot_incidentFaceIds, ht]

def outwardYZPivotLeftFaceIdPairs
    (hmem : outwardYZPivotLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5 outwardYZSwitchLeftPhysical
        outwardYZSwitchPivot) : List (Nat × Nat) :=
  (slabLinkFaceStrandEdges 1 5 outwardYZSwitchLeftPhysical
      outwardYZSwitchPivot outwardYZPivotLeftAuxiliary
      hmem).map fun edge =>
    (edge.source.faceId, edge.target.faceId)

#print axioms outwardYZSwitchLeftPhysical_bounded
#print axioms outwardYZPivotLeftAuxiliary_mem
#print axioms outwardYZPivotLeftAllowed
#print axioms outwardYZPivotZeroToTwoPath
#print axioms outwardYZPivotOneToThreePath
#print axioms outwardYZPivotPartner_zero_eq_two
#print axioms outwardYZPivotPartner_one_eq_three
#print axioms outwardYZPivotCanonicalEdgeIdPairs_eq
#print axioms outwardYZPivotActualEdgeIdPairs_eq
#print axioms outwardYZPivotActualEdgeIdPairs_ne_native
#print axioms outwardYZPivotActual_partner_position_pair
#print axioms outwardYZPivot_incidentFaceIds
#print axioms outwardYZPivotActual_partner_faceId_pair

end YMGap.Continuum.Z4OutwardYZEdgeTouchSlabPivotPairing
