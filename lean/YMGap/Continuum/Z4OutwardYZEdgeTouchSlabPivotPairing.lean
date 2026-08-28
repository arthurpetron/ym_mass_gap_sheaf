/-
# The outward Y/Z pivot pairs within the two cut components

The selected degree-five production carrier has external word
`[1,1,1,1,0]` and auxiliary word `(2,1)`.  Its three trivalent vertices
therefore route the four physical strands as `0 <-> 2` and `1 <-> 3`.
Together with the literal pivot face order `Z,Y,Z,Y,0`, this is the local
within-component pairing needed by the global two-color argument.

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

/-- Every actual pivot terminal lies in one of the two written within-side
pairs.  Positions zero and two are the Z faces; positions one and three are
the Y faces in `outwardYZPivot_incidentPlaquetteOrder`. -/
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
#print axioms outwardYZPivotActual_partner_position_pair

end YMGap.Continuum.Z4OutwardYZEdgeTouchSlabPivotPairing
