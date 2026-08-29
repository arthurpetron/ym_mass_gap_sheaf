/-
# Canonical local pairings on the two-pivot outward Y/Z repair surface

The repair surface has two four-incidence links.  This module selects one
canonical-left SU(2) carrier at each link and computes its physical-terminal
involution.  The spatial carrier pairs positions `0 <-> 2` and `1 <-> 3`.
The temporal carrier pairs positions `0 <-> 3` and `1 <-> 4`.  Compared with
the exact geometric side words, both pairings stay within a single lobe.

This is the local strand compiler only.  Whole-row target realization,
positive recoupling weight, and global marked-face disconnection are
downstream obligations.

Constructive contract: explicit proof-carrying SU(2) carriers and finite
terminal enumeration only; no choice, `Classical`, `native_decide`, `sorry`,
new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
import YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabConnectedSource

namespace YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabPivotPairing

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Continuum.CanonicalLinkPhysicalTerminalPartner
open YMGap.Continuum.CanonicalLinkEdgeOccurrenceMultiplicity
open YMGap.Continuum.CanonicalLinkStrandStep
open YMGap.Continuum.CanonicalLinkStrandTerminal
open YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource
open YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource.SlabBinarySupportConnectedCarrier
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.SU2CanonicalLeftCarrierWitnessReconstruction
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairCutCarrier
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabConnectedSource
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabSwitchingProfile

def outwardYZCanonicalRepairSwitchLeftPhysical : SlabLabelling :=
  slabBinarySupportLabelling 5
    outwardYZCanonicalRepairSwitchSurface

def outwardYZCanonicalRepairSwitchRightPhysical : SlabLabelling :=
  slabBinarySupportLabelling 5 []

theorem outwardYZCanonicalRepairSwitchLeftPhysical_eq_carrier :
    outwardYZCanonicalRepairSwitchLeftPhysical =
      outwardYZCanonicalRepairBinaryConnectedCarrier.leftPhysical := by
  rfl

theorem outwardYZCanonicalRepairSwitchRightPhysical_eq_carrier :
    outwardYZCanonicalRepairSwitchRightPhysical =
      outwardYZCanonicalRepairBinaryConnectedCarrier.rightPhysical := by
  rfl

theorem outwardYZCanonicalRepairSwitchLeftPhysical_bounded :
    SlabFaceLabellingBounded 1 5
      outwardYZCanonicalRepairSwitchLeftPhysical := by
  intro faceId _
  exact slabBinarySupportLabelling_le_one 5
    outwardYZCanonicalRepairSwitchSurface faceId

def outwardYZCanonicalRepairSpatialPivotRecouplingData :
    SlabPhysicalPairRecouplingData 5 5 where
  leftPhysical := outwardYZCanonicalRepairSwitchLeftPhysical
  rightPhysical := outwardYZCanonicalRepairSwitchRightPhysical
  link := outwardYZCanonicalRepairSwitchSpatialPivot
  degree_eq := outwardYZCanonicalRepairSwitchSpatialPivot_degree_five

def outwardYZCanonicalRepairTemporalPivotRecouplingData :
    SlabPhysicalPairRecouplingData 5 5 where
  leftPhysical := outwardYZCanonicalRepairSwitchLeftPhysical
  rightPhysical := outwardYZCanonicalRepairSwitchRightPhysical
  link := outwardYZCanonicalRepairSwitchTemporalPivot
  degree_eq := outwardYZCanonicalRepairSwitchTemporalPivot_degree_five

private theorem outwardYZCanonicalRepairSpatialLeftExternalSpins_eq :
    slabLinkExternalSpins 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchSpatialPivot =
      externalSpinsOfList [1, 1, 1, 1, 0] := by
  unfold slabLinkExternalSpins
    outwardYZCanonicalRepairSwitchLeftPhysical
  change externalSpinsOfList
      ((slabIncidentPlaqIds 5
        outwardYZCanonicalRepairSwitchSpatialPivot).map
          (slabBinarySupportLabelling 5
            outwardYZCanonicalRepairSwitchSurface)) =
    externalSpinsOfList [1, 1, 1, 1, 0]
  rw [outwardYZCanonicalRepairSwitchSpatialPivot_spinList]

private theorem outwardYZCanonicalRepairTemporalLeftExternalSpins_eq :
    slabLinkExternalSpins 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchTemporalPivot =
      externalSpinsOfList [1, 1, 0, 1, 1] := by
  unfold slabLinkExternalSpins
    outwardYZCanonicalRepairSwitchLeftPhysical
  change externalSpinsOfList
      ((slabIncidentPlaqIds 5
        outwardYZCanonicalRepairSwitchTemporalPivot).map
          (slabBinarySupportLabelling 5
            outwardYZCanonicalRepairSwitchSurface)) =
    externalSpinsOfList [1, 1, 0, 1, 1]
  rw [outwardYZCanonicalRepairSwitchTemporalPivot_spinList]

def outwardYZCanonicalRepairPivot_degree_le : 5 ≤
    YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff.linkIncidenceBound := by
  decide

/-! ## 1. Spatial carrier -/

def outwardYZCanonicalRepairSpatialLeftSource :
    ValenceFiveLeftCarrier 1 1 1 1 0 where
  y := 1
  firstLeft :=
    { k := 0
      k_le := by decide
      r := 1
      r_le := by decide
      degree_eq := by decide }
  suffix :=
    { order := 1
      order_le := by decide
      output_eq := by decide }

def outwardYZCanonicalRepairSpatialLeftAuxiliary : SlabLabelling :=
  valenceFiveLeftAuxiliary outwardYZCanonicalRepairSpatialLeftSource

theorem outwardYZCanonicalRepairSpatialLeftAuxiliary_mem :
    outwardYZCanonicalRepairSpatialLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchSpatialPivot :=
  valenceFiveLeftAuxiliary_mem_slabLinkFusionWitnesses
    outwardYZCanonicalRepairSwitchLeftPhysical_bounded
    outwardYZCanonicalRepairSwitchSpatialPivot_degree_five
    outwardYZCanonicalRepairSpatialLeftSource

def outwardYZCanonicalRepairSpatialLeftAllowed :
    YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
      5
      (slabLinkExternalSpins 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchSpatialPivot)
      outwardYZCanonicalRepairSpatialLeftAuxiliary = true := by
  decide

def outwardYZCanonicalRepairSpatialCanonicalPhysicalTerminals :
    List (CanonicalPhysicalStrandPort
      (slabLinkExternalSpins 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchSpatialPivot)
      outwardYZCanonicalRepairSpatialLeftAuxiliary
      outwardYZCanonicalRepairSpatialLeftAllowed) :=
  (allResolvedNetworkPorts
    (canonicalLinkResolvedStrandNetwork 5
      (slabLinkExternalSpins 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchSpatialPivot)
      outwardYZCanonicalRepairSpatialLeftAuxiliary
      outwardYZCanonicalRepairSpatialLeftAllowed)).filterMap
        fun occurrence =>
          if hphysical : occurrence.edgeId < 5 then
            some ⟨occurrence, hphysical⟩
          else none

def outwardYZCanonicalRepairSpatialCanonicalEdgeIdPairs :
    List (Nat × Nat) :=
  outwardYZCanonicalRepairSpatialCanonicalPhysicalTerminals.map
    fun terminal =>
      (terminal.1.edgeId,
        (canonicalPhysicalStrandPartner
          outwardYZCanonicalRepairPivot_degree_le
          outwardYZCanonicalRepairSpatialLeftAllowed terminal).1.edgeId)

abbrev OutwardYZCanonicalRepairSpatialResolvedPort := ResolvedNetworkPort
  (canonicalLinkResolvedStrandNetwork 5
    (slabLinkExternalSpins 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchSpatialPivot)
    outwardYZCanonicalRepairSpatialLeftAuxiliary
    outwardYZCanonicalRepairSpatialLeftAllowed)

def outwardYZCanonicalRepairSpatialPortZero :
    OutwardYZCanonicalRepairSpatialResolvedPort where
  vertexIndex := ⟨0, by decide⟩
  port := .onA ⟨0, by decide⟩

def outwardYZCanonicalRepairSpatialPortOne :
    OutwardYZCanonicalRepairSpatialResolvedPort where
  vertexIndex := ⟨0, by decide⟩
  port := .onB ⟨0, by decide⟩

def outwardYZCanonicalRepairSpatialPortTwo :
    OutwardYZCanonicalRepairSpatialResolvedPort where
  vertexIndex := ⟨1, by decide⟩
  port := .onB ⟨0, by decide⟩

def outwardYZCanonicalRepairSpatialPortThree :
    OutwardYZCanonicalRepairSpatialResolvedPort where
  vertexIndex := ⟨2, by decide⟩
  port := .onB ⟨0, by decide⟩

def outwardYZCanonicalRepairSpatialPortSeven :
    OutwardYZCanonicalRepairSpatialResolvedPort where
  vertexIndex := ⟨1, by decide⟩
  port := .onC ⟨0, by decide⟩

def outwardYZCanonicalRepairSpatialTerminalZero :
    CanonicalPhysicalStrandPort
      (slabLinkExternalSpins 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchSpatialPivot)
      outwardYZCanonicalRepairSpatialLeftAuxiliary
      outwardYZCanonicalRepairSpatialLeftAllowed :=
  ⟨outwardYZCanonicalRepairSpatialPortZero, by decide⟩

def outwardYZCanonicalRepairSpatialTerminalOne :
    CanonicalPhysicalStrandPort
      (slabLinkExternalSpins 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchSpatialPivot)
      outwardYZCanonicalRepairSpatialLeftAuxiliary
      outwardYZCanonicalRepairSpatialLeftAllowed :=
  ⟨outwardYZCanonicalRepairSpatialPortOne, by decide⟩

def outwardYZCanonicalRepairSpatialTerminalTwo :
    CanonicalPhysicalStrandPort
      (slabLinkExternalSpins 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchSpatialPivot)
      outwardYZCanonicalRepairSpatialLeftAuxiliary
      outwardYZCanonicalRepairSpatialLeftAllowed :=
  ⟨outwardYZCanonicalRepairSpatialPortTwo, by decide⟩

def outwardYZCanonicalRepairSpatialTerminalThree :
    CanonicalPhysicalStrandPort
      (slabLinkExternalSpins 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchSpatialPivot)
      outwardYZCanonicalRepairSpatialLeftAuxiliary
      outwardYZCanonicalRepairSpatialLeftAllowed :=
  ⟨outwardYZCanonicalRepairSpatialPortThree, by decide⟩

def outwardYZCanonicalRepairSpatialZeroMate_internal :
    outwardYZCanonicalRepairSpatialTerminalZero.1.localMate.edgeId ∈
      canonicalInternalFusionEdges 5 := by
  decide

theorem outwardYZCanonicalRepairSpatialZeroMate_advance_eq :
    canonicalInternalAdvancePort outwardYZCanonicalRepairPivot_degree_le
      outwardYZCanonicalRepairSpatialLeftAllowed
      outwardYZCanonicalRepairSpatialTerminalZero.1.localMate
      outwardYZCanonicalRepairSpatialZeroMate_internal =
        outwardYZCanonicalRepairSpatialTerminalTwo.1 := by
  apply ResolvedNetworkPort.address_injective
  decide

def outwardYZCanonicalRepairSpatialZeroToTwoPath :
    CanonicalStrandPathToPhysical
      outwardYZCanonicalRepairPivot_degree_le
      outwardYZCanonicalRepairSpatialLeftAllowed
      outwardYZCanonicalRepairSpatialTerminalZero.1.localMate
      outwardYZCanonicalRepairSpatialTerminalTwo := by
  refine .advance outwardYZCanonicalRepairSpatialTerminalZero.1.localMate
    outwardYZCanonicalRepairSpatialZeroMate_internal
    outwardYZCanonicalRepairSpatialTerminalTwo ?_
  rw [outwardYZCanonicalRepairSpatialZeroMate_advance_eq]
  exact .stop outwardYZCanonicalRepairSpatialTerminalTwo

def outwardYZCanonicalRepairSpatialOneMate_internal :
    outwardYZCanonicalRepairSpatialTerminalOne.1.localMate.edgeId ∈
      canonicalInternalFusionEdges 5 := by
  decide

theorem outwardYZCanonicalRepairSpatialOneMate_advance_eq :
    canonicalInternalAdvancePort outwardYZCanonicalRepairPivot_degree_le
      outwardYZCanonicalRepairSpatialLeftAllowed
      outwardYZCanonicalRepairSpatialTerminalOne.1.localMate
      outwardYZCanonicalRepairSpatialOneMate_internal =
        outwardYZCanonicalRepairSpatialPortSeven := by
  apply ResolvedNetworkPort.address_injective
  decide

def outwardYZCanonicalRepairSpatialPortSeven_internal :
    outwardYZCanonicalRepairSpatialPortSeven.edgeId ∈
      canonicalInternalFusionEdges 5 := by
  decide

theorem outwardYZCanonicalRepairSpatialPortSeven_advance_eq :
    canonicalInternalAdvancePort outwardYZCanonicalRepairPivot_degree_le
      outwardYZCanonicalRepairSpatialLeftAllowed
      outwardYZCanonicalRepairSpatialPortSeven
      outwardYZCanonicalRepairSpatialPortSeven_internal =
        outwardYZCanonicalRepairSpatialTerminalThree.1 := by
  apply ResolvedNetworkPort.address_injective
  decide

def outwardYZCanonicalRepairSpatialOneToThreePath :
    CanonicalStrandPathToPhysical
      outwardYZCanonicalRepairPivot_degree_le
      outwardYZCanonicalRepairSpatialLeftAllowed
      outwardYZCanonicalRepairSpatialTerminalOne.1.localMate
      outwardYZCanonicalRepairSpatialTerminalThree := by
  refine .advance outwardYZCanonicalRepairSpatialTerminalOne.1.localMate
    outwardYZCanonicalRepairSpatialOneMate_internal
    outwardYZCanonicalRepairSpatialTerminalThree ?_
  rw [outwardYZCanonicalRepairSpatialOneMate_advance_eq]
  refine .advance outwardYZCanonicalRepairSpatialPortSeven
    outwardYZCanonicalRepairSpatialPortSeven_internal
    outwardYZCanonicalRepairSpatialTerminalThree ?_
  rw [outwardYZCanonicalRepairSpatialPortSeven_advance_eq]
  exact .stop outwardYZCanonicalRepairSpatialTerminalThree

theorem outwardYZCanonicalRepairSpatialPartner_zero_eq_two :
    canonicalPhysicalStrandPartner
      outwardYZCanonicalRepairPivot_degree_le
      outwardYZCanonicalRepairSpatialLeftAllowed
      outwardYZCanonicalRepairSpatialTerminalZero =
        outwardYZCanonicalRepairSpatialTerminalTwo :=
  canonicalStrandPath_terminal_unique
    (canonicalPhysicalStrandPartner_path
      outwardYZCanonicalRepairPivot_degree_le
      outwardYZCanonicalRepairSpatialLeftAllowed
      outwardYZCanonicalRepairSpatialTerminalZero)
    outwardYZCanonicalRepairSpatialZeroToTwoPath

theorem outwardYZCanonicalRepairSpatialPartner_one_eq_three :
    canonicalPhysicalStrandPartner
      outwardYZCanonicalRepairPivot_degree_le
      outwardYZCanonicalRepairSpatialLeftAllowed
      outwardYZCanonicalRepairSpatialTerminalOne =
        outwardYZCanonicalRepairSpatialTerminalThree :=
  canonicalStrandPath_terminal_unique
    (canonicalPhysicalStrandPartner_path
      outwardYZCanonicalRepairPivot_degree_le
      outwardYZCanonicalRepairSpatialLeftAllowed
      outwardYZCanonicalRepairSpatialTerminalOne)
    outwardYZCanonicalRepairSpatialOneToThreePath

theorem outwardYZCanonicalRepairSpatialPartner_two_eq_zero :
    canonicalPhysicalStrandPartner
      outwardYZCanonicalRepairPivot_degree_le
      outwardYZCanonicalRepairSpatialLeftAllowed
      outwardYZCanonicalRepairSpatialTerminalTwo =
        outwardYZCanonicalRepairSpatialTerminalZero := by
  rw [← outwardYZCanonicalRepairSpatialPartner_zero_eq_two]
  exact canonicalPhysicalStrandPartner_involutive
    outwardYZCanonicalRepairPivot_degree_le
    outwardYZCanonicalRepairSpatialLeftAllowed
    outwardYZCanonicalRepairSpatialTerminalZero

theorem outwardYZCanonicalRepairSpatialPartner_three_eq_one :
    canonicalPhysicalStrandPartner
      outwardYZCanonicalRepairPivot_degree_le
      outwardYZCanonicalRepairSpatialLeftAllowed
      outwardYZCanonicalRepairSpatialTerminalThree =
        outwardYZCanonicalRepairSpatialTerminalOne := by
  rw [← outwardYZCanonicalRepairSpatialPartner_one_eq_three]
  exact canonicalPhysicalStrandPartner_involutive
    outwardYZCanonicalRepairPivot_degree_le
    outwardYZCanonicalRepairSpatialLeftAllowed
    outwardYZCanonicalRepairSpatialTerminalOne

theorem outwardYZCanonicalRepairSpatialCanonicalPhysicalTerminals_exact :
    outwardYZCanonicalRepairSpatialCanonicalPhysicalTerminals =
      [outwardYZCanonicalRepairSpatialTerminalZero,
       outwardYZCanonicalRepairSpatialTerminalOne,
       outwardYZCanonicalRepairSpatialTerminalTwo,
       outwardYZCanonicalRepairSpatialTerminalThree] := by
  decide

theorem outwardYZCanonicalRepairSpatialCanonicalEdgeIdPairs_exact :
    outwardYZCanonicalRepairSpatialCanonicalEdgeIdPairs =
      [(0, 2), (1, 3), (2, 0), (3, 1)] := by
  unfold outwardYZCanonicalRepairSpatialCanonicalEdgeIdPairs
  rw [outwardYZCanonicalRepairSpatialCanonicalPhysicalTerminals_exact]
  simp only [List.map_cons, List.map_nil]
  rw [outwardYZCanonicalRepairSpatialPartner_zero_eq_two,
    outwardYZCanonicalRepairSpatialPartner_one_eq_three,
    outwardYZCanonicalRepairSpatialPartner_two_eq_zero,
    outwardYZCanonicalRepairSpatialPartner_three_eq_one]
  decide

/-! ## 2. Temporal carrier -/

/-- Fuse the first two fundamentals without contraction, pass through the
vacuum third slot, and contract once against the fourth fundamental. -/
def outwardYZCanonicalRepairTemporalLeftSource :
    ValenceFiveLeftCarrier 1 1 0 1 1 where
  y := 2
  firstLeft :=
    { k := 0
      k_le := by decide
      r := 0
      r_le := by decide
      degree_eq := by decide }
  suffix :=
    { order := 1
      order_le := by decide
      output_eq := by decide }

def outwardYZCanonicalRepairTemporalLeftAuxiliary : SlabLabelling :=
  valenceFiveLeftAuxiliary outwardYZCanonicalRepairTemporalLeftSource

theorem outwardYZCanonicalRepairTemporalLeftAuxiliary_mem :
    outwardYZCanonicalRepairTemporalLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchTemporalPivot :=
  valenceFiveLeftAuxiliary_mem_slabLinkFusionWitnesses
    outwardYZCanonicalRepairSwitchLeftPhysical_bounded
    outwardYZCanonicalRepairSwitchTemporalPivot_degree_five
    outwardYZCanonicalRepairTemporalLeftSource

def outwardYZCanonicalRepairTemporalLeftAllowed :
    YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
      5
      (slabLinkExternalSpins 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchTemporalPivot)
      outwardYZCanonicalRepairTemporalLeftAuxiliary = true := by
  decide

def outwardYZCanonicalRepairTemporalCanonicalPhysicalTerminals :
    List (CanonicalPhysicalStrandPort
      (slabLinkExternalSpins 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchTemporalPivot)
      outwardYZCanonicalRepairTemporalLeftAuxiliary
      outwardYZCanonicalRepairTemporalLeftAllowed) :=
  (allResolvedNetworkPorts
    (canonicalLinkResolvedStrandNetwork 5
      (slabLinkExternalSpins 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchTemporalPivot)
      outwardYZCanonicalRepairTemporalLeftAuxiliary
      outwardYZCanonicalRepairTemporalLeftAllowed)).filterMap
        fun occurrence =>
          if hphysical : occurrence.edgeId < 5 then
            some ⟨occurrence, hphysical⟩
          else none

def outwardYZCanonicalRepairTemporalCanonicalEdgeIdPairs :
    List (Nat × Nat) :=
  outwardYZCanonicalRepairTemporalCanonicalPhysicalTerminals.map
    fun terminal =>
      (terminal.1.edgeId,
        (canonicalPhysicalStrandPartner
          outwardYZCanonicalRepairPivot_degree_le
          outwardYZCanonicalRepairTemporalLeftAllowed terminal).1.edgeId)

abbrev OutwardYZCanonicalRepairTemporalResolvedPort := ResolvedNetworkPort
  (canonicalLinkResolvedStrandNetwork 5
    (slabLinkExternalSpins 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchTemporalPivot)
    outwardYZCanonicalRepairTemporalLeftAuxiliary
    outwardYZCanonicalRepairTemporalLeftAllowed)

def outwardYZCanonicalRepairTemporalPortZero :
    OutwardYZCanonicalRepairTemporalResolvedPort where
  vertexIndex := ⟨0, by decide⟩
  port := .onA ⟨0, by decide⟩

def outwardYZCanonicalRepairTemporalPortOne :
    OutwardYZCanonicalRepairTemporalResolvedPort where
  vertexIndex := ⟨0, by decide⟩
  port := .onB ⟨0, by decide⟩

def outwardYZCanonicalRepairTemporalPortThree :
    OutwardYZCanonicalRepairTemporalResolvedPort where
  vertexIndex := ⟨2, by decide⟩
  port := .onB ⟨0, by decide⟩

def outwardYZCanonicalRepairTemporalPortFour :
    OutwardYZCanonicalRepairTemporalResolvedPort where
  vertexIndex := ⟨2, by decide⟩
  port := .onC ⟨0, by decide⟩

def outwardYZCanonicalRepairTemporalTerminalZero :
    CanonicalPhysicalStrandPort
      (slabLinkExternalSpins 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchTemporalPivot)
      outwardYZCanonicalRepairTemporalLeftAuxiliary
      outwardYZCanonicalRepairTemporalLeftAllowed :=
  ⟨outwardYZCanonicalRepairTemporalPortZero, by decide⟩

def outwardYZCanonicalRepairTemporalTerminalOne :
    CanonicalPhysicalStrandPort
      (slabLinkExternalSpins 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchTemporalPivot)
      outwardYZCanonicalRepairTemporalLeftAuxiliary
      outwardYZCanonicalRepairTemporalLeftAllowed :=
  ⟨outwardYZCanonicalRepairTemporalPortOne, by decide⟩

def outwardYZCanonicalRepairTemporalTerminalThree :
    CanonicalPhysicalStrandPort
      (slabLinkExternalSpins 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchTemporalPivot)
      outwardYZCanonicalRepairTemporalLeftAuxiliary
      outwardYZCanonicalRepairTemporalLeftAllowed :=
  ⟨outwardYZCanonicalRepairTemporalPortThree, by decide⟩

def outwardYZCanonicalRepairTemporalTerminalFour :
    CanonicalPhysicalStrandPort
      (slabLinkExternalSpins 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchTemporalPivot)
      outwardYZCanonicalRepairTemporalLeftAuxiliary
      outwardYZCanonicalRepairTemporalLeftAllowed :=
  ⟨outwardYZCanonicalRepairTemporalPortFour, by decide⟩

def outwardYZCanonicalRepairTemporalZeroMate_internal :
    outwardYZCanonicalRepairTemporalTerminalZero.1.localMate.edgeId ∈
      canonicalInternalFusionEdges 5 := by
  decide

def outwardYZCanonicalRepairTemporalOneMate_internal :
    outwardYZCanonicalRepairTemporalTerminalOne.1.localMate.edgeId ∈
      canonicalInternalFusionEdges 5 := by
  decide

def outwardYZCanonicalRepairTemporalPortSevenSlotOne :
    OutwardYZCanonicalRepairTemporalResolvedPort where
  vertexIndex := ⟨1, by decide⟩
  port := .onC ⟨1, by decide⟩

def outwardYZCanonicalRepairTemporalPortSevenSlotZero :
    OutwardYZCanonicalRepairTemporalResolvedPort where
  vertexIndex := ⟨1, by decide⟩
  port := .onC ⟨0, by decide⟩

theorem outwardYZCanonicalRepairTemporalZeroMate_advance_eq :
    canonicalInternalAdvancePort outwardYZCanonicalRepairPivot_degree_le
      outwardYZCanonicalRepairTemporalLeftAllowed
      outwardYZCanonicalRepairTemporalTerminalZero.1.localMate
      outwardYZCanonicalRepairTemporalZeroMate_internal =
        outwardYZCanonicalRepairTemporalPortSevenSlotOne := by
  apply ResolvedNetworkPort.address_injective
  decide

theorem outwardYZCanonicalRepairTemporalOneMate_advance_eq :
    canonicalInternalAdvancePort outwardYZCanonicalRepairPivot_degree_le
      outwardYZCanonicalRepairTemporalLeftAllowed
      outwardYZCanonicalRepairTemporalTerminalOne.1.localMate
      outwardYZCanonicalRepairTemporalOneMate_internal =
        outwardYZCanonicalRepairTemporalPortSevenSlotZero := by
  apply ResolvedNetworkPort.address_injective
  decide

def outwardYZCanonicalRepairTemporalPortSevenSlotOne_internal :
    outwardYZCanonicalRepairTemporalPortSevenSlotOne.edgeId ∈
      canonicalInternalFusionEdges 5 := by
  decide

def outwardYZCanonicalRepairTemporalPortSevenSlotZero_internal :
    outwardYZCanonicalRepairTemporalPortSevenSlotZero.edgeId ∈
      canonicalInternalFusionEdges 5 := by
  decide

theorem outwardYZCanonicalRepairTemporalPortSevenSlotOne_advance_eq :
    canonicalInternalAdvancePort outwardYZCanonicalRepairPivot_degree_le
      outwardYZCanonicalRepairTemporalLeftAllowed
      outwardYZCanonicalRepairTemporalPortSevenSlotOne
      outwardYZCanonicalRepairTemporalPortSevenSlotOne_internal =
        outwardYZCanonicalRepairTemporalTerminalThree.1 := by
  apply ResolvedNetworkPort.address_injective
  decide

theorem outwardYZCanonicalRepairTemporalPortSevenSlotZero_advance_eq :
    canonicalInternalAdvancePort outwardYZCanonicalRepairPivot_degree_le
      outwardYZCanonicalRepairTemporalLeftAllowed
      outwardYZCanonicalRepairTemporalPortSevenSlotZero
      outwardYZCanonicalRepairTemporalPortSevenSlotZero_internal =
        outwardYZCanonicalRepairTemporalTerminalFour.1 := by
  apply ResolvedNetworkPort.address_injective
  decide

def outwardYZCanonicalRepairTemporalZeroToThreePath :
    CanonicalStrandPathToPhysical
      outwardYZCanonicalRepairPivot_degree_le
      outwardYZCanonicalRepairTemporalLeftAllowed
      outwardYZCanonicalRepairTemporalTerminalZero.1.localMate
      outwardYZCanonicalRepairTemporalTerminalThree := by
  refine .advance outwardYZCanonicalRepairTemporalTerminalZero.1.localMate
    outwardYZCanonicalRepairTemporalZeroMate_internal
    outwardYZCanonicalRepairTemporalTerminalThree ?_
  rw [outwardYZCanonicalRepairTemporalZeroMate_advance_eq]
  refine .advance outwardYZCanonicalRepairTemporalPortSevenSlotOne
    outwardYZCanonicalRepairTemporalPortSevenSlotOne_internal
    outwardYZCanonicalRepairTemporalTerminalThree ?_
  rw [outwardYZCanonicalRepairTemporalPortSevenSlotOne_advance_eq]
  exact .stop outwardYZCanonicalRepairTemporalTerminalThree

def outwardYZCanonicalRepairTemporalOneToFourPath :
    CanonicalStrandPathToPhysical
      outwardYZCanonicalRepairPivot_degree_le
      outwardYZCanonicalRepairTemporalLeftAllowed
      outwardYZCanonicalRepairTemporalTerminalOne.1.localMate
      outwardYZCanonicalRepairTemporalTerminalFour := by
  refine .advance outwardYZCanonicalRepairTemporalTerminalOne.1.localMate
    outwardYZCanonicalRepairTemporalOneMate_internal
    outwardYZCanonicalRepairTemporalTerminalFour ?_
  rw [outwardYZCanonicalRepairTemporalOneMate_advance_eq]
  refine .advance outwardYZCanonicalRepairTemporalPortSevenSlotZero
    outwardYZCanonicalRepairTemporalPortSevenSlotZero_internal
    outwardYZCanonicalRepairTemporalTerminalFour ?_
  rw [outwardYZCanonicalRepairTemporalPortSevenSlotZero_advance_eq]
  exact .stop outwardYZCanonicalRepairTemporalTerminalFour

theorem outwardYZCanonicalRepairTemporalPartner_zero_eq_three :
    canonicalPhysicalStrandPartner
      outwardYZCanonicalRepairPivot_degree_le
      outwardYZCanonicalRepairTemporalLeftAllowed
      outwardYZCanonicalRepairTemporalTerminalZero =
        outwardYZCanonicalRepairTemporalTerminalThree :=
  canonicalStrandPath_terminal_unique
    (canonicalPhysicalStrandPartner_path
      outwardYZCanonicalRepairPivot_degree_le
      outwardYZCanonicalRepairTemporalLeftAllowed
      outwardYZCanonicalRepairTemporalTerminalZero)
    outwardYZCanonicalRepairTemporalZeroToThreePath

theorem outwardYZCanonicalRepairTemporalPartner_one_eq_four :
    canonicalPhysicalStrandPartner
      outwardYZCanonicalRepairPivot_degree_le
      outwardYZCanonicalRepairTemporalLeftAllowed
      outwardYZCanonicalRepairTemporalTerminalOne =
        outwardYZCanonicalRepairTemporalTerminalFour :=
  canonicalStrandPath_terminal_unique
    (canonicalPhysicalStrandPartner_path
      outwardYZCanonicalRepairPivot_degree_le
      outwardYZCanonicalRepairTemporalLeftAllowed
      outwardYZCanonicalRepairTemporalTerminalOne)
    outwardYZCanonicalRepairTemporalOneToFourPath

theorem outwardYZCanonicalRepairTemporalPartner_three_eq_zero :
    canonicalPhysicalStrandPartner
      outwardYZCanonicalRepairPivot_degree_le
      outwardYZCanonicalRepairTemporalLeftAllowed
      outwardYZCanonicalRepairTemporalTerminalThree =
        outwardYZCanonicalRepairTemporalTerminalZero := by
  rw [← outwardYZCanonicalRepairTemporalPartner_zero_eq_three]
  exact canonicalPhysicalStrandPartner_involutive
    outwardYZCanonicalRepairPivot_degree_le
    outwardYZCanonicalRepairTemporalLeftAllowed
    outwardYZCanonicalRepairTemporalTerminalZero

theorem outwardYZCanonicalRepairTemporalPartner_four_eq_one :
    canonicalPhysicalStrandPartner
      outwardYZCanonicalRepairPivot_degree_le
      outwardYZCanonicalRepairTemporalLeftAllowed
      outwardYZCanonicalRepairTemporalTerminalFour =
        outwardYZCanonicalRepairTemporalTerminalOne := by
  rw [← outwardYZCanonicalRepairTemporalPartner_one_eq_four]
  exact canonicalPhysicalStrandPartner_involutive
    outwardYZCanonicalRepairPivot_degree_le
    outwardYZCanonicalRepairTemporalLeftAllowed
    outwardYZCanonicalRepairTemporalTerminalOne

theorem outwardYZCanonicalRepairTemporalCanonicalPhysicalTerminals_exact :
    outwardYZCanonicalRepairTemporalCanonicalPhysicalTerminals =
      [outwardYZCanonicalRepairTemporalTerminalZero,
       outwardYZCanonicalRepairTemporalTerminalOne,
       outwardYZCanonicalRepairTemporalTerminalThree,
       outwardYZCanonicalRepairTemporalTerminalFour] := by
  decide

theorem outwardYZCanonicalRepairTemporalCanonicalEdgeIdPairs_exact :
    outwardYZCanonicalRepairTemporalCanonicalEdgeIdPairs =
      [(0, 3), (1, 4), (3, 0), (4, 1)] := by
  unfold outwardYZCanonicalRepairTemporalCanonicalEdgeIdPairs
  rw [outwardYZCanonicalRepairTemporalCanonicalPhysicalTerminals_exact]
  simp only [List.map_cons, List.map_nil]
  rw [outwardYZCanonicalRepairTemporalPartner_zero_eq_three,
    outwardYZCanonicalRepairTemporalPartner_one_eq_four,
    outwardYZCanonicalRepairTemporalPartner_three_eq_zero,
    outwardYZCanonicalRepairTemporalPartner_four_eq_one]
  decide

/-! ## 3. Exact agreement with the two geometric lobes -/

def outwardYZCanonicalRepairSpatialPositionSide (position : Nat) : Nat :=
  [1, 2, 1, 2, 0].getD position 0

def outwardYZCanonicalRepairTemporalPositionSide (position : Nat) : Nat :=
  [1, 2, 0, 1, 2].getD position 0

theorem outwardYZCanonicalRepairSpatialPair_same_side
    (pair : Nat × Nat)
    (hpair : pair ∈
      outwardYZCanonicalRepairSpatialCanonicalEdgeIdPairs) :
    outwardYZCanonicalRepairSpatialPositionSide pair.1 =
      outwardYZCanonicalRepairSpatialPositionSide pair.2 := by
  rw [outwardYZCanonicalRepairSpatialCanonicalEdgeIdPairs_exact] at hpair
  rcases List.mem_cons.mp hpair with rfl | hpair
  · decide
  rcases List.mem_cons.mp hpair with rfl | hpair
  · decide
  rcases List.mem_cons.mp hpair with rfl | hpair
  · decide
  rcases List.mem_cons.mp hpair with rfl | hpair
  · decide
  exact False.elim (List.not_mem_nil hpair)

theorem outwardYZCanonicalRepairTemporalPair_same_side
    (pair : Nat × Nat)
    (hpair : pair ∈
      outwardYZCanonicalRepairTemporalCanonicalEdgeIdPairs) :
    outwardYZCanonicalRepairTemporalPositionSide pair.1 =
      outwardYZCanonicalRepairTemporalPositionSide pair.2 := by
  rw [outwardYZCanonicalRepairTemporalCanonicalEdgeIdPairs_exact] at hpair
  rcases List.mem_cons.mp hpair with rfl | hpair
  · decide
  rcases List.mem_cons.mp hpair with rfl | hpair
  · decide
  rcases List.mem_cons.mp hpair with rfl | hpair
  · decide
  rcases List.mem_cons.mp hpair with rfl | hpair
  · decide
  exact False.elim (List.not_mem_nil hpair)

#print axioms outwardYZCanonicalRepairSpatialLeftAuxiliary_mem
#print axioms outwardYZCanonicalRepairSpatialCanonicalEdgeIdPairs_exact
#print axioms outwardYZCanonicalRepairTemporalLeftAuxiliary_mem
#print axioms outwardYZCanonicalRepairTemporalCanonicalEdgeIdPairs_exact
#print axioms outwardYZCanonicalRepairSpatialPair_same_side
#print axioms outwardYZCanonicalRepairTemporalPair_same_side

end YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabPivotPairing
