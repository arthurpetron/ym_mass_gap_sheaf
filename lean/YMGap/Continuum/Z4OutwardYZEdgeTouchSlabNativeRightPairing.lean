/-
# The native right-tree pairing of the outward Y/Z pivot target

The selected pivot target has right-associated channel data `m = 0`.
Consequently its inner vertex pairs physical positions one and two, while
the remaining singlet pairs positions zero and three.  The fixed production
resolver is left-associated, so this file compiles the right tree through
the explicit leaf reindexing `[1,2,0,3,4]` and the left carrier `(0,1)`.

The resulting canonical terminal pairing is `0 <-> 1`, `2 <-> 3`; after
reindexing it is exactly the native target pairing `1 <-> 2`, `0 <-> 3`.
This is deliberately distinct from equal-rank realization, whose `(2,1)`
carrier was proved to pair across the geometric cut.

Constructive contract: explicit finite tree paths and a finite leaf
permutation only; no choice, `Classical`, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4OutwardYZEdgeTouchSlabPivotPairing

namespace YMGap.Continuum.Z4OutwardYZEdgeTouchSlabNativeRightPairing

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Continuum.CanonicalLinkPhysicalTerminalPartner
open YMGap.Continuum.CanonicalLinkEdgeOccurrenceMultiplicity
open YMGap.Continuum.CanonicalLinkStrandStep
open YMGap.Continuum.CanonicalLinkStrandTerminal
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.SU2CanonicalLeftCarrierWitnessReconstruction
open YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition
open YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabPivotPairing
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabWholeProductPositivity

/-! ## 1. Compile the selected right tree as a reindexed left tree -/

def outwardYZPivotNativeRightAsLeftSource :
    ValenceFiveLeftCarrier 1 1 1 1 0 where
  y := 1
  firstLeft :=
    { k := 1
      k_le := by decide
      r := 0
      r_le := by decide
      degree_eq := by decide }
  suffix :=
    { order := 1
      order_le := by decide
      output_eq := by decide }

def outwardYZPivotNativeRightAsLeftAuxiliary : SlabLabelling :=
  valenceFiveLeftAuxiliary outwardYZPivotNativeRightAsLeftSource

theorem outwardYZPivotNativeRightAsLeftAuxiliary_firstIntermediate :
    outwardYZPivotNativeRightAsLeftAuxiliary 6 = 0 := by
  rfl

theorem outwardYZPivotNativeRightAsLeftAuxiliary_secondIntermediate :
    outwardYZPivotNativeRightAsLeftAuxiliary 7 = 1 := by
  rfl

theorem outwardYZPivotNativeRightAsLeftAuxiliary_mem :
    outwardYZPivotNativeRightAsLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5 outwardYZSwitchLeftPhysical
        outwardYZSwitchPivot :=
  valenceFiveLeftAuxiliary_mem_slabLinkFusionWitnesses
    outwardYZSwitchLeftPhysical_bounded
    outwardYZSwitchPivot_degree_five
    outwardYZPivotNativeRightAsLeftSource

/-- Canonical left positions are sent to native right-tree physical
positions by `[0,1,2,3,4] |-> [1,2,0,3,4]`. -/
def outwardYZPivotNativeRightPosition : Fin 5 -> Fin 5
  | ⟨0, _⟩ => ⟨1, by decide⟩
  | ⟨1, _⟩ => ⟨2, by decide⟩
  | ⟨2, _⟩ => ⟨0, by decide⟩
  | ⟨3, _⟩ => ⟨3, by decide⟩
  | ⟨4, _⟩ => ⟨4, by decide⟩
  | ⟨n + 5, h⟩ => False.elim (by omega)

def outwardYZPivotNativeRightPositionPair
    (pair : Nat × Nat) : Nat × Nat :=
  if hs : pair.1 < 5 then
    if ht : pair.2 < 5 then
      ((outwardYZPivotNativeRightPosition ⟨pair.1, hs⟩).val,
       (outwardYZPivotNativeRightPosition ⟨pair.2, ht⟩).val)
    else pair
  else pair

/-! ## 2. The literal reindexed-left terminal pairing -/

def outwardYZPivotNativeRightAllowed :
    YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
      5
      (slabLinkExternalSpins 5 outwardYZSwitchLeftPhysical
        outwardYZSwitchPivot)
      outwardYZPivotNativeRightAsLeftAuxiliary = true := by
  decide

abbrev OutwardYZPivotNativeRightResolvedPort := ResolvedNetworkPort
  (canonicalLinkResolvedStrandNetwork 5
    (slabLinkExternalSpins 5 outwardYZSwitchLeftPhysical
      outwardYZSwitchPivot)
    outwardYZPivotNativeRightAsLeftAuxiliary
    outwardYZPivotNativeRightAllowed)

def outwardYZPivotNativeRightPortZero :
    OutwardYZPivotNativeRightResolvedPort where
  vertexIndex := ⟨0, by decide⟩
  port := .onA ⟨0, by decide⟩

def outwardYZPivotNativeRightPortOne :
    OutwardYZPivotNativeRightResolvedPort where
  vertexIndex := ⟨0, by decide⟩
  port := .onB ⟨0, by decide⟩

def outwardYZPivotNativeRightPortTwo :
    OutwardYZPivotNativeRightResolvedPort where
  vertexIndex := ⟨1, by decide⟩
  port := .onB ⟨0, by decide⟩

def outwardYZPivotNativeRightPortThree :
    OutwardYZPivotNativeRightResolvedPort where
  vertexIndex := ⟨2, by decide⟩
  port := .onB ⟨0, by decide⟩

def outwardYZPivotNativeRightTerminalZero : CanonicalPhysicalStrandPort
    (slabLinkExternalSpins 5 outwardYZSwitchLeftPhysical
      outwardYZSwitchPivot)
    outwardYZPivotNativeRightAsLeftAuxiliary
    outwardYZPivotNativeRightAllowed :=
  ⟨outwardYZPivotNativeRightPortZero, by decide⟩

def outwardYZPivotNativeRightTerminalOne : CanonicalPhysicalStrandPort
    (slabLinkExternalSpins 5 outwardYZSwitchLeftPhysical
      outwardYZSwitchPivot)
    outwardYZPivotNativeRightAsLeftAuxiliary
    outwardYZPivotNativeRightAllowed :=
  ⟨outwardYZPivotNativeRightPortOne, by decide⟩

def outwardYZPivotNativeRightTerminalTwo : CanonicalPhysicalStrandPort
    (slabLinkExternalSpins 5 outwardYZSwitchLeftPhysical
      outwardYZSwitchPivot)
    outwardYZPivotNativeRightAsLeftAuxiliary
    outwardYZPivotNativeRightAllowed :=
  ⟨outwardYZPivotNativeRightPortTwo, by decide⟩

def outwardYZPivotNativeRightTerminalThree : CanonicalPhysicalStrandPort
    (slabLinkExternalSpins 5 outwardYZSwitchLeftPhysical
      outwardYZSwitchPivot)
    outwardYZPivotNativeRightAsLeftAuxiliary
    outwardYZPivotNativeRightAllowed :=
  ⟨outwardYZPivotNativeRightPortThree, by decide⟩

theorem outwardYZPivotNativeRightZeroMate_eq_one :
    outwardYZPivotNativeRightTerminalZero.1.localMate =
      outwardYZPivotNativeRightTerminalOne.1 := by
  apply ResolvedNetworkPort.address_injective
  decide

def outwardYZPivotNativeRightZeroToOnePath : CanonicalStrandPathToPhysical
    outwardYZPivot_degree_le outwardYZPivotNativeRightAllowed
    outwardYZPivotNativeRightTerminalZero.1.localMate
    outwardYZPivotNativeRightTerminalOne := by
  rw [outwardYZPivotNativeRightZeroMate_eq_one]
  exact .stop outwardYZPivotNativeRightTerminalOne

def outwardYZPivotNativeRightTwoMate_internal :
    outwardYZPivotNativeRightTerminalTwo.1.localMate.edgeId ∈
      canonicalInternalFusionEdges 5 := by
  decide

theorem outwardYZPivotNativeRightTwoMate_advance_eq_three :
    canonicalInternalAdvancePort outwardYZPivot_degree_le
      outwardYZPivotNativeRightAllowed
      outwardYZPivotNativeRightTerminalTwo.1.localMate
      outwardYZPivotNativeRightTwoMate_internal =
        outwardYZPivotNativeRightTerminalThree.1 := by
  apply ResolvedNetworkPort.address_injective
  decide

def outwardYZPivotNativeRightTwoToThreePath : CanonicalStrandPathToPhysical
    outwardYZPivot_degree_le outwardYZPivotNativeRightAllowed
    outwardYZPivotNativeRightTerminalTwo.1.localMate
    outwardYZPivotNativeRightTerminalThree := by
  refine .advance outwardYZPivotNativeRightTerminalTwo.1.localMate
    outwardYZPivotNativeRightTwoMate_internal
    outwardYZPivotNativeRightTerminalThree ?_
  rw [outwardYZPivotNativeRightTwoMate_advance_eq_three]
  exact .stop outwardYZPivotNativeRightTerminalThree

theorem outwardYZPivotNativeRightPartner_zero_eq_one :
    canonicalPhysicalStrandPartner outwardYZPivot_degree_le
      outwardYZPivotNativeRightAllowed
      outwardYZPivotNativeRightTerminalZero =
        outwardYZPivotNativeRightTerminalOne :=
  canonicalStrandPath_terminal_unique
    (canonicalPhysicalStrandPartner_path outwardYZPivot_degree_le
      outwardYZPivotNativeRightAllowed
      outwardYZPivotNativeRightTerminalZero)
    outwardYZPivotNativeRightZeroToOnePath

theorem outwardYZPivotNativeRightPartner_two_eq_three :
    canonicalPhysicalStrandPartner outwardYZPivot_degree_le
      outwardYZPivotNativeRightAllowed
      outwardYZPivotNativeRightTerminalTwo =
        outwardYZPivotNativeRightTerminalThree :=
  canonicalStrandPath_terminal_unique
    (canonicalPhysicalStrandPartner_path outwardYZPivot_degree_le
      outwardYZPivotNativeRightAllowed
      outwardYZPivotNativeRightTerminalTwo)
    outwardYZPivotNativeRightTwoToThreePath

theorem outwardYZPivotNativeRightPartner_one_eq_zero :
    canonicalPhysicalStrandPartner outwardYZPivot_degree_le
      outwardYZPivotNativeRightAllowed
      outwardYZPivotNativeRightTerminalOne =
        outwardYZPivotNativeRightTerminalZero := by
  rw [← outwardYZPivotNativeRightPartner_zero_eq_one]
  exact canonicalPhysicalStrandPartner_involutive
    outwardYZPivot_degree_le outwardYZPivotNativeRightAllowed
    outwardYZPivotNativeRightTerminalZero

theorem outwardYZPivotNativeRightPartner_three_eq_two :
    canonicalPhysicalStrandPartner outwardYZPivot_degree_le
      outwardYZPivotNativeRightAllowed
      outwardYZPivotNativeRightTerminalThree =
        outwardYZPivotNativeRightTerminalTwo := by
  rw [← outwardYZPivotNativeRightPartner_two_eq_three]
  exact canonicalPhysicalStrandPartner_involutive
    outwardYZPivot_degree_le outwardYZPivotNativeRightAllowed
    outwardYZPivotNativeRightTerminalTwo

def outwardYZPivotNativeRightCanonicalTerminals :
    List (CanonicalPhysicalStrandPort
      (slabLinkExternalSpins 5 outwardYZSwitchLeftPhysical
        outwardYZSwitchPivot)
      outwardYZPivotNativeRightAsLeftAuxiliary
      outwardYZPivotNativeRightAllowed) :=
  (allResolvedNetworkPorts
    (canonicalLinkResolvedStrandNetwork 5
      (slabLinkExternalSpins 5 outwardYZSwitchLeftPhysical
        outwardYZSwitchPivot)
      outwardYZPivotNativeRightAsLeftAuxiliary
      outwardYZPivotNativeRightAllowed)).filterMap fun occurrence =>
        if hphysical : occurrence.edgeId < 5 then
          some ⟨occurrence, hphysical⟩
        else none

theorem outwardYZPivotNativeRightCanonicalTerminals_eq :
    outwardYZPivotNativeRightCanonicalTerminals =
      [outwardYZPivotNativeRightTerminalZero,
       outwardYZPivotNativeRightTerminalOne,
       outwardYZPivotNativeRightTerminalTwo,
       outwardYZPivotNativeRightTerminalThree] := by
  decide

def outwardYZPivotNativeRightCanonicalEdgeIdPairs : List (Nat × Nat) :=
  outwardYZPivotNativeRightCanonicalTerminals.map fun terminal =>
    (terminal.1.edgeId,
      (canonicalPhysicalStrandPartner outwardYZPivot_degree_le
        outwardYZPivotNativeRightAllowed terminal).1.edgeId)

theorem outwardYZPivotNativeRightCanonicalEdgeIdPairs_eq :
    outwardYZPivotNativeRightCanonicalEdgeIdPairs =
      [(0, 1), (1, 0), (2, 3), (3, 2)] := by
  unfold outwardYZPivotNativeRightCanonicalEdgeIdPairs
  rw [outwardYZPivotNativeRightCanonicalTerminals_eq]
  simp only [List.map_cons, List.map_nil]
  rw [outwardYZPivotNativeRightPartner_zero_eq_one,
    outwardYZPivotNativeRightPartner_one_eq_zero,
    outwardYZPivotNativeRightPartner_two_eq_three,
    outwardYZPivotNativeRightPartner_three_eq_two]
  decide

/-! ## 3. Contraction to the native right-target pairing -/

def outwardYZPivotNativeRightReindexedEdgeIdPairs : List (Nat × Nat) :=
  outwardYZPivotNativeRightCanonicalEdgeIdPairs.map
    outwardYZPivotNativeRightPositionPair

theorem outwardYZPivotNativeRightReindexedEdgeIdPairs_eq :
    outwardYZPivotNativeRightReindexedEdgeIdPairs =
      outwardYZPivotNativeRightEdgeIdPairs := by
  rw [show outwardYZPivotNativeRightReindexedEdgeIdPairs =
      outwardYZPivotNativeRightCanonicalEdgeIdPairs.map
        outwardYZPivotNativeRightPositionPair by rfl,
    outwardYZPivotNativeRightCanonicalEdgeIdPairs_eq]
  decide

def outwardYZPivotNativeRightFaceIdPairs : List (Nat × Nat) :=
  outwardYZPivotNativeRightEdgeIdPairs.map fun pair =>
    ((slabIncidentPlaqIds 5 outwardYZSwitchPivot).getD pair.1 0,
     (slabIncidentPlaqIds 5 outwardYZSwitchPivot).getD pair.2 0)

theorem outwardYZPivotNativeRightFaceIdPairs_eq :
    outwardYZPivotNativeRightFaceIdPairs =
      [(199, 231), (231, 199), (33, 232), (232, 33)] := by
  unfold outwardYZPivotNativeRightFaceIdPairs
  rw [outwardYZPivot_incidentFaceIds]
  decide

def OutwardYZPivotFaceIdPairSameSide (pair : Nat × Nat) : Prop :=
  (slabPlaquetteAt 5 pair.1 ∈ outwardYSurface ∧
    slabPlaquetteAt 5 pair.2 ∈ outwardYSurface) ∨
  (slabPlaquetteAt 5 pair.1 ∈ outwardZSurface ∧
    slabPlaquetteAt 5 pair.2 ∈ outwardZSurface)

theorem outwardYZPivotNativeRightFaceIdPair_same_side
    (pair : Nat × Nat)
    (hpair : pair ∈ outwardYZPivotNativeRightFaceIdPairs) :
    OutwardYZPivotFaceIdPairSameSide pair := by
  rw [outwardYZPivotNativeRightFaceIdPairs_eq] at hpair
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
  rcases hpair with rfl | rfl | rfl | rfl <;>
    unfold OutwardYZPivotFaceIdPairSameSide <;> decide

/-- The reindexed production tree is a literal compiler for the selected
target's native right-tree channel data and physical pairing. -/
structure OutwardYZPivotNativeRightPairingCertificate : Type where
  targetChannel :
    outwardYZPivotLeftTarget.m = 0 ∧
    outwardYZPivotLeftTarget.inner.order = 1 ∧
    outwardYZPivotLeftTarget.second.p = 0 ∧
    outwardYZPivotLeftTarget.second.r = 1
  firstIntermediate :
    outwardYZPivotNativeRightAsLeftAuxiliary 6 = 0
  secondIntermediate :
    outwardYZPivotNativeRightAsLeftAuxiliary 7 = 1
  accepted : outwardYZPivotNativeRightAsLeftAuxiliary ∈
    slabLinkFusionWitnesses 1 5 outwardYZSwitchLeftPhysical
      outwardYZSwitchPivot
  nativePairing : outwardYZPivotNativeRightReindexedEdgeIdPairs =
    outwardYZPivotNativeRightEdgeIdPairs
  nativeFacePairing : outwardYZPivotNativeRightFaceIdPairs =
    [(199, 231), (231, 199), (33, 232), (232, 33)]
  nativePairsStayOnSide : forall pair,
    pair ∈ outwardYZPivotNativeRightFaceIdPairs ->
      OutwardYZPivotFaceIdPairSameSide pair
  equalRankPairingDiffers : outwardYZPivotActualEdgeIdPairs
      outwardYZPivotLeftAuxiliary_mem ≠
    outwardYZPivotNativeRightEdgeIdPairs

def outwardYZPivotNativeRightPairingCertificate :
    OutwardYZPivotNativeRightPairingCertificate :=
  { targetChannel := outwardYZPivotLeftTarget_native_channel_data
    firstIntermediate :=
      outwardYZPivotNativeRightAsLeftAuxiliary_firstIntermediate
    secondIntermediate :=
      outwardYZPivotNativeRightAsLeftAuxiliary_secondIntermediate
    accepted := outwardYZPivotNativeRightAsLeftAuxiliary_mem
    nativePairing := outwardYZPivotNativeRightReindexedEdgeIdPairs_eq
    nativeFacePairing := outwardYZPivotNativeRightFaceIdPairs_eq
    nativePairsStayOnSide :=
      outwardYZPivotNativeRightFaceIdPair_same_side
    equalRankPairingDiffers :=
      outwardYZPivotActualEdgeIdPairs_ne_native
        outwardYZPivotLeftAuxiliary_mem }

#print axioms outwardYZPivotNativeRightAsLeftAuxiliary_mem
#print axioms outwardYZPivotNativeRightZeroToOnePath
#print axioms outwardYZPivotNativeRightTwoToThreePath
#print axioms outwardYZPivotNativeRightCanonicalEdgeIdPairs_eq
#print axioms outwardYZPivotNativeRightReindexedEdgeIdPairs_eq
#print axioms outwardYZPivotNativeRightFaceIdPairs_eq
#print axioms outwardYZPivotNativeRightFaceIdPair_same_side
#print axioms outwardYZPivotNativeRightPairingCertificate

end YMGap.Continuum.Z4OutwardYZEdgeTouchSlabNativeRightPairing
