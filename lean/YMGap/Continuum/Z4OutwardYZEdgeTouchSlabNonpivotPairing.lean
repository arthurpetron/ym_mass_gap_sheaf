/-
# Every outward Y/Z nonpivot strand edge preserves its cube side

At an arbitrary accepted link, a physical terminal and its canonical partner
both lie on positive faces of the binary outward Y/Z support.  Hence each
endpoint is a face of the Y cube or of the Z cube.  If the two endpoints had
different sides, their common lattice link would be the unique geometric
pivot.  Therefore every nonpivot terminal pair stays within one side,
independently of the selected sparse target column.

Constructive contract: literal terminal slots, binary support membership, and
the proved one-link cut geometry only; no choice, `Classical`,
`native_decide`, `sorry`, new axiom, noncomputable declaration, or unbounded
heartbeat option.
-/

import YMGap.Continuum.Z4OutwardYZEdgeTouchSlabPivotPairing

namespace YMGap.Continuum.Z4OutwardYZEdgeTouchSlabNonpivotPairing

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier
open YMGap.Continuum.Z4OutwardYZEdgeTouchCutCarrier
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabPivotPairing
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabWholeProductPositivity

/-! ## 1. Recover geometric support and incidence from a terminal face -/

theorem slabPlaquetteAt_edge_of_mem_incident
    {extent : Nat} {link : SlabLink} {faceId : Nat}
    (hface : faceId ∈ slabIncidentPlaqIds extent link) :
    link ∈ edgesOf (slabPlaquetteAt extent faceId) := by
  obtain ⟨plaquette, hindexed, hedge⟩ :=
    mem_slabIncidentPlaqIds.mp hface
  have hlookup : slabPlaquetteAt extent faceId = plaquette := by
    unfold slabPlaquetteAt
    exact enumerate_getD_of_mem fallbackPlaquette hindexed
  rw [hlookup]
  exact hedge

theorem outwardYZSwitchFace_mem_of_positive
    {faceId : Nat} (hphysical : faceId ∈ slabPhysicalFaceEdges 5)
    (hpositive : 0 < outwardYZSwitchLeftPhysical faceId) :
    slabPlaquetteAt 5 faceId ∈ outwardYZSwitchSurface := by
  have hindicator := slabBinarySupportLabelling_eq_indicator
    (support := outwardYZSwitchSurface) hphysical
  change slabBinarySupportLabelling 5 outwardYZSwitchSurface faceId =
      (if slabPlaquetteAt 5 faceId ∈ outwardYZSwitchSurface then 1 else 0)
    at hindicator
  by_cases hmem : slabPlaquetteAt 5 faceId ∈ outwardYZSwitchSurface
  · exact hmem
  · have hzero : outwardYZSwitchLeftPhysical faceId = 0 := by
      change slabBinarySupportLabelling 5 outwardYZSwitchSurface faceId = 0
      rw [hindicator]
      simp [hmem]
    rw [hzero] at hpositive
    exact False.elim (Nat.not_lt_zero 0 hpositive)

/-! ## 2. The selected pivot carrier is cross-side -/

theorem outwardYZPivotTerminal_pair_cross_side
    (hmem : outwardYZPivotLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5 outwardYZSwitchLeftPhysical
        outwardYZSwitchPivot)
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      outwardYZSwitchLeftPhysical outwardYZSwitchPivot
      outwardYZPivotLeftAuxiliary hmem) :
    let partner := slabLinkPhysicalStrandPartner 1 5
      outwardYZSwitchLeftPhysical outwardYZSwitchPivot
      outwardYZPivotLeftAuxiliary hmem terminal
    let sourceFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        outwardYZSwitchLeftPhysical outwardYZSwitchPivot
        outwardYZPivotLeftAuxiliary hmem terminal).faceId
    let targetFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        outwardYZSwitchLeftPhysical outwardYZSwitchPivot
        outwardYZPivotLeftAuxiliary hmem partner).faceId
    (sourceFace ∈ outwardZSurface ∧ targetFace ∈ outwardYSurface) ∨
      (sourceFace ∈ outwardYSurface ∧ targetFace ∈ outwardZSurface) := by
  dsimp only
  let partner := slabLinkPhysicalStrandPartner 1 5
    outwardYZSwitchLeftPhysical outwardYZSwitchPivot
    outwardYZPivotLeftAuxiliary hmem terminal
  have hfaces := outwardYZPivotActual_partner_faceId_pair hmem terminal
  rcases hfaces with hZ | hY | hZ | hY
  · left
    have hs : (slabLinkPhysicalTerminalOccurrence 1 5
        outwardYZSwitchLeftPhysical outwardYZSwitchPivot
        outwardYZPivotLeftAuxiliary hmem terminal).faceId = 33 := by
      simpa only using congrArg Prod.fst hZ
    have ht : (slabLinkPhysicalTerminalOccurrence 1 5
        outwardYZSwitchLeftPhysical outwardYZSwitchPivot
        outwardYZPivotLeftAuxiliary hmem partner).faceId = 231 := by
      simpa only [partner] using congrArg Prod.snd hZ
    rw [hs, ht]
    constructor <;> decide
  · right
    have hs : (slabLinkPhysicalTerminalOccurrence 1 5
        outwardYZSwitchLeftPhysical outwardYZSwitchPivot
        outwardYZPivotLeftAuxiliary hmem terminal).faceId = 199 := by
      simpa only using congrArg Prod.fst hY
    have ht : (slabLinkPhysicalTerminalOccurrence 1 5
        outwardYZSwitchLeftPhysical outwardYZSwitchPivot
        outwardYZPivotLeftAuxiliary hmem partner).faceId = 232 := by
      simpa only [partner] using congrArg Prod.snd hY
    rw [hs, ht]
    constructor <;> decide
  · right
    have hs : (slabLinkPhysicalTerminalOccurrence 1 5
        outwardYZSwitchLeftPhysical outwardYZSwitchPivot
        outwardYZPivotLeftAuxiliary hmem terminal).faceId = 231 := by
      simpa only using congrArg Prod.fst hZ
    have ht : (slabLinkPhysicalTerminalOccurrence 1 5
        outwardYZSwitchLeftPhysical outwardYZSwitchPivot
        outwardYZPivotLeftAuxiliary hmem partner).faceId = 33 := by
      simpa only [partner] using congrArg Prod.snd hZ
    rw [hs, ht]
    constructor <;> decide
  · left
    have hs : (slabLinkPhysicalTerminalOccurrence 1 5
        outwardYZSwitchLeftPhysical outwardYZSwitchPivot
        outwardYZPivotLeftAuxiliary hmem terminal).faceId = 232 := by
      simpa only using congrArg Prod.fst hY
    have ht : (slabLinkPhysicalTerminalOccurrence 1 5
        outwardYZSwitchLeftPhysical outwardYZSwitchPivot
        outwardYZPivotLeftAuxiliary hmem partner).faceId = 199 := by
      simpa only [partner] using congrArg Prod.snd hY
    rw [hs, ht]
    constructor <;> decide

/-! ## 3. The nonpivot two-color theorem -/

theorem outwardYZNonpivotTerminal_pair_same_side
    {link : SlabLink} (hnonpivot : link ≠ outwardYZSwitchPivot)
    {auxiliary : SlabLabelling}
    (hmem : auxiliary ∈
      slabLinkFusionWitnesses 1 5 outwardYZSwitchLeftPhysical link)
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      outwardYZSwitchLeftPhysical link auxiliary hmem) :
    let partner := slabLinkPhysicalStrandPartner 1 5
      outwardYZSwitchLeftPhysical link auxiliary hmem terminal
    let sourceFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        outwardYZSwitchLeftPhysical link auxiliary hmem terminal).faceId
    let targetFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        outwardYZSwitchLeftPhysical link auxiliary hmem partner).faceId
    (sourceFace ∈ outwardYSurface ∧ targetFace ∈ outwardYSurface) ∨
      (sourceFace ∈ outwardZSurface ∧ targetFace ∈ outwardZSurface) := by
  dsimp only
  let partner := slabLinkPhysicalStrandPartner 1 5
    outwardYZSwitchLeftPhysical link auxiliary hmem terminal
  let sourceOccurrence := slabLinkPhysicalTerminalOccurrence 1 5
    outwardYZSwitchLeftPhysical link auxiliary hmem terminal
  let targetOccurrence := slabLinkPhysicalTerminalOccurrence 1 5
    outwardYZSwitchLeftPhysical link auxiliary hmem partner
  have hsourcePhysical : sourceOccurrence.faceId ∈
      slabPhysicalFaceEdges 5 := sourceOccurrence.faceId_physical
  have htargetPhysical : targetOccurrence.faceId ∈
      slabPhysicalFaceEdges 5 := targetOccurrence.faceId_physical
  have hsourcePositive :
      0 < outwardYZSwitchLeftPhysical sourceOccurrence.faceId := by
    have hslot := sourceOccurrence.slot.isLt
    change 0 < outwardYZSwitchLeftPhysical
      ((slabIncidentPlaqIds 5 link).get sourceOccurrence.position)
    omega
  have htargetPositive :
      0 < outwardYZSwitchLeftPhysical targetOccurrence.faceId := by
    have hslot := targetOccurrence.slot.isLt
    change 0 < outwardYZSwitchLeftPhysical
      ((slabIncidentPlaqIds 5 link).get targetOccurrence.position)
    omega
  have hsourceSupport : slabPlaquetteAt 5 sourceOccurrence.faceId ∈
      outwardYZSwitchSurface :=
    outwardYZSwitchFace_mem_of_positive hsourcePhysical hsourcePositive
  have htargetSupport : slabPlaquetteAt 5 targetOccurrence.faceId ∈
      outwardYZSwitchSurface :=
    outwardYZSwitchFace_mem_of_positive htargetPhysical htargetPositive
  have hsourceLink : link ∈
      edgesOf (slabPlaquetteAt 5 sourceOccurrence.faceId) :=
    slabPlaquetteAt_edge_of_mem_incident
      sourceOccurrence.faceId_mem_incident
  have htargetLink : link ∈
      edgesOf (slabPlaquetteAt 5 targetOccurrence.faceId) :=
    slabPlaquetteAt_edge_of_mem_incident
      targetOccurrence.faceId_mem_incident
  have hsourceSide :
      slabPlaquetteAt 5 sourceOccurrence.faceId ∈ outwardYSurface ∨
      slabPlaquetteAt 5 sourceOccurrence.faceId ∈ outwardZSurface := by
    exact List.mem_append.mp hsourceSupport
  have htargetSide :
      slabPlaquetteAt 5 targetOccurrence.faceId ∈ outwardYSurface ∨
      slabPlaquetteAt 5 targetOccurrence.faceId ∈ outwardZSurface := by
    exact List.mem_append.mp htargetSupport
  rcases hsourceSide with hsourceY | hsourceZ
  · rcases htargetSide with htargetY | htargetZ
    · exact Or.inl ⟨hsourceY, htargetY⟩
    · exact False.elim (hnonpivot
        (outwardYZ_crossSharedLink_eq_pivot
          hsourceY htargetZ hsourceLink htargetLink))
  · rcases htargetSide with htargetY | htargetZ
    · exact False.elim (hnonpivot
        (outwardYZ_crossSharedLink_eq_pivot
          htargetY hsourceZ htargetLink hsourceLink))
    · exact Or.inr ⟨hsourceZ, htargetZ⟩

#print axioms slabPlaquetteAt_edge_of_mem_incident
#print axioms outwardYZSwitchFace_mem_of_positive
#print axioms outwardYZPivotTerminal_pair_cross_side
#print axioms outwardYZNonpivotTerminal_pair_same_side

end YMGap.Continuum.Z4OutwardYZEdgeTouchSlabNonpivotPairing
