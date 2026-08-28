/-
# Every aligned-diagonal nonpivot strand edge preserves its cut side

At an arbitrary accepted link, a physical terminal and its canonical partner
both lie on positive faces of the binary aligned support.  Hence each endpoint
is a face of the near cube or of the diagonally displaced far cube.  If those
endpoints belonged to different cubes, their common lattice link would be the
unique cut pivot.  Every nonpivot terminal pair therefore stays within one
side, independently of the selected sparse target column.

Constructive contract: literal terminal slots, binary support membership, and
the proved one-link cut geometry only; no choice, `Classical`,
`native_decide`, `sorry`, new axiom, noncomputable declaration, or unbounded
heartbeat option.
-/

import YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabPivotPairing

namespace YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabNonpivotPairing

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchCutCarrier
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabPivotPairing
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabWholeProductPositivity
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

/-! ## 1. Recover geometric support and incidence from a terminal face -/

theorem alignedDiagonalSlabPlaquetteAt_edge_of_mem_incident
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

theorem alignedDiagonalSwitchFace_mem_of_positive
    {faceId : Nat} (hphysical : faceId ∈ slabPhysicalFaceEdges 5)
    (hpositive : 0 < alignedDiagonalSwitchLeftPhysical faceId) :
    slabPlaquetteAt 5 faceId ∈ alignedDiagonalSwitchSurface := by
  have hindicator := slabBinarySupportLabelling_eq_indicator
    (support := alignedDiagonalSwitchSurface) hphysical
  change slabBinarySupportLabelling 5 alignedDiagonalSwitchSurface faceId =
      (if slabPlaquetteAt 5 faceId ∈ alignedDiagonalSwitchSurface
        then 1 else 0) at hindicator
  by_cases hmem :
      slabPlaquetteAt 5 faceId ∈ alignedDiagonalSwitchSurface
  · exact hmem
  · have hzero : alignedDiagonalSwitchLeftPhysical faceId = 0 := by
      change slabBinarySupportLabelling 5
        alignedDiagonalSwitchSurface faceId = 0
      rw [hindicator]
      simp [hmem]
    rw [hzero] at hpositive
    exact False.elim (Nat.not_lt_zero 0 hpositive)

/-! ## 2. The nonpivot two-color theorem -/

theorem alignedDiagonalNonpivotTerminal_pair_same_side
    {link : SlabLink} (hnonpivot : link ≠ alignedDiagonalSwitchPivot)
    {auxiliary : SlabLabelling}
    (hmem : auxiliary ∈
      slabLinkFusionWitnesses 1 5 alignedDiagonalSwitchLeftPhysical link)
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      alignedDiagonalSwitchLeftPhysical link auxiliary hmem) :
    let partner := slabLinkPhysicalStrandPartner 1 5
      alignedDiagonalSwitchLeftPhysical link auxiliary hmem terminal
    let sourceFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        alignedDiagonalSwitchLeftPhysical link auxiliary hmem terminal).faceId
    let targetFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        alignedDiagonalSwitchLeftPhysical link auxiliary hmem partner).faceId
    (sourceFace ∈ alignedDiagonalNearSurface ∧
        targetFace ∈ alignedDiagonalNearSurface) ∨
      (sourceFace ∈ alignedDiagonalFarSurface ∧
        targetFace ∈ alignedDiagonalFarSurface) := by
  dsimp only
  let partner := slabLinkPhysicalStrandPartner 1 5
    alignedDiagonalSwitchLeftPhysical link auxiliary hmem terminal
  let sourceOccurrence := slabLinkPhysicalTerminalOccurrence 1 5
    alignedDiagonalSwitchLeftPhysical link auxiliary hmem terminal
  let targetOccurrence := slabLinkPhysicalTerminalOccurrence 1 5
    alignedDiagonalSwitchLeftPhysical link auxiliary hmem partner
  have hsourcePhysical : sourceOccurrence.faceId ∈
      slabPhysicalFaceEdges 5 := sourceOccurrence.faceId_physical
  have htargetPhysical : targetOccurrence.faceId ∈
      slabPhysicalFaceEdges 5 := targetOccurrence.faceId_physical
  have hsourcePositive :
      0 < alignedDiagonalSwitchLeftPhysical sourceOccurrence.faceId := by
    have hslot := sourceOccurrence.slot.isLt
    change 0 < alignedDiagonalSwitchLeftPhysical
      ((slabIncidentPlaqIds 5 link).get sourceOccurrence.position)
    omega
  have htargetPositive :
      0 < alignedDiagonalSwitchLeftPhysical targetOccurrence.faceId := by
    have hslot := targetOccurrence.slot.isLt
    change 0 < alignedDiagonalSwitchLeftPhysical
      ((slabIncidentPlaqIds 5 link).get targetOccurrence.position)
    omega
  have hsourceSupport : slabPlaquetteAt 5 sourceOccurrence.faceId ∈
      alignedDiagonalSwitchSurface :=
    alignedDiagonalSwitchFace_mem_of_positive
      hsourcePhysical hsourcePositive
  have htargetSupport : slabPlaquetteAt 5 targetOccurrence.faceId ∈
      alignedDiagonalSwitchSurface :=
    alignedDiagonalSwitchFace_mem_of_positive
      htargetPhysical htargetPositive
  have hsourceLink : link ∈
      edgesOf (slabPlaquetteAt 5 sourceOccurrence.faceId) :=
    alignedDiagonalSlabPlaquetteAt_edge_of_mem_incident
      sourceOccurrence.faceId_mem_incident
  have htargetLink : link ∈
      edgesOf (slabPlaquetteAt 5 targetOccurrence.faceId) :=
    alignedDiagonalSlabPlaquetteAt_edge_of_mem_incident
      targetOccurrence.faceId_mem_incident
  have hsourceSide :
      slabPlaquetteAt 5 sourceOccurrence.faceId ∈
          alignedDiagonalNearSurface ∨
      slabPlaquetteAt 5 sourceOccurrence.faceId ∈
          alignedDiagonalFarSurface := by
    exact List.mem_append.mp hsourceSupport
  have htargetSide :
      slabPlaquetteAt 5 targetOccurrence.faceId ∈
          alignedDiagonalNearSurface ∨
      slabPlaquetteAt 5 targetOccurrence.faceId ∈
          alignedDiagonalFarSurface := by
    exact List.mem_append.mp htargetSupport
  rcases hsourceSide with hsourceNear | hsourceFar
  · rcases htargetSide with htargetNear | htargetFar
    · exact Or.inl ⟨hsourceNear, htargetNear⟩
    · exact False.elim (hnonpivot
        (alignedDiagonal_crossSharedLink_eq_pivot
          hsourceNear htargetFar hsourceLink htargetLink))
  · rcases htargetSide with htargetNear | htargetFar
    · exact False.elim (hnonpivot
        (alignedDiagonal_crossSharedLink_eq_pivot
          htargetNear hsourceFar htargetLink hsourceLink))
    · exact Or.inr ⟨hsourceFar, htargetFar⟩

#print axioms alignedDiagonalSlabPlaquetteAt_edge_of_mem_incident
#print axioms alignedDiagonalSwitchFace_mem_of_positive
#print axioms alignedDiagonalNonpivotTerminal_pair_same_side

end YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabNonpivotPairing
