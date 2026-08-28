/-
# Every reflected bent-cube nonpivot strand edge preserves its lobe

At an accepted link, a physical terminal and its canonical partner both lie
on positive faces of the binary support.  Hence both are faces of the near or
far lobe.  If they belonged to different lobes, their common lattice link
would be the unique shared pivot.  Every nonpivot terminal pair therefore
stays within one lobe, independently of the chosen sparse target column.

Constructive contract: binary support membership and the proved one-link cut
geometry only; no choice, `Classical`, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotPairing

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabNonpivotPairing

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchCutCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotPairing
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabWholeProductPositivity

/-! ## 1. Recover geometric support and incidence from a terminal face -/

theorem reflectedBentSlabPlaquetteAt_edge_of_mem_incident
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

theorem reflectedBentSwitchFace_mem_of_positive
    {faceId : Nat} (hphysical : faceId ∈ slabPhysicalFaceEdges 5)
    (hpositive : 0 < reflectedBentSwitchLeftPhysical faceId) :
    slabPlaquetteAt 5 faceId ∈
      YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile.reflectedBentSwitchSurface := by
  have hindicator := slabBinarySupportLabelling_eq_indicator
    (support :=
      YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile.reflectedBentSwitchSurface)
    hphysical
  change slabBinarySupportLabelling 5
      YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile.reflectedBentSwitchSurface
      faceId =
      (if slabPlaquetteAt 5 faceId ∈
        YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile.reflectedBentSwitchSurface
        then 1 else 0) at hindicator
  by_cases hmem : slabPlaquetteAt 5 faceId ∈
      YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile.reflectedBentSwitchSurface
  · exact hmem
  · have hzero : reflectedBentSwitchLeftPhysical faceId = 0 := by
      change slabBinarySupportLabelling 5
        YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile.reflectedBentSwitchSurface
        faceId = 0
      rw [hindicator]
      simp [hmem]
    rw [hzero] at hpositive
    exact False.elim (Nat.not_lt_zero 0 hpositive)

/-! ## 2. The nonpivot two-color theorem -/

theorem reflectedBentNonpivotTerminal_pair_same_side
    {link : SlabLink} (hnonpivot : link ≠ reflectedBentSwitchPivot)
    {auxiliary : SlabLabelling}
    (hmem : auxiliary ∈
      slabLinkFusionWitnesses 1 5 reflectedBentSwitchLeftPhysical link)
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      reflectedBentSwitchLeftPhysical link auxiliary hmem) :
    let partner := slabLinkPhysicalStrandPartner 1 5
      reflectedBentSwitchLeftPhysical link auxiliary hmem terminal
    let sourceFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        reflectedBentSwitchLeftPhysical link auxiliary hmem terminal).faceId
    let targetFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        reflectedBentSwitchLeftPhysical link auxiliary hmem partner).faceId
    (sourceFace ∈ reflectedBentNearSurface ∧
        targetFace ∈ reflectedBentNearSurface) ∨
      (sourceFace ∈ reflectedBentFarSurface ∧
        targetFace ∈ reflectedBentFarSurface) := by
  dsimp only
  let partner := slabLinkPhysicalStrandPartner 1 5
    reflectedBentSwitchLeftPhysical link auxiliary hmem terminal
  let sourceOccurrence := slabLinkPhysicalTerminalOccurrence 1 5
    reflectedBentSwitchLeftPhysical link auxiliary hmem terminal
  let targetOccurrence := slabLinkPhysicalTerminalOccurrence 1 5
    reflectedBentSwitchLeftPhysical link auxiliary hmem partner
  have hsourcePhysical : sourceOccurrence.faceId ∈
      slabPhysicalFaceEdges 5 := sourceOccurrence.faceId_physical
  have htargetPhysical : targetOccurrence.faceId ∈
      slabPhysicalFaceEdges 5 := targetOccurrence.faceId_physical
  have hsourcePositive :
      0 < reflectedBentSwitchLeftPhysical sourceOccurrence.faceId := by
    have hslot := sourceOccurrence.slot.isLt
    change 0 < reflectedBentSwitchLeftPhysical
      ((slabIncidentPlaqIds 5 link).get sourceOccurrence.position)
    omega
  have htargetPositive :
      0 < reflectedBentSwitchLeftPhysical targetOccurrence.faceId := by
    have hslot := targetOccurrence.slot.isLt
    change 0 < reflectedBentSwitchLeftPhysical
      ((slabIncidentPlaqIds 5 link).get targetOccurrence.position)
    omega
  have hsourceSupport : slabPlaquetteAt 5 sourceOccurrence.faceId ∈
      YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile.reflectedBentSwitchSurface :=
    reflectedBentSwitchFace_mem_of_positive
      hsourcePhysical hsourcePositive
  have htargetSupport : slabPlaquetteAt 5 targetOccurrence.faceId ∈
      YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile.reflectedBentSwitchSurface :=
    reflectedBentSwitchFace_mem_of_positive
      htargetPhysical htargetPositive
  have hsourceLink : link ∈
      edgesOf (slabPlaquetteAt 5 sourceOccurrence.faceId) :=
    reflectedBentSlabPlaquetteAt_edge_of_mem_incident
      sourceOccurrence.faceId_mem_incident
  have htargetLink : link ∈
      edgesOf (slabPlaquetteAt 5 targetOccurrence.faceId) :=
    reflectedBentSlabPlaquetteAt_edge_of_mem_incident
      targetOccurrence.faceId_mem_incident
  have hsourceSide :
      slabPlaquetteAt 5 sourceOccurrence.faceId ∈ reflectedBentNearSurface ∨
      slabPlaquetteAt 5 sourceOccurrence.faceId ∈ reflectedBentFarSurface := by
    exact List.mem_append.mp hsourceSupport
  have htargetSide :
      slabPlaquetteAt 5 targetOccurrence.faceId ∈ reflectedBentNearSurface ∨
      slabPlaquetteAt 5 targetOccurrence.faceId ∈ reflectedBentFarSurface := by
    exact List.mem_append.mp htargetSupport
  rcases hsourceSide with hsourceNear | hsourceFar
  · rcases htargetSide with htargetNear | htargetFar
    · exact Or.inl ⟨hsourceNear, htargetNear⟩
    · exact False.elim (hnonpivot
        (reflectedBent_crossSharedLink_eq_pivot
          hsourceNear htargetFar hsourceLink htargetLink))
  · rcases htargetSide with htargetNear | htargetFar
    · exact False.elim (hnonpivot
        (reflectedBent_crossSharedLink_eq_pivot
          htargetNear hsourceFar htargetLink hsourceLink))
    · exact Or.inr ⟨hsourceFar, htargetFar⟩

#print axioms reflectedBentSlabPlaquetteAt_edge_of_mem_incident
#print axioms reflectedBentSwitchFace_mem_of_positive
#print axioms reflectedBentNonpivotTerminal_pair_same_side

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabNonpivotPairing
