/-
# Every two-pivot repair nonpivot strand edge preserves its lobe

Both terminals of an accepted local strand lie on positive faces of the
binary support, hence on one of the two repair lobes.  If the two faces were
on different lobes, their common lattice link would be one of the two proved
cross-lobe pivots.  Excluding both pivots therefore forces every nonpivot
terminal pair to remain in a single lobe, independently of its sparse target
column.

Constructive contract: binary support membership and the proved two-link cut
geometry only; no choice, `Classical`, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabPivotPairing

namespace YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabNonpivotPairing

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
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairCutCarrier
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabPivotPairing
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabSwitchingProfile

/-! ## 1. Recover geometric support and incidence from a terminal face -/

theorem outwardYZCanonicalRepairSlabPlaquetteAt_edge_of_mem_incident
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

theorem outwardYZCanonicalRepairSwitchFace_mem_of_positive
    {faceId : Nat} (hphysical : faceId ∈ slabPhysicalFaceEdges 5)
    (hpositive : 0 < outwardYZCanonicalRepairSwitchLeftPhysical faceId) :
    slabPlaquetteAt 5 faceId ∈ outwardYZCanonicalRepairSwitchSurface := by
  have hindicator := slabBinarySupportLabelling_eq_indicator
    (support := outwardYZCanonicalRepairSwitchSurface) hphysical
  change slabBinarySupportLabelling 5
      outwardYZCanonicalRepairSwitchSurface faceId =
      (if slabPlaquetteAt 5 faceId ∈
        outwardYZCanonicalRepairSwitchSurface then 1 else 0) at hindicator
  by_cases hmem : slabPlaquetteAt 5 faceId ∈
      outwardYZCanonicalRepairSwitchSurface
  · exact hmem
  · have hzero : outwardYZCanonicalRepairSwitchLeftPhysical faceId = 0 := by
      change slabBinarySupportLabelling 5
        outwardYZCanonicalRepairSwitchSurface faceId = 0
      rw [hindicator]
      simp [hmem]
    rw [hzero] at hpositive
    exact False.elim (Nat.not_lt_zero 0 hpositive)

/-! ## 2. The nonpivot two-color theorem -/

theorem outwardYZCanonicalRepairNonpivotTerminal_pair_same_side
    {link : SlabLink}
    (hneSpatial : link ≠ outwardYZCanonicalRepairSwitchSpatialPivot)
    (hneTemporal : link ≠ outwardYZCanonicalRepairSwitchTemporalPivot)
    {auxiliary : SlabLabelling}
    (hmem : auxiliary ∈
      slabLinkFusionWitnesses 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical link)
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      outwardYZCanonicalRepairSwitchLeftPhysical link auxiliary hmem) :
    let partner := slabLinkPhysicalStrandPartner 1 5
      outwardYZCanonicalRepairSwitchLeftPhysical link auxiliary hmem terminal
    let sourceFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical link auxiliary hmem
        terminal).faceId
    let targetFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        outwardYZCanonicalRepairSwitchLeftPhysical link auxiliary hmem
        partner).faceId
    (sourceFace ∈ outwardYZCanonicalRepairTargetLobe ∧
        targetFace ∈ outwardYZCanonicalRepairTargetLobe) ∨
      (sourceFace ∈ outwardYZCanonicalRepairRootLobe ∧
        targetFace ∈ outwardYZCanonicalRepairRootLobe) := by
  dsimp only
  let partner := slabLinkPhysicalStrandPartner 1 5
    outwardYZCanonicalRepairSwitchLeftPhysical link auxiliary hmem terminal
  let sourceOccurrence := slabLinkPhysicalTerminalOccurrence 1 5
    outwardYZCanonicalRepairSwitchLeftPhysical link auxiliary hmem terminal
  let targetOccurrence := slabLinkPhysicalTerminalOccurrence 1 5
    outwardYZCanonicalRepairSwitchLeftPhysical link auxiliary hmem partner
  have hsourcePhysical : sourceOccurrence.faceId ∈
      slabPhysicalFaceEdges 5 := sourceOccurrence.faceId_physical
  have htargetPhysical : targetOccurrence.faceId ∈
      slabPhysicalFaceEdges 5 := targetOccurrence.faceId_physical
  have hsourcePositive :
      0 < outwardYZCanonicalRepairSwitchLeftPhysical
        sourceOccurrence.faceId := by
    have hslot := sourceOccurrence.slot.isLt
    change 0 < outwardYZCanonicalRepairSwitchLeftPhysical
      ((slabIncidentPlaqIds 5 link).get sourceOccurrence.position)
    omega
  have htargetPositive :
      0 < outwardYZCanonicalRepairSwitchLeftPhysical
        targetOccurrence.faceId := by
    have hslot := targetOccurrence.slot.isLt
    change 0 < outwardYZCanonicalRepairSwitchLeftPhysical
      ((slabIncidentPlaqIds 5 link).get targetOccurrence.position)
    omega
  have hsourceSupport : slabPlaquetteAt 5 sourceOccurrence.faceId ∈
      outwardYZCanonicalRepairSwitchSurface :=
    outwardYZCanonicalRepairSwitchFace_mem_of_positive
      hsourcePhysical hsourcePositive
  have htargetSupport : slabPlaquetteAt 5 targetOccurrence.faceId ∈
      outwardYZCanonicalRepairSwitchSurface :=
    outwardYZCanonicalRepairSwitchFace_mem_of_positive
      htargetPhysical htargetPositive
  have hsourceLink : link ∈
      edgesOf (slabPlaquetteAt 5 sourceOccurrence.faceId) :=
    outwardYZCanonicalRepairSlabPlaquetteAt_edge_of_mem_incident
      sourceOccurrence.faceId_mem_incident
  have htargetLink : link ∈
      edgesOf (slabPlaquetteAt 5 targetOccurrence.faceId) :=
    outwardYZCanonicalRepairSlabPlaquetteAt_edge_of_mem_incident
      targetOccurrence.faceId_mem_incident
  have hsourceSide :
      slabPlaquetteAt 5 sourceOccurrence.faceId ∈
          outwardYZCanonicalRepairTargetLobe ∨
        slabPlaquetteAt 5 sourceOccurrence.faceId ∈
          outwardYZCanonicalRepairRootLobe :=
    List.mem_append.mp hsourceSupport
  have htargetSide :
      slabPlaquetteAt 5 targetOccurrence.faceId ∈
          outwardYZCanonicalRepairTargetLobe ∨
        slabPlaquetteAt 5 targetOccurrence.faceId ∈
          outwardYZCanonicalRepairRootLobe :=
    List.mem_append.mp htargetSupport
  rcases hsourceSide with hsourceTarget | hsourceRoot
  · rcases htargetSide with htargetTarget | htargetRoot
    · exact Or.inl ⟨hsourceTarget, htargetTarget⟩
    · have hpivots := outwardYZCanonicalRepair_crossSharedLink_mem_pivots
        hsourceTarget htargetRoot hsourceLink htargetLink
      have hpivots' :
          link = outwardYZCanonicalRepairSwitchSpatialPivot ∨
            link = outwardYZCanonicalRepairSwitchTemporalPivot := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false] using hpivots
      rcases hpivots' with hspatial | htemporal
      · exact False.elim (hneSpatial hspatial)
      · exact False.elim (hneTemporal htemporal)
  · rcases htargetSide with htargetTarget | htargetRoot
    · have hpivots := outwardYZCanonicalRepair_crossSharedLink_mem_pivots
        htargetTarget hsourceRoot htargetLink hsourceLink
      have hpivots' :
          link = outwardYZCanonicalRepairSwitchSpatialPivot ∨
            link = outwardYZCanonicalRepairSwitchTemporalPivot := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false] using hpivots
      rcases hpivots' with hspatial | htemporal
      · exact False.elim (hneSpatial hspatial)
      · exact False.elim (hneTemporal htemporal)
    · exact Or.inr ⟨hsourceRoot, htargetRoot⟩

#print axioms outwardYZCanonicalRepairSlabPlaquetteAt_edge_of_mem_incident
#print axioms outwardYZCanonicalRepairSwitchFace_mem_of_positive
#print axioms outwardYZCanonicalRepairNonpivotTerminal_pair_same_side

end YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabNonpivotPairing
