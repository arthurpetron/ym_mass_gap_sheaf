/-
# Color-preserving guarded-target edges at every cutoff

At the pivot, use the cutoff-stable explicit carrier.  At any other active
left link, the unique shared near/far link geometry prevents a crossing,
independently of which accepted auxiliary realizes the positive target.
Active right links have zero physical word, and inactive links cannot touch
the inserted near support.  Hence every projected edge preserves the near/far
color at every ambient cutoff.

Constructive contract: accepted terminal witnesses, literal incidence, and
Boolean color transport only; no `Classical`, choice, `native_decide`,
`sorry`, new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetEdges
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPivotEdgesCutoffPersistence

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetEdgesCutoffPersistence

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchCutCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuard
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLinkWords
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetEdges
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPivotEdgesCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPivotPairing
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealizationCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabNonpivotPairing
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile

/-! ## 1. Active nonpivot left links cannot cross the two lobes -/

theorem reflectedBentGuardGraftActiveNonpivotLeftTerminal_pair_same_side_at_cutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (hactive : reflectedBentPatternActiveLinkB linked.1 = true)
    (hnonpivot : linked.1 ≠ reflectedBentSwitchPivot)
    (terminal : SlabLinkPhysicalStrandTerminal D.cutoff 5
      (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
      (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff
        D hcutoff hextent state linked)
      (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff_mem
        D hcutoff hextent state linked)) :
    let partner := slabLinkPhysicalStrandPartner D.cutoff 5
      (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
      (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff
        D hcutoff hextent state linked)
      (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff_mem
        D hcutoff hextent state linked) terminal
    let sourceFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence D.cutoff 5
        (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
        (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff
          D hcutoff hextent state linked)
        (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff_mem
          D hcutoff hextent state linked) terminal).faceId
    let targetFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence D.cutoff 5
        (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
        (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff
          D hcutoff hextent state linked)
        (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff_mem
          D hcutoff hextent state linked) partner).faceId
    (sourceFace ∈ reflectedBentNearSurface ∧
      targetFace ∈ reflectedBentNearSurface) ∨
    (sourceFace ∈ reflectedBentFarSurface ∧
      targetFace ∈ reflectedBentFarSurface) := by
  dsimp only
  let auxiliary := reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff
    D hcutoff hextent state linked
  let auxiliary_mem :=
    reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff_mem
      D hcutoff hextent state linked
  let partner := slabLinkPhysicalStrandPartner D.cutoff 5
    (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
    auxiliary auxiliary_mem terminal
  let sourceOccurrence := slabLinkPhysicalTerminalOccurrence D.cutoff 5
    (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
    auxiliary auxiliary_mem terminal
  let targetOccurrence := slabLinkPhysicalTerminalOccurrence D.cutoff 5
    (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
    auxiliary auxiliary_mem partner
  have hsourcePositive :
      0 < reflectedBentSwitchLeftPhysical sourceOccurrence.faceId := by
    have hslot := sourceOccurrence.slot.isLt
    change sourceOccurrence.slot.val <
      reflectedBentGuardGraftLeftPhysical D hextent state
        sourceOccurrence.faceId at hslot
    have heq := (reflectedBentGuardGraft_eq_pattern_on_active_link
      D hextent state linked.2 hactive sourceOccurrence.faceId
      sourceOccurrence.faceId_mem_incident).1
    rw [heq] at hslot
    omega
  have htargetPositive :
      0 < reflectedBentSwitchLeftPhysical targetOccurrence.faceId := by
    have hslot := targetOccurrence.slot.isLt
    change targetOccurrence.slot.val <
      reflectedBentGuardGraftLeftPhysical D hextent state
        targetOccurrence.faceId at hslot
    have heq := (reflectedBentGuardGraft_eq_pattern_on_active_link
      D hextent state linked.2 hactive targetOccurrence.faceId
      targetOccurrence.faceId_mem_incident).1
    rw [heq] at hslot
    omega
  have hsourceSupport := reflectedBentSwitchFace_mem_of_positive
    sourceOccurrence.faceId_physical hsourcePositive
  have htargetSupport := reflectedBentSwitchFace_mem_of_positive
    targetOccurrence.faceId_physical htargetPositive
  have hsourceLink : linked.1 ∈
      edgesOf (slabPlaquetteAt 5 sourceOccurrence.faceId) :=
    reflectedBentSlabPlaquetteAt_edge_of_mem_incident
      sourceOccurrence.faceId_mem_incident
  have htargetLink : linked.1 ∈
      edgesOf (slabPlaquetteAt 5 targetOccurrence.faceId) :=
    reflectedBentSlabPlaquetteAt_edge_of_mem_incident
      targetOccurrence.faceId_mem_incident
  rcases List.mem_append.mp hsourceSupport with hsourceNear | hsourceFar
  · rcases List.mem_append.mp htargetSupport with htargetNear | htargetFar
    · exact Or.inl ⟨hsourceNear, htargetNear⟩
    · exact False.elim (hnonpivot
        (reflectedBent_crossSharedLink_eq_pivot
          hsourceNear htargetFar hsourceLink htargetLink))
  · rcases List.mem_append.mp htargetSupport with htargetNear | htargetFar
    · exact False.elim (hnonpivot
        (reflectedBent_crossSharedLink_eq_pivot
          htargetNear hsourceFar htargetLink hsourceLink))
    · exact Or.inr ⟨hsourceFar, htargetFar⟩

/-! ## 2. Every ambient local terminal preserves the face color -/

theorem reflectedBentGuardGraftRealizedLeftTerminal_color_eq_at_cutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (terminal : SlabLinkPhysicalStrandTerminal D.cutoff 5
      (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
      (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff
        D hcutoff hextent state linked)
      (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff_mem
        D hcutoff hextent state linked)) :
    let partner := slabLinkPhysicalStrandPartner D.cutoff 5
      (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
      (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff
        D hcutoff hextent state linked)
      (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff_mem
        D hcutoff hextent state linked) terminal
    reflectedBentGuardTargetFaceColorB
      (slabLinkPhysicalTerminalOccurrence D.cutoff 5
        (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
        (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff
          D hcutoff hextent state linked)
        (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff_mem
          D hcutoff hextent state linked) terminal).faceId =
    reflectedBentGuardTargetFaceColorB
      (slabLinkPhysicalTerminalOccurrence D.cutoff 5
        (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
        (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff
          D hcutoff hextent state linked)
        (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff_mem
          D hcutoff hextent state linked) partner).faceId := by
  dsimp only
  let auxiliary := reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff
    D hcutoff hextent state linked
  let auxiliary_mem :=
    reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff_mem
      D hcutoff hextent state linked
  let partner := slabLinkPhysicalStrandPartner D.cutoff 5
    (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
    auxiliary auxiliary_mem terminal
  let sourceOccurrence := slabLinkPhysicalTerminalOccurrence D.cutoff 5
    (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
    auxiliary auxiliary_mem terminal
  let targetOccurrence := slabLinkPhysicalTerminalOccurrence D.cutoff 5
    (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
    auxiliary auxiliary_mem partner
  by_cases hactive : reflectedBentPatternActiveLinkB linked.1 = true
  · by_cases hpivot : linked.1 = reflectedBentSwitchPivot
    · cases linked with
      | mk link hlink =>
          dsimp at hpivot
          subst link
          exact reflectedBentGuardTargetFaceColor_eq_of_same_side
            (reflectedBentGuardGraftRealizedPivotTerminal_pair_same_side_at_cutoff
              D hcutoff hextent state terminal)
    · exact reflectedBentGuardTargetFaceColor_eq_of_same_side
        (reflectedBentGuardGraftActiveNonpivotLeftTerminal_pair_same_side_at_cutoff
          D hcutoff hextent state linked hactive hpivot terminal)
  · have hinactive : reflectedBentPatternActiveLinkB linked.1 = false :=
      Bool.eq_false_iff.mpr hactive
    have hsourceNotPattern :
        sourceOccurrence.faceId ∉ reflectedBentPatternFaceIds :=
      (reflectedBentPatternActiveLinkB_eq_false_iff linked.1).mp
        hinactive sourceOccurrence.faceId
        sourceOccurrence.faceId_mem_incident
    have htargetNotPattern :
        targetOccurrence.faceId ∉ reflectedBentPatternFaceIds :=
      (reflectedBentPatternActiveLinkB_eq_false_iff linked.1).mp
        hinactive targetOccurrence.faceId
        targetOccurrence.faceId_mem_incident
    have hsourceNotNear :
        slabPlaquetteAt 5 sourceOccurrence.faceId ∉
          reflectedBentNearSurface := by
      intro hnear
      exact hsourceNotPattern
        (reflectedBentGuardFaceId_mem_pattern_of_near
          sourceOccurrence.faceId_physical hnear)
    have htargetNotNear :
        slabPlaquetteAt 5 targetOccurrence.faceId ∉
          reflectedBentNearSurface := by
      intro hnear
      exact htargetNotPattern
        (reflectedBentGuardFaceId_mem_pattern_of_near
          targetOccurrence.faceId_physical hnear)
    have hsourceColor :
        reflectedBentGuardTargetFaceColorB sourceOccurrence.faceId = false :=
      decide_eq_false hsourceNotNear
    have htargetColor :
        reflectedBentGuardTargetFaceColorB targetOccurrence.faceId = false :=
      decide_eq_false htargetNotNear
    exact hsourceColor.trans htargetColor.symm

theorem reflectedBentGuardGraftRealizedRightTerminal_color_eq_at_cutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (terminal : SlabLinkPhysicalStrandTerminal D.cutoff 5
      (reflectedBentGuardGraftRightPhysical D hextent state) linked.1
      (reflectedBentGuardGraftRealizedRightAuxiliaryAtCutoff
        D hcutoff hextent state linked)
      (reflectedBentGuardGraftRealizedRightAuxiliaryAtCutoff_mem
        D hcutoff hextent state linked)) :
    let partner := slabLinkPhysicalStrandPartner D.cutoff 5
      (reflectedBentGuardGraftRightPhysical D hextent state) linked.1
      (reflectedBentGuardGraftRealizedRightAuxiliaryAtCutoff
        D hcutoff hextent state linked)
      (reflectedBentGuardGraftRealizedRightAuxiliaryAtCutoff_mem
        D hcutoff hextent state linked) terminal
    reflectedBentGuardTargetFaceColorB
      (slabLinkPhysicalTerminalOccurrence D.cutoff 5
        (reflectedBentGuardGraftRightPhysical D hextent state) linked.1
        (reflectedBentGuardGraftRealizedRightAuxiliaryAtCutoff
          D hcutoff hextent state linked)
        (reflectedBentGuardGraftRealizedRightAuxiliaryAtCutoff_mem
          D hcutoff hextent state linked) terminal).faceId =
    reflectedBentGuardTargetFaceColorB
      (slabLinkPhysicalTerminalOccurrence D.cutoff 5
        (reflectedBentGuardGraftRightPhysical D hextent state) linked.1
        (reflectedBentGuardGraftRealizedRightAuxiliaryAtCutoff
          D hcutoff hextent state linked)
        (reflectedBentGuardGraftRealizedRightAuxiliaryAtCutoff_mem
          D hcutoff hextent state linked) partner).faceId := by
  dsimp only
  let auxiliary := reflectedBentGuardGraftRealizedRightAuxiliaryAtCutoff
    D hcutoff hextent state linked
  let auxiliary_mem :=
    reflectedBentGuardGraftRealizedRightAuxiliaryAtCutoff_mem
      D hcutoff hextent state linked
  let partner := slabLinkPhysicalStrandPartner D.cutoff 5
    (reflectedBentGuardGraftRightPhysical D hextent state) linked.1
    auxiliary auxiliary_mem terminal
  let sourceOccurrence := slabLinkPhysicalTerminalOccurrence D.cutoff 5
    (reflectedBentGuardGraftRightPhysical D hextent state) linked.1
    auxiliary auxiliary_mem terminal
  let targetOccurrence := slabLinkPhysicalTerminalOccurrence D.cutoff 5
    (reflectedBentGuardGraftRightPhysical D hextent state) linked.1
    auxiliary auxiliary_mem partner
  by_cases hactive : reflectedBentPatternActiveLinkB linked.1 = true
  · have hslot := sourceOccurrence.slot.isLt
    change sourceOccurrence.slot.val <
      reflectedBentGuardGraftRightPhysical D hextent state
        sourceOccurrence.faceId at hslot
    have heq := (reflectedBentGuardGraft_eq_pattern_on_active_link
      D hextent state linked.2 hactive sourceOccurrence.faceId
      sourceOccurrence.faceId_mem_incident).2
    have hzero : reflectedBentGuardGraftRightPhysical D hextent state
        sourceOccurrence.faceId = 0 :=
      heq.trans (reflectedBentSwitchRightPhysical_eq_zero
        sourceOccurrence.faceId)
    rw [hzero] at hslot
    exact False.elim (Nat.not_lt_zero sourceOccurrence.slot.val hslot)
  · have hinactive : reflectedBentPatternActiveLinkB linked.1 = false :=
      Bool.eq_false_iff.mpr hactive
    have hsourceNotPattern :
        sourceOccurrence.faceId ∉ reflectedBentPatternFaceIds :=
      (reflectedBentPatternActiveLinkB_eq_false_iff linked.1).mp
        hinactive sourceOccurrence.faceId
        sourceOccurrence.faceId_mem_incident
    have htargetNotPattern :
        targetOccurrence.faceId ∉ reflectedBentPatternFaceIds :=
      (reflectedBentPatternActiveLinkB_eq_false_iff linked.1).mp
        hinactive targetOccurrence.faceId
        targetOccurrence.faceId_mem_incident
    have hsourceNotNear :
        slabPlaquetteAt 5 sourceOccurrence.faceId ∉
          reflectedBentNearSurface := by
      intro hnear
      exact hsourceNotPattern
        (reflectedBentGuardFaceId_mem_pattern_of_near
          sourceOccurrence.faceId_physical hnear)
    have htargetNotNear :
        slabPlaquetteAt 5 targetOccurrence.faceId ∉
          reflectedBentNearSurface := by
      intro hnear
      exact htargetNotPattern
        (reflectedBentGuardFaceId_mem_pattern_of_near
          targetOccurrence.faceId_physical hnear)
    have hsourceColor :
        reflectedBentGuardTargetFaceColorB sourceOccurrence.faceId = false :=
      decide_eq_false hsourceNotNear
    have htargetColor :
        reflectedBentGuardTargetFaceColorB targetOccurrence.faceId = false :=
      decide_eq_false htargetNotNear
    exact hsourceColor.trans htargetColor.symm

/-! ## 3. Assemble the ambient projected graph -/

def reflectedBentGuardGraftRealizedLeftProjectedFaceEdgesAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    List SlabProjectedFaceEdge :=
  (boundaryCompleteSlabLinks 5).attach.flatMap fun linked =>
    slabProjectedFaceEdges
      (slabLinkFaceStrandEdges D.cutoff 5
        (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
        (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff
          D hcutoff hextent state linked)
        (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff_mem
          D hcutoff hextent state linked))

def reflectedBentGuardGraftRealizedRightProjectedFaceEdgesAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    List SlabProjectedFaceEdge :=
  (boundaryCompleteSlabLinks 5).attach.flatMap fun linked =>
    slabProjectedFaceEdges
      (slabLinkFaceStrandEdges D.cutoff 5
        (reflectedBentGuardGraftRightPhysical D hextent state) linked.1
        (reflectedBentGuardGraftRealizedRightAuxiliaryAtCutoff
          D hcutoff hextent state linked)
        (reflectedBentGuardGraftRealizedRightAuxiliaryAtCutoff_mem
          D hcutoff hextent state linked))

def reflectedBentGuardGraftPositiveTargetProjectedFaceEdgesAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    List SlabProjectedFaceEdge :=
  reflectedBentGuardGraftRealizedLeftProjectedFaceEdgesAtCutoff
      D hcutoff hextent state ++
    reflectedBentGuardGraftRealizedRightProjectedFaceEdgesAtCutoff
      D hcutoff hextent state

theorem reflectedBentGuardGraftRealizedLeftProjectedFaceEdge_color_eq_at_cutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (projected : SlabProjectedFaceEdge)
    (hprojected : projected ∈
      reflectedBentGuardGraftRealizedLeftProjectedFaceEdgesAtCutoff
        D hcutoff hextent state) :
    reflectedBentGuardTargetFaceColorB projected.source =
      reflectedBentGuardTargetFaceColorB projected.target := by
  unfold reflectedBentGuardGraftRealizedLeftProjectedFaceEdgesAtCutoff
    at hprojected
  obtain ⟨linked, _, hlocal⟩ := List.mem_flatMap.mp hprojected
  unfold slabProjectedFaceEdges slabLinkFaceStrandEdges at hlocal
  obtain ⟨edge, hedge, rfl⟩ := List.mem_map.mp hlocal
  obtain ⟨terminal, _, rfl⟩ := List.mem_map.mp hedge
  simpa only [slabLinkFaceStrandEdgeOfTerminal,
    slabLinkPhysicalTerminalFaceStrandCopy,
    slabLinkFaceStrandOccurrenceToCopy] using
      reflectedBentGuardGraftRealizedLeftTerminal_color_eq_at_cutoff
        D hcutoff hextent state linked terminal

theorem reflectedBentGuardGraftRealizedRightProjectedFaceEdge_color_eq_at_cutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (projected : SlabProjectedFaceEdge)
    (hprojected : projected ∈
      reflectedBentGuardGraftRealizedRightProjectedFaceEdgesAtCutoff
        D hcutoff hextent state) :
    reflectedBentGuardTargetFaceColorB projected.source =
      reflectedBentGuardTargetFaceColorB projected.target := by
  unfold reflectedBentGuardGraftRealizedRightProjectedFaceEdgesAtCutoff
    at hprojected
  obtain ⟨linked, _, hlocal⟩ := List.mem_flatMap.mp hprojected
  unfold slabProjectedFaceEdges slabLinkFaceStrandEdges at hlocal
  obtain ⟨edge, hedge, rfl⟩ := List.mem_map.mp hlocal
  obtain ⟨terminal, _, rfl⟩ := List.mem_map.mp hedge
  simpa only [slabLinkFaceStrandEdgeOfTerminal,
    slabLinkPhysicalTerminalFaceStrandCopy,
    slabLinkFaceStrandOccurrenceToCopy] using
      reflectedBentGuardGraftRealizedRightTerminal_color_eq_at_cutoff
        D hcutoff hextent state linked terminal

theorem reflectedBentGuardGraftPositiveTargetProjectedFaceEdge_color_eq_at_cutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (projected : SlabProjectedFaceEdge)
    (hprojected : projected ∈
      reflectedBentGuardGraftPositiveTargetProjectedFaceEdgesAtCutoff
        D hcutoff hextent state) :
    reflectedBentGuardTargetFaceColorB projected.source =
      reflectedBentGuardTargetFaceColorB projected.target := by
  rcases List.mem_append.mp hprojected with hleft | hright
  · exact
      reflectedBentGuardGraftRealizedLeftProjectedFaceEdge_color_eq_at_cutoff
        D hcutoff hextent state projected hleft
  · exact
      reflectedBentGuardGraftRealizedRightProjectedFaceEdge_color_eq_at_cutoff
        D hcutoff hextent state projected hright

#print axioms reflectedBentGuardGraftActiveNonpivotLeftTerminal_pair_same_side_at_cutoff
#print axioms reflectedBentGuardGraftRealizedLeftTerminal_color_eq_at_cutoff
#print axioms reflectedBentGuardGraftRealizedRightTerminal_color_eq_at_cutoff
#print axioms reflectedBentGuardGraftPositiveTargetProjectedFaceEdge_color_eq_at_cutoff

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetEdgesCutoffPersistence
