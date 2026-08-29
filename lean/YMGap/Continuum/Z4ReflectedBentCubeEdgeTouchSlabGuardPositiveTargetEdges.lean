/-
# Color-preserving edges of the realized positive guarded target

Project the two realized target assignments to ordinary physical-face edges.
Inactive links cannot touch the inserted reflected support.  Active left links
preserve the near/far lobe by the unique-pivot geometry, with the pivot handled
by its exact realized edge list.  Active right links have vacuum physical word
and therefore no physical strand terminal.

Constructive contract: finite terminal lists, literal incidence, and Boolean
color transport only; no `Classical`, choice, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPivotEdges

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetEdges

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
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPivotEdges
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPivotPairing
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealization
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabNonpivotPairing
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile

/-! ## 1. The face color and its support interface -/

def reflectedBentGuardTargetFaceColorB (faceId : Nat) : Bool :=
  decide (slabPlaquetteAt 5 faceId ∈ reflectedBentNearSurface)

theorem reflectedBentGuardFaceId_mem_pattern_of_near
    {faceId : Nat} (hphysical : faceId ∈ slabPhysicalFaceEdges 5)
    (hnear : slabPlaquetteAt 5 faceId ∈ reflectedBentNearSurface) :
    faceId ∈ reflectedBentPatternFaceIds := by
  apply (mem_reflectedBentPatternFaceIds_iff hphysical).mpr
  have hsupport : slabPlaquetteAt 5 faceId ∈
      YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile.reflectedBentSwitchSurface :=
    List.mem_append.mpr (Or.inl hnear)
  change 0 < slabBinarySupportLabelling 5
    YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile.reflectedBentSwitchSurface
    faceId
  rw [slabBinarySupportLabelling_eq_indicator hphysical]
  rw [if_pos hsupport]
  decide

theorem reflectedBentGuardFarFace_not_near
    {face : Z4Plaq} (hfar : face ∈ reflectedBentFarSurface) :
    face ∉ reflectedBentNearSurface := by
  intro hnear
  have hcross := (List.nodup_append.mp
    YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchCutCarrier.reflectedBentSwitchSurface_nodup).2.2
  exact hcross face hnear face hfar rfl

theorem reflectedBentGuardTargetFaceColor_eq_of_same_side
    {sourceFaceId targetFaceId : Nat}
    (hside :
      (slabPlaquetteAt 5 sourceFaceId ∈ reflectedBentNearSurface ∧
        slabPlaquetteAt 5 targetFaceId ∈ reflectedBentNearSurface) ∨
      (slabPlaquetteAt 5 sourceFaceId ∈ reflectedBentFarSurface ∧
        slabPlaquetteAt 5 targetFaceId ∈ reflectedBentFarSurface)) :
    reflectedBentGuardTargetFaceColorB sourceFaceId =
      reflectedBentGuardTargetFaceColorB targetFaceId := by
  rcases hside with hnear | hfar
  · simp [reflectedBentGuardTargetFaceColorB, hnear.1, hnear.2]
  · have hs := reflectedBentGuardFarFace_not_near hfar.1
    have ht := reflectedBentGuardFarFace_not_near hfar.2
    simp [reflectedBentGuardTargetFaceColorB, hs, ht]

/-! ## 2. Active left nonpivot links preserve the lobe -/

theorem reflectedBentGuardGraftActiveNonpivotLeftTerminal_pair_same_side
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (hactive : reflectedBentPatternActiveLinkB linked.1 = true)
    (hnonpivot : linked.1 ≠ reflectedBentSwitchPivot)
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
      (reflectedBentGuardGraftRealizedLeftAuxiliary
        D hcutoff hextent state linked)
      (reflectedBentGuardGraftRealizedLeftAuxiliary_mem
        D hcutoff hextent state linked)) :
    let partner := slabLinkPhysicalStrandPartner 1 5
      (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
      (reflectedBentGuardGraftRealizedLeftAuxiliary
        D hcutoff hextent state linked)
      (reflectedBentGuardGraftRealizedLeftAuxiliary_mem
        D hcutoff hextent state linked) terminal
    let sourceFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
        (reflectedBentGuardGraftRealizedLeftAuxiliary
          D hcutoff hextent state linked)
        (reflectedBentGuardGraftRealizedLeftAuxiliary_mem
          D hcutoff hextent state linked) terminal).faceId
    let targetFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence 1 5
        (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
        (reflectedBentGuardGraftRealizedLeftAuxiliary
          D hcutoff hextent state linked)
        (reflectedBentGuardGraftRealizedLeftAuxiliary_mem
          D hcutoff hextent state linked) partner).faceId
    (sourceFace ∈ reflectedBentNearSurface ∧
      targetFace ∈ reflectedBentNearSurface) ∨
    (sourceFace ∈ reflectedBentFarSurface ∧
      targetFace ∈ reflectedBentFarSurface) := by
  dsimp only
  let auxiliary := reflectedBentGuardGraftRealizedLeftAuxiliary
    D hcutoff hextent state linked
  let auxiliary_mem := reflectedBentGuardGraftRealizedLeftAuxiliary_mem
    D hcutoff hextent state linked
  let partner := slabLinkPhysicalStrandPartner 1 5
    (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
    auxiliary auxiliary_mem terminal
  let sourceOccurrence := slabLinkPhysicalTerminalOccurrence 1 5
    (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
    auxiliary auxiliary_mem terminal
  let targetOccurrence := slabLinkPhysicalTerminalOccurrence 1 5
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

/-! ## 3. Every realized local terminal preserves the face color -/

theorem reflectedBentGuardGraftRealizedLeftTerminal_color_eq
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
      (reflectedBentGuardGraftRealizedLeftAuxiliary
        D hcutoff hextent state linked)
      (reflectedBentGuardGraftRealizedLeftAuxiliary_mem
        D hcutoff hextent state linked)) :
    let partner := slabLinkPhysicalStrandPartner 1 5
      (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
      (reflectedBentGuardGraftRealizedLeftAuxiliary
        D hcutoff hextent state linked)
      (reflectedBentGuardGraftRealizedLeftAuxiliary_mem
        D hcutoff hextent state linked) terminal
    reflectedBentGuardTargetFaceColorB
      (slabLinkPhysicalTerminalOccurrence 1 5
        (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
        (reflectedBentGuardGraftRealizedLeftAuxiliary
          D hcutoff hextent state linked)
        (reflectedBentGuardGraftRealizedLeftAuxiliary_mem
          D hcutoff hextent state linked) terminal).faceId =
    reflectedBentGuardTargetFaceColorB
      (slabLinkPhysicalTerminalOccurrence 1 5
        (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
        (reflectedBentGuardGraftRealizedLeftAuxiliary
          D hcutoff hextent state linked)
        (reflectedBentGuardGraftRealizedLeftAuxiliary_mem
          D hcutoff hextent state linked) partner).faceId := by
  dsimp only
  let auxiliary := reflectedBentGuardGraftRealizedLeftAuxiliary
    D hcutoff hextent state linked
  let auxiliary_mem := reflectedBentGuardGraftRealizedLeftAuxiliary_mem
    D hcutoff hextent state linked
  let partner := slabLinkPhysicalStrandPartner 1 5
    (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
    auxiliary auxiliary_mem terminal
  let sourceOccurrence := slabLinkPhysicalTerminalOccurrence 1 5
    (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
    auxiliary auxiliary_mem terminal
  let targetOccurrence := slabLinkPhysicalTerminalOccurrence 1 5
    (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
    auxiliary auxiliary_mem partner
  by_cases hactive : reflectedBentPatternActiveLinkB linked.1 = true
  · by_cases hpivot : linked.1 = reflectedBentSwitchPivot
    · cases linked with
      | mk link hlink =>
          dsimp at hpivot
          subst link
          exact reflectedBentGuardTargetFaceColor_eq_of_same_side
            (reflectedBentGuardGraftRealizedPivotTerminal_pair_same_side
              D hcutoff hextent state terminal)
    · exact reflectedBentGuardTargetFaceColor_eq_of_same_side
        (reflectedBentGuardGraftActiveNonpivotLeftTerminal_pair_same_side
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

theorem reflectedBentGuardGraftRealizedRightTerminal_color_eq
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (terminal : SlabLinkPhysicalStrandTerminal 1 5
      (reflectedBentGuardGraftRightPhysical D hextent state) linked.1
      (reflectedBentGuardGraftRealizedRightAuxiliary
        D hcutoff hextent state linked)
      (reflectedBentGuardGraftRealizedRightAuxiliary_mem
        D hcutoff hextent state linked)) :
    let partner := slabLinkPhysicalStrandPartner 1 5
      (reflectedBentGuardGraftRightPhysical D hextent state) linked.1
      (reflectedBentGuardGraftRealizedRightAuxiliary
        D hcutoff hextent state linked)
      (reflectedBentGuardGraftRealizedRightAuxiliary_mem
        D hcutoff hextent state linked) terminal
    reflectedBentGuardTargetFaceColorB
      (slabLinkPhysicalTerminalOccurrence 1 5
        (reflectedBentGuardGraftRightPhysical D hextent state) linked.1
        (reflectedBentGuardGraftRealizedRightAuxiliary
          D hcutoff hextent state linked)
        (reflectedBentGuardGraftRealizedRightAuxiliary_mem
          D hcutoff hextent state linked) terminal).faceId =
    reflectedBentGuardTargetFaceColorB
      (slabLinkPhysicalTerminalOccurrence 1 5
        (reflectedBentGuardGraftRightPhysical D hextent state) linked.1
        (reflectedBentGuardGraftRealizedRightAuxiliary
          D hcutoff hextent state linked)
        (reflectedBentGuardGraftRealizedRightAuxiliary_mem
          D hcutoff hextent state linked) partner).faceId := by
  dsimp only
  let auxiliary := reflectedBentGuardGraftRealizedRightAuxiliary
    D hcutoff hextent state linked
  let auxiliary_mem := reflectedBentGuardGraftRealizedRightAuxiliary_mem
    D hcutoff hextent state linked
  let partner := slabLinkPhysicalStrandPartner 1 5
    (reflectedBentGuardGraftRightPhysical D hextent state) linked.1
    auxiliary auxiliary_mem terminal
  let sourceOccurrence := slabLinkPhysicalTerminalOccurrence 1 5
    (reflectedBentGuardGraftRightPhysical D hextent state) linked.1
    auxiliary auxiliary_mem terminal
  let targetOccurrence := slabLinkPhysicalTerminalOccurrence 1 5
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

/-! ## 4. Assemble both replicas as one ordinary projected graph -/

def reflectedBentGuardGraftRealizedLeftFaceStrandEdgesAt
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    List (SlabFaceStrandEdge
      (reflectedBentGuardGraftLeftPhysical D hextent state)) :=
  slabLinkFaceStrandEdges 1 5
    (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
    (reflectedBentGuardGraftRealizedLeftAuxiliary
      D hcutoff hextent state linked)
    (reflectedBentGuardGraftRealizedLeftAuxiliary_mem
      D hcutoff hextent state linked)

def reflectedBentGuardGraftRealizedRightFaceStrandEdgesAt
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    List (SlabFaceStrandEdge
      (reflectedBentGuardGraftRightPhysical D hextent state)) :=
  slabLinkFaceStrandEdges 1 5
    (reflectedBentGuardGraftRightPhysical D hextent state) linked.1
    (reflectedBentGuardGraftRealizedRightAuxiliary
      D hcutoff hextent state linked)
    (reflectedBentGuardGraftRealizedRightAuxiliary_mem
      D hcutoff hextent state linked)

theorem reflectedBentGuardGraftRealizedLeftFaceStrandEdgeAt_color_eq
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (edge : SlabFaceStrandEdge
      (reflectedBentGuardGraftLeftPhysical D hextent state))
    (hedge : edge ∈ reflectedBentGuardGraftRealizedLeftFaceStrandEdgesAt
      D hcutoff hextent state linked) :
    reflectedBentGuardTargetFaceColorB edge.source.faceId =
      reflectedBentGuardTargetFaceColorB edge.target.faceId := by
  unfold reflectedBentGuardGraftRealizedLeftFaceStrandEdgesAt
    slabLinkFaceStrandEdges at hedge
  obtain ⟨terminal, _, rfl⟩ := List.mem_map.mp hedge
  simpa only [slabLinkFaceStrandEdgeOfTerminal,
    slabLinkPhysicalTerminalFaceStrandCopy,
    slabLinkFaceStrandOccurrenceToCopy] using
      reflectedBentGuardGraftRealizedLeftTerminal_color_eq
        D hcutoff hextent state linked terminal

theorem reflectedBentGuardGraftRealizedRightFaceStrandEdgeAt_color_eq
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (edge : SlabFaceStrandEdge
      (reflectedBentGuardGraftRightPhysical D hextent state))
    (hedge : edge ∈ reflectedBentGuardGraftRealizedRightFaceStrandEdgesAt
      D hcutoff hextent state linked) :
    reflectedBentGuardTargetFaceColorB edge.source.faceId =
      reflectedBentGuardTargetFaceColorB edge.target.faceId := by
  unfold reflectedBentGuardGraftRealizedRightFaceStrandEdgesAt
    slabLinkFaceStrandEdges at hedge
  obtain ⟨terminal, _, rfl⟩ := List.mem_map.mp hedge
  simpa only [slabLinkFaceStrandEdgeOfTerminal,
    slabLinkPhysicalTerminalFaceStrandCopy,
    slabLinkFaceStrandOccurrenceToCopy] using
      reflectedBentGuardGraftRealizedRightTerminal_color_eq
        D hcutoff hextent state linked terminal

def reflectedBentGuardGraftRealizedLeftProjectedFaceEdgesAt
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    List SlabProjectedFaceEdge :=
  slabProjectedFaceEdges
    (reflectedBentGuardGraftRealizedLeftFaceStrandEdgesAt
      D hcutoff hextent state linked)

def reflectedBentGuardGraftRealizedRightProjectedFaceEdgesAt
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    List SlabProjectedFaceEdge :=
  slabProjectedFaceEdges
    (reflectedBentGuardGraftRealizedRightFaceStrandEdgesAt
      D hcutoff hextent state linked)

def reflectedBentGuardGraftRealizedLeftProjectedFaceEdges
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    List SlabProjectedFaceEdge :=
  (boundaryCompleteSlabLinks 5).attach.flatMap
    (reflectedBentGuardGraftRealizedLeftProjectedFaceEdgesAt
      D hcutoff hextent state)

def reflectedBentGuardGraftRealizedRightProjectedFaceEdges
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    List SlabProjectedFaceEdge :=
  (boundaryCompleteSlabLinks 5).attach.flatMap
    (reflectedBentGuardGraftRealizedRightProjectedFaceEdgesAt
      D hcutoff hextent state)

def reflectedBentGuardGraftPositiveTargetProjectedFaceEdges
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    List SlabProjectedFaceEdge :=
  reflectedBentGuardGraftRealizedLeftProjectedFaceEdges
      D hcutoff hextent state ++
    reflectedBentGuardGraftRealizedRightProjectedFaceEdges
      D hcutoff hextent state

theorem reflectedBentGuardGraftRealizedLeftProjectedFaceEdge_color_eq
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (projected : SlabProjectedFaceEdge)
    (hprojected : projected ∈
      reflectedBentGuardGraftRealizedLeftProjectedFaceEdges
        D hcutoff hextent state) :
    reflectedBentGuardTargetFaceColorB projected.source =
      reflectedBentGuardTargetFaceColorB projected.target := by
  unfold reflectedBentGuardGraftRealizedLeftProjectedFaceEdges at hprojected
  obtain ⟨linked, _, hlocal⟩ := List.mem_flatMap.mp hprojected
  unfold reflectedBentGuardGraftRealizedLeftProjectedFaceEdgesAt
    slabProjectedFaceEdges at hlocal
  obtain ⟨edge, hedge, rfl⟩ := List.mem_map.mp hlocal
  exact reflectedBentGuardGraftRealizedLeftFaceStrandEdgeAt_color_eq
    D hcutoff hextent state linked edge hedge

theorem reflectedBentGuardGraftRealizedRightProjectedFaceEdge_color_eq
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (projected : SlabProjectedFaceEdge)
    (hprojected : projected ∈
      reflectedBentGuardGraftRealizedRightProjectedFaceEdges
        D hcutoff hextent state) :
    reflectedBentGuardTargetFaceColorB projected.source =
      reflectedBentGuardTargetFaceColorB projected.target := by
  unfold reflectedBentGuardGraftRealizedRightProjectedFaceEdges at hprojected
  obtain ⟨linked, _, hlocal⟩ := List.mem_flatMap.mp hprojected
  unfold reflectedBentGuardGraftRealizedRightProjectedFaceEdgesAt
    slabProjectedFaceEdges at hlocal
  obtain ⟨edge, hedge, rfl⟩ := List.mem_map.mp hlocal
  exact reflectedBentGuardGraftRealizedRightFaceStrandEdgeAt_color_eq
    D hcutoff hextent state linked edge hedge

theorem reflectedBentGuardGraftPositiveTargetProjectedFaceEdge_color_eq
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (projected : SlabProjectedFaceEdge)
    (hprojected : projected ∈
      reflectedBentGuardGraftPositiveTargetProjectedFaceEdges
        D hcutoff hextent state) :
    reflectedBentGuardTargetFaceColorB projected.source =
      reflectedBentGuardTargetFaceColorB projected.target := by
  rcases List.mem_append.mp hprojected with hleft | hright
  · exact reflectedBentGuardGraftRealizedLeftProjectedFaceEdge_color_eq
      D hcutoff hextent state projected hleft
  · exact reflectedBentGuardGraftRealizedRightProjectedFaceEdge_color_eq
      D hcutoff hextent state projected hright

#print axioms reflectedBentGuardFaceId_mem_pattern_of_near
#print axioms reflectedBentGuardGraftActiveNonpivotLeftTerminal_pair_same_side
#print axioms reflectedBentGuardGraftRealizedLeftTerminal_color_eq
#print axioms reflectedBentGuardGraftRealizedRightTerminal_color_eq
#print axioms reflectedBentGuardGraftPositiveTargetProjectedFaceEdge_color_eq

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetEdges
