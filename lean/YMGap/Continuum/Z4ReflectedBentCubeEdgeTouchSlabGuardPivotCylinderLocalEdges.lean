/-
# Every locally realized pivot-cylinder column preserves the marked-side color

The pivot cylinder fixes only one recoupling coordinate.  Consequently its
geometric proof may not reuse a distinguished auxiliary away from that pivot.
This module isolates the exact local invariant: every accepted auxiliary at a
nonpivot link preserves the near/far side, while the pinned pivot auxiliary is
the already classified component-preserving carrier.  The right replica is
independent of the target because its active physical word is empty.

Constructive contract: accepted terminal witnesses, literal incidence, and
the pinned pivot equality only; no `Classical`, choice, `native_decide`,
`sorry`, new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderRealization
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetEdgesCutoffPersistence

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderLocalEdges

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchCutCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuard
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLinkWords
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderRealization
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTarget
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetEdges
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetEdgesCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPivotEdgesCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealizationCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardTargetAssignmentRealizationCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabNonpivotPairing
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile

/-! ## 1. Nonpivot geometry is independent of the recoupling column -/

theorem reflectedBentGuardGraftActiveNonpivotLeftTerminalForAuxiliary_pair_same_side_at_cutoff
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (hactive : reflectedBentPatternActiveLinkB linked.1 = true)
    (hnonpivot : linked.1 ≠ reflectedBentSwitchPivot)
    (auxiliary : SlabLabelling)
    (auxiliary_mem : auxiliary ∈
      slabLinkFusionWitnesses D.cutoff 5
        (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1)
    (terminal : SlabLinkPhysicalStrandTerminal D.cutoff 5
      (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
      auxiliary auxiliary_mem) :
    let partner := slabLinkPhysicalStrandPartner D.cutoff 5
      (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
      auxiliary auxiliary_mem terminal
    let sourceFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence D.cutoff 5
        (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
        auxiliary auxiliary_mem terminal).faceId
    let targetFace := slabPlaquetteAt 5
      (slabLinkPhysicalTerminalOccurrence D.cutoff 5
        (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
        auxiliary auxiliary_mem partner).faceId
    (sourceFace ∈ reflectedBentNearSurface ∧
      targetFace ∈ reflectedBentNearSurface) ∨
    (sourceFace ∈ reflectedBentFarSurface ∧
      targetFace ∈ reflectedBentFarSurface) := by
  dsimp only
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

/-! ## 2. An arbitrary accepted auxiliary preserves color if the pivot is pinned -/

theorem reflectedBentGuardGraftLeftTerminalForAuxiliary_color_eq_at_cutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (auxiliary : SlabLabelling)
    (auxiliary_mem : auxiliary ∈
      slabLinkFusionWitnesses D.cutoff 5
        (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1)
    (hpivotAuxiliary : linked.1 = reflectedBentSwitchPivot →
      auxiliary = reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff
        D hcutoff hextent state linked)
    (terminal : SlabLinkPhysicalStrandTerminal D.cutoff 5
      (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
      auxiliary auxiliary_mem) :
    let partner := slabLinkPhysicalStrandPartner D.cutoff 5
      (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
      auxiliary auxiliary_mem terminal
    reflectedBentGuardTargetFaceColorB
      (slabLinkPhysicalTerminalOccurrence D.cutoff 5
        (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
        auxiliary auxiliary_mem terminal).faceId =
    reflectedBentGuardTargetFaceColorB
      (slabLinkPhysicalTerminalOccurrence D.cutoff 5
        (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
        auxiliary auxiliary_mem partner).faceId := by
  dsimp only
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
    · have hauxiliary := hpivotAuxiliary hpivot
      subst auxiliary
      cases linked with
      | mk link hlink =>
          dsimp at hpivot
          subst link
          exact reflectedBentGuardTargetFaceColor_eq_of_same_side
            (reflectedBentGuardGraftRealizedPivotTerminal_pair_same_side_at_cutoff
              D hcutoff hextent state terminal)
    · exact reflectedBentGuardTargetFaceColor_eq_of_same_side
        (reflectedBentGuardGraftActiveNonpivotLeftTerminalForAuxiliary_pair_same_side_at_cutoff
          D hextent state linked hactive hpivot
          auxiliary auxiliary_mem terminal)
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
        slabPlaquetteAt 5 sourceOccurrence.faceId ∉ reflectedBentNearSurface := by
      intro hnear
      exact hsourceNotPattern
        (reflectedBentGuardFaceId_mem_pattern_of_near
          sourceOccurrence.faceId_physical hnear)
    have htargetNotNear :
        slabPlaquetteAt 5 targetOccurrence.faceId ∉ reflectedBentNearSurface := by
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

theorem reflectedBentGuardGraftRightTerminalForAuxiliary_color_eq_at_cutoff
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (auxiliary : SlabLabelling)
    (auxiliary_mem : auxiliary ∈
      slabLinkFusionWitnesses D.cutoff 5
        (reflectedBentGuardGraftRightPhysical D hextent state) linked.1)
    (terminal : SlabLinkPhysicalStrandTerminal D.cutoff 5
      (reflectedBentGuardGraftRightPhysical D hextent state) linked.1
      auxiliary auxiliary_mem) :
    let partner := slabLinkPhysicalStrandPartner D.cutoff 5
      (reflectedBentGuardGraftRightPhysical D hextent state) linked.1
      auxiliary auxiliary_mem terminal
    reflectedBentGuardTargetFaceColorB
      (slabLinkPhysicalTerminalOccurrence D.cutoff 5
        (reflectedBentGuardGraftRightPhysical D hextent state) linked.1
        auxiliary auxiliary_mem terminal).faceId =
    reflectedBentGuardTargetFaceColorB
      (slabLinkPhysicalTerminalOccurrence D.cutoff 5
        (reflectedBentGuardGraftRightPhysical D hextent state) linked.1
        auxiliary auxiliary_mem partner).faceId := by
  dsimp only
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
        slabPlaquetteAt 5 sourceOccurrence.faceId ∉ reflectedBentNearSurface := by
      intro hnear
      exact hsourceNotPattern
        (reflectedBentGuardFaceId_mem_pattern_of_near
          sourceOccurrence.faceId_physical hnear)
    have htargetNotNear :
        slabPlaquetteAt 5 targetOccurrence.faceId ∉ reflectedBentNearSurface := by
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

/-! ## 3. Specialize to an arbitrary local target coordinate -/

theorem reflectedBentGuardGraftRealizedLeftTerminalForTarget_color_eq_at_cutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : (slabPhysicalPairRecouplingPackageAtLink 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      (reflectedBentGuardGraftRightPhysical D hextent state)
      linked).Target)
    (hpinned : linked.1 = reflectedBentSwitchPivot →
      target = reflectedBentGuardGraftLocalTargetAtCutoff
        D hcutoff hextent state linked)
    (terminal : SlabLinkPhysicalStrandTerminal D.cutoff 5
      (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
      (reflectedBentGuardGraftRealizedLeftAuxiliaryForTargetAtCutoff
        D hcutoff hextent state linked target)
      (reflectedBentGuardGraftRealizedLeftAuxiliaryForTargetAtCutoff_mem
        D hcutoff hextent state linked target)) :
    let partner := slabLinkPhysicalStrandPartner D.cutoff 5
      (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
      (reflectedBentGuardGraftRealizedLeftAuxiliaryForTargetAtCutoff
        D hcutoff hextent state linked target)
      (reflectedBentGuardGraftRealizedLeftAuxiliaryForTargetAtCutoff_mem
        D hcutoff hextent state linked target) terminal
    reflectedBentGuardTargetFaceColorB
      (slabLinkPhysicalTerminalOccurrence D.cutoff 5
        (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
        (reflectedBentGuardGraftRealizedLeftAuxiliaryForTargetAtCutoff
          D hcutoff hextent state linked target)
        (reflectedBentGuardGraftRealizedLeftAuxiliaryForTargetAtCutoff_mem
          D hcutoff hextent state linked target) terminal).faceId =
    reflectedBentGuardTargetFaceColorB
      (slabLinkPhysicalTerminalOccurrence D.cutoff 5
        (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
        (reflectedBentGuardGraftRealizedLeftAuxiliaryForTargetAtCutoff
          D hcutoff hextent state linked target)
        (reflectedBentGuardGraftRealizedLeftAuxiliaryForTargetAtCutoff_mem
          D hcutoff hextent state linked target) partner).faceId := by
  apply reflectedBentGuardGraftLeftTerminalForAuxiliary_color_eq_at_cutoff
    D hcutoff hextent state linked
      (reflectedBentGuardGraftRealizedLeftAuxiliaryForTargetAtCutoff
        D hcutoff hextent state linked target)
      (reflectedBentGuardGraftRealizedLeftAuxiliaryForTargetAtCutoff_mem
        D hcutoff hextent state linked target)
  intro hpivot
  have hpair :=
    reflectedBentGuardGraftLocalRealizedPairForTargetAtCutoff_eq_selected
      D hcutoff hextent state linked target (hpinned hpivot)
  exact congrArg (fun pair => pair.leftAuxiliary) hpair

theorem reflectedBentGuardGraftRealizedRightTerminalForTarget_color_eq_at_cutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : (slabPhysicalPairRecouplingPackageAtLink 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      (reflectedBentGuardGraftRightPhysical D hextent state)
      linked).Target)
    (terminal : SlabLinkPhysicalStrandTerminal D.cutoff 5
      (reflectedBentGuardGraftRightPhysical D hextent state) linked.1
      (reflectedBentGuardGraftRealizedRightAuxiliaryForTargetAtCutoff
        D hcutoff hextent state linked target)
      (reflectedBentGuardGraftRealizedRightAuxiliaryForTargetAtCutoff_mem
        D hcutoff hextent state linked target)) :
    let partner := slabLinkPhysicalStrandPartner D.cutoff 5
      (reflectedBentGuardGraftRightPhysical D hextent state) linked.1
      (reflectedBentGuardGraftRealizedRightAuxiliaryForTargetAtCutoff
        D hcutoff hextent state linked target)
      (reflectedBentGuardGraftRealizedRightAuxiliaryForTargetAtCutoff_mem
        D hcutoff hextent state linked target) terminal
    reflectedBentGuardTargetFaceColorB
      (slabLinkPhysicalTerminalOccurrence D.cutoff 5
        (reflectedBentGuardGraftRightPhysical D hextent state) linked.1
        (reflectedBentGuardGraftRealizedRightAuxiliaryForTargetAtCutoff
          D hcutoff hextent state linked target)
        (reflectedBentGuardGraftRealizedRightAuxiliaryForTargetAtCutoff_mem
          D hcutoff hextent state linked target) terminal).faceId =
    reflectedBentGuardTargetFaceColorB
      (slabLinkPhysicalTerminalOccurrence D.cutoff 5
        (reflectedBentGuardGraftRightPhysical D hextent state) linked.1
        (reflectedBentGuardGraftRealizedRightAuxiliaryForTargetAtCutoff
          D hcutoff hextent state linked target)
        (reflectedBentGuardGraftRealizedRightAuxiliaryForTargetAtCutoff_mem
          D hcutoff hextent state linked target) partner).faceId :=
  reflectedBentGuardGraftRightTerminalForAuxiliary_color_eq_at_cutoff
    D hextent state linked
      (reflectedBentGuardGraftRealizedRightAuxiliaryForTargetAtCutoff
        D hcutoff hextent state linked target)
      (reflectedBentGuardGraftRealizedRightAuxiliaryForTargetAtCutoff_mem
        D hcutoff hextent state linked target) terminal

#print axioms reflectedBentGuardGraftActiveNonpivotLeftTerminalForAuxiliary_pair_same_side_at_cutoff
#print axioms reflectedBentGuardGraftLeftTerminalForAuxiliary_color_eq_at_cutoff
#print axioms reflectedBentGuardGraftRightTerminalForAuxiliary_color_eq_at_cutoff
#print axioms reflectedBentGuardGraftRealizedLeftTerminalForTarget_color_eq_at_cutoff
#print axioms reflectedBentGuardGraftRealizedRightTerminalForTarget_color_eq_at_cutoff

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderLocalEdges
