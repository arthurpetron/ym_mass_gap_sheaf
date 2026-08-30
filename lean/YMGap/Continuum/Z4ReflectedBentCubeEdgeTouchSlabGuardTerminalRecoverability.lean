/-
# Recovering the peeled terminal from the reflected guard graft

The reflected guard graft overwrites the cleared collar by one fixed
non-abelian channel.  This does not retain the canonical peeling trace, but it
does retain the peeled terminal itself.  Outside the active links the terminal
physical and auxiliary data are copied literally.  At an active link every
incident terminal spin is zero, and the accepted SU(2) auxiliary bound forces
the local intertwiner to be the unique zero labelling.

Consequently, equality of two accepted guard grafts implies equality of their
peeled terminal states.  The only information lost by the graft is therefore
the canonical reconstruction trace; this isolates the exact fiber that a
second Peierls estimate must pay.

Constructive contract: pointwise finite-support reconstruction and the proved
accepted auxiliary bound only; no `Classical`, choice, `native_decide`,
`sorry`, new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabAcceptedAuxiliaryValueBound
import YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalAuxiliaryReconstruction
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraft

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardTerminalRecoverability

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedAuxiliaryValueBound
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalAuxiliaryReconstruction
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuard
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLinkWords
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPeeling
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

private theorem natListSum_map_eq_zero_of
    {A : Type} (weight : A → Nat) : ∀ items : List A,
    (∀ item, item ∈ items → weight item = 0) →
      natListSum (items.map weight) = 0
  | [], _ => rfl
  | head :: tail, hzero => by
      simp only [List.map_cons, natListSum]
      rw [hzero head List.mem_cons_self,
        natListSum_map_eq_zero_of weight tail
          (fun item hitem =>
            hzero item (List.mem_cons_of_mem head hitem))]

/-! ## 1. Rigidity of the all-zero local SU(2) fiber -/

/-- Two accepted local fusion witnesses are equal when both physical words
vanish on every face incident on the link. -/
theorem slabLinkFusionWitness_eq_of_incidentPhysical_zero
    {K extent : Nat}
    {leftPhysical rightPhysical left right : SlabLabelling}
    {link : SlabLink}
    (hleft : left ∈
      slabLinkFusionWitnesses K extent leftPhysical link)
    (hright : right ∈
      slabLinkFusionWitnesses K extent rightPhysical link)
    (hleftZero : ∀ faceId,
      faceId ∈ slabIncidentPlaqIds extent link →
        leftPhysical faceId = 0)
    (hrightZero : ∀ faceId,
      faceId ∈ slabIncidentPlaqIds extent link →
        rightPhysical faceId = 0) :
    left = right := by
  have hleftSum :
      natListSum
          ((slabIncidentPlaqIds extent link).map leftPhysical) = 0 :=
    natListSum_map_eq_zero_of leftPhysical
      (slabIncidentPlaqIds extent link) hleftZero
  have hrightSum :
      natListSum
          ((slabIncidentPlaqIds extent link).map rightPhysical) = 0 :=
    natListSum_map_eq_zero_of rightPhysical
      (slabIncidentPlaqIds extent link) hrightZero
  funext edge
  by_cases hedge : edge ∈ canonicalUsedAuxiliaryCoordinates
      (slabIncidentPlaqIds extent link).length
  · have hleftBound :=
      slabLinkFusionWitness_auxiliary_le_incidentPhysical_l1
        hleft edge hedge
    have hrightBound :=
      slabLinkFusionWitness_auxiliary_le_incidentPhysical_l1
        hright edge hedge
    rw [hleftSum] at hleftBound
    rw [hrightSum] at hrightBound
    omega
  · have hleftBounded := (List.mem_filter.mp hleft).1
    have hrightBounded := (List.mem_filter.mp hright).1
    rw [(boundedEdgeLabellings_sound
          (linkAuxiliaryCutoff K)
          (canonicalUsedAuxiliaryCoordinates
            (slabIncidentPlaqIds extent link).length)
          left hleftBounded).2 edge hedge,
      (boundedEdgeLabellings_sound
          (linkAuxiliaryCutoff K)
          (canonicalUsedAuxiliaryCoordinates
            (slabIncidentPlaqIds extent link).length)
          right hrightBounded).2 edge hedge]

/-! ## 2. Physical terminal recovery -/

private theorem terminalLeftPhysical_zero_outside
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (faceId : Nat)
    (houtside : faceId ∉ slabPhysicalFaceEdges D.extent) :
    (reflectedBentGuardCanonicalPeeling
      D hextent state).1.1.1.1 faceId = 0 := by
  have hmem :=
    (mem_slabExpandedFineSources_iff.mp
      (reflectedBentGuardCanonicalPeeling D hextent state).1.1.2).1
  exact (boundedEdgeLabellings_sound D.cutoff D.faceEdges
    (reflectedBentGuardCanonicalPeeling D hextent state).1.1.1.1
    hmem).2 faceId (by simpa [SlabPhysicalData.faceEdges] using houtside)

theorem reflectedBentGuardTerminal_leftPhysical_eq_of_graftPhysical_eq
    (D : SlabPhysicalData)
    (hextent : D.extent = 5)
    (left right : SlabAcceptedTwoReplicaState D)
    (hgraftPhysical :
      reflectedBentGuardGraftLeftPhysical D hextent left =
        reflectedBentGuardGraftLeftPhysical D hextent right) :
    (reflectedBentGuardCanonicalPeeling D hextent left).1.1.1.1 =
      (reflectedBentGuardCanonicalPeeling D hextent right).1.1.1.1 := by
  funext faceId
  by_cases hphysical : faceId ∈ slabPhysicalFaceEdges D.extent
  · by_cases hguard : faceId ∈ reflectedBentPatternGuardFaceIds
    · have hleftZero :=
        (reflectedBentGuardCanonicalPeeling_final_zero
          D hextent left faceId hguard).1
      have hrightZero :=
        (reflectedBentGuardCanonicalPeeling_final_zero
          D hextent right faceId hguard).1
      rw [hleftZero, hrightZero]
    · have hleftOutside :=
        reflectedBentGuardGraftLeftPhysical_eq_terminal_outside
          D hextent left faceId hphysical hguard
      have hrightOutside :=
        reflectedBentGuardGraftLeftPhysical_eq_terminal_outside
          D hextent right faceId hphysical hguard
      rw [← hleftOutside, ← hrightOutside, hgraftPhysical]
  · rw [terminalLeftPhysical_zero_outside
        D hextent left faceId hphysical,
      terminalLeftPhysical_zero_outside
        D hextent right faceId hphysical]

theorem reflectedBentGuardTerminal_leftPhysical_eq_of_graft_eq
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (left right : SlabAcceptedTwoReplicaState D)
    (hgraft : reflectedBentGuardGraftAcceptedState
        D hcutoff hextent left =
      reflectedBentGuardGraftAcceptedState
        D hcutoff hextent right) :
    (reflectedBentGuardCanonicalPeeling D hextent left).1.1.1.1 =
      (reflectedBentGuardCanonicalPeeling D hextent right).1.1.1.1 := by
  apply reflectedBentGuardTerminal_leftPhysical_eq_of_graftPhysical_eq
  have hsource := congrArg (fun state => state.1.1) hgraft
  change (reflectedBentGuardGraftAcceptedState
      D hcutoff hextent left).1.1 =
    (reflectedBentGuardGraftAcceptedState
      D hcutoff hextent right).1.1 at hsource
  rw [reflectedBentGuardGraftAcceptedState_leftSource,
    reflectedBentGuardGraftAcceptedState_leftSource] at hsource
  exact congrArg Prod.fst hsource

theorem reflectedBentGuardTerminal_rightPhysical_eq_of_graftPhysical_eq
    (D : SlabPhysicalData)
    (hextent : D.extent = 5)
    (left right : SlabAcceptedTwoReplicaState D)
    (hgraftPhysical :
      reflectedBentGuardGraftRightPhysical D hextent left =
        reflectedBentGuardGraftRightPhysical D hextent right) :
    (reflectedBentGuardCanonicalPeeling D hextent left).1.2.1.1 =
      (reflectedBentGuardCanonicalPeeling D hextent right).1.2.1.1 := by
  simpa only [reflectedBentGuardGraftRightPhysical] using hgraftPhysical

theorem reflectedBentGuardTerminal_rightPhysical_eq_of_graft_eq
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (left right : SlabAcceptedTwoReplicaState D)
    (hgraft : reflectedBentGuardGraftAcceptedState
        D hcutoff hextent left =
      reflectedBentGuardGraftAcceptedState
        D hcutoff hextent right) :
    (reflectedBentGuardCanonicalPeeling D hextent left).1.2.1.1 =
      (reflectedBentGuardCanonicalPeeling D hextent right).1.2.1.1 := by
  have hsource := congrArg (fun state => state.2.1) hgraft
  change (reflectedBentGuardGraftAcceptedState
      D hcutoff hextent left).2.1 =
    (reflectedBentGuardGraftAcceptedState
      D hcutoff hextent right).2.1 at hsource
  rw [reflectedBentGuardGraftAcceptedState_rightSource,
    reflectedBentGuardGraftAcceptedState_rightSource] at hsource
  have hphysical := congrArg Prod.fst hsource
  exact reflectedBentGuardTerminal_rightPhysical_eq_of_graftPhysical_eq
    D hextent left right hphysical

/-! ## 3. Auxiliary and accepted-state terminal recovery -/

private theorem terminalLeftAssignmentAt_mem
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (link : SlabLink) (hlink : link ∈ boundaryCompleteSlabLinks 5) :
    slabFusionWitnessAssignmentAt link
        (reflectedBentGuardCanonicalPeeling D hextent state).1.1.1.2 ∈
      slabLinkFusionWitnesses D.cutoff 5
        (reflectedBentGuardCanonicalPeeling
          D hextent state).1.1.1.1 link := by
  have hglobal :=
    (mem_slabExpandedFineSources_iff.mp
      (reflectedBentGuardCanonicalPeeling D hextent state).1.1.2).2
  simpa only [hextent] using
    slabFusionWitnessAssignmentAt_mem_local
      D.cutoff D.extent
      (reflectedBentGuardCanonicalPeeling D hextent state).1.1.1.1
      (boundaryCompleteSlabLinks D.extent)
      (reflectedBentGuardCanonicalPeeling D hextent state).1.1.1.2
      hglobal link (by simpa only [hextent] using hlink)

private theorem terminalRightAssignmentAt_mem
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (link : SlabLink) (hlink : link ∈ boundaryCompleteSlabLinks 5) :
    slabFusionWitnessAssignmentAt link
        (reflectedBentGuardCanonicalPeeling D hextent state).1.2.1.2 ∈
      slabLinkFusionWitnesses D.cutoff 5
        (reflectedBentGuardCanonicalPeeling
          D hextent state).1.2.1.1 link := by
  have hglobal :=
    (mem_slabExpandedFineSources_iff.mp
      (reflectedBentGuardCanonicalPeeling D hextent state).1.2.2).2
  simpa only [hextent] using
    slabFusionWitnessAssignmentAt_mem_local
      D.cutoff D.extent
      (reflectedBentGuardCanonicalPeeling D hextent state).1.2.1.1
      (boundaryCompleteSlabLinks D.extent)
      (reflectedBentGuardCanonicalPeeling D hextent state).1.2.1.2
      hglobal link (by simpa only [hextent] using hlink)

private theorem terminalLeftAssignmentAt_eq_of_graftAssignment_eq
    (D : SlabPhysicalData)
    (hextent : D.extent = 5)
    (left right : SlabAcceptedTwoReplicaState D)
    (hgraftAssignment :
      reflectedBentGuardGraftLeftAssignment D hextent left =
        reflectedBentGuardGraftLeftAssignment D hextent right)
    (link : SlabLink)
    (hlink : link ∈ boundaryCompleteSlabLinks 5) :
    slabFusionWitnessAssignmentAt link
        (reflectedBentGuardCanonicalPeeling D hextent left).1.1.1.2 =
      slabFusionWitnessAssignmentAt link
        (reflectedBentGuardCanonicalPeeling D hextent right).1.1.1.2 := by
  cases hactive : reflectedBentPatternActiveLinkB link with
  | false =>
      have hgraftAssignmentAt :=
        congrArg (slabFusionWitnessAssignmentAt link) hgraftAssignment
      have hleftInactive :
          slabFusionWitnessAssignmentAt link
              (reflectedBentGuardGraftLeftAssignment D hextent left) =
            slabFusionWitnessAssignmentAt link
              (reflectedBentGuardCanonicalPeeling
                D hextent left).1.1.1.2 := by
        exact
          reflectedBentGuardGraftLeftAssignmentAt_eq_terminal_of_inactive
            D hextent left link hlink hactive
      have hrightInactive :
          slabFusionWitnessAssignmentAt link
              (reflectedBentGuardGraftLeftAssignment D hextent right) =
            slabFusionWitnessAssignmentAt link
              (reflectedBentGuardCanonicalPeeling
                D hextent right).1.1.1.2 := by
        exact
          reflectedBentGuardGraftLeftAssignmentAt_eq_terminal_of_inactive
            D hextent right link hlink hactive
      exact hleftInactive.symm.trans
        (hgraftAssignmentAt.trans hrightInactive)
  | true =>
      apply slabLinkFusionWitness_eq_of_incidentPhysical_zero
        (terminalLeftAssignmentAt_mem D hextent left link hlink)
        (terminalLeftAssignmentAt_mem D hextent right link hlink)
      · intro faceId hincident
        have hguard := reflectedBentIncidentFace_mem_guard_of_active
          hlink hactive hincident
        exact (reflectedBentGuardCanonicalPeeling_final_zero
          D hextent left faceId hguard).1
      · intro faceId hincident
        have hguard := reflectedBentIncidentFace_mem_guard_of_active
          hlink hactive hincident
        exact (reflectedBentGuardCanonicalPeeling_final_zero
          D hextent right faceId hguard).1

private theorem terminalLeftAssignmentAt_eq_of_graft_eq
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (left right : SlabAcceptedTwoReplicaState D)
    (hgraft : reflectedBentGuardGraftAcceptedState
        D hcutoff hextent left =
      reflectedBentGuardGraftAcceptedState
        D hcutoff hextent right)
    (link : SlabLink)
    (hlink : link ∈ boundaryCompleteSlabLinks 5) :
    slabFusionWitnessAssignmentAt link
        (reflectedBentGuardCanonicalPeeling D hextent left).1.1.1.2 =
      slabFusionWitnessAssignmentAt link
        (reflectedBentGuardCanonicalPeeling D hextent right).1.1.1.2 := by
  have hsource := congrArg (fun state => state.1.1) hgraft
  change (reflectedBentGuardGraftAcceptedState
      D hcutoff hextent left).1.1 =
    (reflectedBentGuardGraftAcceptedState
      D hcutoff hextent right).1.1 at hsource
  rw [reflectedBentGuardGraftAcceptedState_leftSource,
    reflectedBentGuardGraftAcceptedState_leftSource] at hsource
  have hparts :
      reflectedBentGuardGraftLeftPhysical D hextent left =
          reflectedBentGuardGraftLeftPhysical D hextent right ∧
        reflectedBentGuardGraftLeftAssignment D hextent left =
          reflectedBentGuardGraftLeftAssignment D hextent right := by
    simpa only [Prod.mk.injEq] using hsource
  exact terminalLeftAssignmentAt_eq_of_graftAssignment_eq
    D hextent left right hparts.2 link hlink

private theorem terminalRightAssignmentAt_eq_of_graftAssignment_eq
    (D : SlabPhysicalData)
    (hextent : D.extent = 5)
    (left right : SlabAcceptedTwoReplicaState D)
    (hgraftAssignment :
      reflectedBentGuardGraftRightAssignment D hextent left =
        reflectedBentGuardGraftRightAssignment D hextent right)
    (link : SlabLink)
    (hlink : link ∈ boundaryCompleteSlabLinks 5) :
    slabFusionWitnessAssignmentAt link
        (reflectedBentGuardCanonicalPeeling D hextent left).1.2.1.2 =
      slabFusionWitnessAssignmentAt link
        (reflectedBentGuardCanonicalPeeling D hextent right).1.2.1.2 := by
  cases hactive : reflectedBentPatternActiveLinkB link with
  | false =>
      have hgraftAssignmentAt :=
        congrArg (slabFusionWitnessAssignmentAt link) hgraftAssignment
      have hleftInactive :
          slabFusionWitnessAssignmentAt link
              (reflectedBentGuardGraftRightAssignment D hextent left) =
            slabFusionWitnessAssignmentAt link
              (reflectedBentGuardCanonicalPeeling
                D hextent left).1.2.1.2 := by
        exact
          reflectedBentGuardGraftRightAssignmentAt_eq_terminal_of_inactive
            D hextent left link hlink hactive
      have hrightInactive :
          slabFusionWitnessAssignmentAt link
              (reflectedBentGuardGraftRightAssignment D hextent right) =
            slabFusionWitnessAssignmentAt link
              (reflectedBentGuardCanonicalPeeling
                D hextent right).1.2.1.2 := by
        exact
          reflectedBentGuardGraftRightAssignmentAt_eq_terminal_of_inactive
            D hextent right link hlink hactive
      exact hleftInactive.symm.trans
        (hgraftAssignmentAt.trans hrightInactive)
  | true =>
      apply slabLinkFusionWitness_eq_of_incidentPhysical_zero
        (terminalRightAssignmentAt_mem D hextent left link hlink)
        (terminalRightAssignmentAt_mem D hextent right link hlink)
      · intro faceId hincident
        have hguard := reflectedBentIncidentFace_mem_guard_of_active
          hlink hactive hincident
        exact (reflectedBentGuardCanonicalPeeling_final_zero
          D hextent left faceId hguard).2
      · intro faceId hincident
        have hguard := reflectedBentIncidentFace_mem_guard_of_active
          hlink hactive hincident
        exact (reflectedBentGuardCanonicalPeeling_final_zero
          D hextent right faceId hguard).2

private theorem terminalRightAssignmentAt_eq_of_graft_eq
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (left right : SlabAcceptedTwoReplicaState D)
    (hgraft : reflectedBentGuardGraftAcceptedState
        D hcutoff hextent left =
      reflectedBentGuardGraftAcceptedState
        D hcutoff hextent right)
    (link : SlabLink)
    (hlink : link ∈ boundaryCompleteSlabLinks 5) :
    slabFusionWitnessAssignmentAt link
        (reflectedBentGuardCanonicalPeeling D hextent left).1.2.1.2 =
      slabFusionWitnessAssignmentAt link
        (reflectedBentGuardCanonicalPeeling D hextent right).1.2.1.2 := by
  have hsource := congrArg (fun state => state.2.1) hgraft
  change (reflectedBentGuardGraftAcceptedState
      D hcutoff hextent left).2.1 =
    (reflectedBentGuardGraftAcceptedState
      D hcutoff hextent right).2.1 at hsource
  rw [reflectedBentGuardGraftAcceptedState_rightSource,
    reflectedBentGuardGraftAcceptedState_rightSource] at hsource
  have hparts :
      reflectedBentGuardGraftRightPhysical D hextent left =
          reflectedBentGuardGraftRightPhysical D hextent right ∧
        reflectedBentGuardGraftRightAssignment D hextent left =
          reflectedBentGuardGraftRightAssignment D hextent right := by
    simpa only [Prod.mk.injEq] using hsource
  exact terminalRightAssignmentAt_eq_of_graftAssignment_eq
    D hextent left right hparts.2 link hlink

theorem reflectedBentGuardTerminal_leftAssignment_eq_of_graftAssignment_eq
    (D : SlabPhysicalData)
    (hextent : D.extent = 5)
    (left right : SlabAcceptedTwoReplicaState D)
    (hgraftAssignment :
      reflectedBentGuardGraftLeftAssignment D hextent left =
        reflectedBentGuardGraftLeftAssignment D hextent right) :
    (reflectedBentGuardCanonicalPeeling D hextent left).1.1.1.2 =
      (reflectedBentGuardCanonicalPeeling D hextent right).1.1.1.2 := by
  apply slabFusionWitnessAssignment_eq_of_at_eq
    D.cutoff D.extent
    (reflectedBentGuardCanonicalPeeling D hextent left).1.1.1.1
    (reflectedBentGuardCanonicalPeeling D hextent right).1.1.1.1
  · exact (mem_slabExpandedFineSources_iff.mp
      (reflectedBentGuardCanonicalPeeling D hextent left).1.1.2).2
  · exact (mem_slabExpandedFineSources_iff.mp
      (reflectedBentGuardCanonicalPeeling D hextent right).1.1.2).2
  · intro link hlink
    exact terminalLeftAssignmentAt_eq_of_graftAssignment_eq
      D hextent left right hgraftAssignment link
      (by simpa only [hextent] using hlink)

theorem reflectedBentGuardTerminal_leftAssignment_eq_of_graft_eq
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (left right : SlabAcceptedTwoReplicaState D)
    (hgraft : reflectedBentGuardGraftAcceptedState
        D hcutoff hextent left =
      reflectedBentGuardGraftAcceptedState
        D hcutoff hextent right) :
    (reflectedBentGuardCanonicalPeeling D hextent left).1.1.1.2 =
      (reflectedBentGuardCanonicalPeeling D hextent right).1.1.1.2 := by
  apply reflectedBentGuardTerminal_leftAssignment_eq_of_graftAssignment_eq
  have hsource := congrArg (fun state => state.1.1) hgraft
  change (reflectedBentGuardGraftAcceptedState
      D hcutoff hextent left).1.1 =
    (reflectedBentGuardGraftAcceptedState
      D hcutoff hextent right).1.1 at hsource
  rw [reflectedBentGuardGraftAcceptedState_leftSource,
    reflectedBentGuardGraftAcceptedState_leftSource] at hsource
  have hparts :
      reflectedBentGuardGraftLeftPhysical D hextent left =
          reflectedBentGuardGraftLeftPhysical D hextent right ∧
        reflectedBentGuardGraftLeftAssignment D hextent left =
          reflectedBentGuardGraftLeftAssignment D hextent right := by
    simpa only [Prod.mk.injEq] using hsource
  exact hparts.2

theorem reflectedBentGuardTerminal_rightAssignment_eq_of_graftAssignment_eq
    (D : SlabPhysicalData)
    (hextent : D.extent = 5)
    (left right : SlabAcceptedTwoReplicaState D)
    (hgraftAssignment :
      reflectedBentGuardGraftRightAssignment D hextent left =
        reflectedBentGuardGraftRightAssignment D hextent right) :
    (reflectedBentGuardCanonicalPeeling D hextent left).1.2.1.2 =
      (reflectedBentGuardCanonicalPeeling D hextent right).1.2.1.2 := by
  apply slabFusionWitnessAssignment_eq_of_at_eq
    D.cutoff D.extent
    (reflectedBentGuardCanonicalPeeling D hextent left).1.2.1.1
    (reflectedBentGuardCanonicalPeeling D hextent right).1.2.1.1
  · exact (mem_slabExpandedFineSources_iff.mp
      (reflectedBentGuardCanonicalPeeling D hextent left).1.2.2).2
  · exact (mem_slabExpandedFineSources_iff.mp
      (reflectedBentGuardCanonicalPeeling D hextent right).1.2.2).2
  · intro link hlink
    exact terminalRightAssignmentAt_eq_of_graftAssignment_eq
      D hextent left right hgraftAssignment link
      (by simpa only [hextent] using hlink)

theorem reflectedBentGuardTerminal_rightAssignment_eq_of_graft_eq
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (left right : SlabAcceptedTwoReplicaState D)
    (hgraft : reflectedBentGuardGraftAcceptedState
        D hcutoff hextent left =
      reflectedBentGuardGraftAcceptedState
        D hcutoff hextent right) :
    (reflectedBentGuardCanonicalPeeling D hextent left).1.2.1.2 =
      (reflectedBentGuardCanonicalPeeling D hextent right).1.2.1.2 := by
  apply reflectedBentGuardTerminal_rightAssignment_eq_of_graftAssignment_eq
  have hsource := congrArg (fun state => state.2.1) hgraft
  change (reflectedBentGuardGraftAcceptedState
      D hcutoff hextent left).2.1 =
    (reflectedBentGuardGraftAcceptedState
      D hcutoff hextent right).2.1 at hsource
  rw [reflectedBentGuardGraftAcceptedState_rightSource,
    reflectedBentGuardGraftAcceptedState_rightSource] at hsource
  have hparts :
      reflectedBentGuardGraftRightPhysical D hextent left =
          reflectedBentGuardGraftRightPhysical D hextent right ∧
        reflectedBentGuardGraftRightAssignment D hextent left =
          reflectedBentGuardGraftRightAssignment D hextent right := by
    simpa only [Prod.mk.injEq] using hsource
  exact hparts.2

/-- Equality of the four semantic graft components recovers the accepted
peeled terminal.  This formulation is independent of how cutoff-valid
membership proofs package the graft as a state. -/
theorem reflectedBentGuardCanonicalPeeling_terminal_eq_of_graftComponents_eq
    (D : SlabPhysicalData)
    (hextent : D.extent = 5)
    (left right : SlabAcceptedTwoReplicaState D)
    (hleftPhysical :
      reflectedBentGuardGraftLeftPhysical D hextent left =
        reflectedBentGuardGraftLeftPhysical D hextent right)
    (hleftAssignment :
      reflectedBentGuardGraftLeftAssignment D hextent left =
        reflectedBentGuardGraftLeftAssignment D hextent right)
    (hrightPhysical :
      reflectedBentGuardGraftRightPhysical D hextent left =
        reflectedBentGuardGraftRightPhysical D hextent right)
    (hrightAssignment :
      reflectedBentGuardGraftRightAssignment D hextent left =
        reflectedBentGuardGraftRightAssignment D hextent right) :
    (reflectedBentGuardCanonicalPeeling D hextent left).1 =
      (reflectedBentGuardCanonicalPeeling D hextent right).1 := by
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · exact reflectedBentGuardTerminal_leftPhysical_eq_of_graftPhysical_eq
        D hextent left right hleftPhysical
    · exact reflectedBentGuardTerminal_leftAssignment_eq_of_graftAssignment_eq
        D hextent left right hleftAssignment
  · apply Subtype.ext
    apply Prod.ext
    · exact reflectedBentGuardTerminal_rightPhysical_eq_of_graftPhysical_eq
        D hextent left right hrightPhysical
    · exact reflectedBentGuardTerminal_rightAssignment_eq_of_graftAssignment_eq
        D hextent left right hrightAssignment

/-- The accepted guard graft is injective on its peeled terminal projection.
The canonical trace is deliberately absent from the conclusion. -/
theorem reflectedBentGuardCanonicalPeeling_terminal_eq_of_graft_eq
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (left right : SlabAcceptedTwoReplicaState D)
    (hgraft : reflectedBentGuardGraftAcceptedState
        D hcutoff hextent left =
      reflectedBentGuardGraftAcceptedState
        D hcutoff hextent right) :
    (reflectedBentGuardCanonicalPeeling D hextent left).1 =
      (reflectedBentGuardCanonicalPeeling D hextent right).1 := by
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · exact reflectedBentGuardTerminal_leftPhysical_eq_of_graft_eq
        D hcutoff hextent left right hgraft
    · exact reflectedBentGuardTerminal_leftAssignment_eq_of_graft_eq
        D hcutoff hextent left right hgraft
  · apply Subtype.ext
    apply Prod.ext
    · exact reflectedBentGuardTerminal_rightPhysical_eq_of_graft_eq
        D hcutoff hextent left right hgraft
    · exact reflectedBentGuardTerminal_rightAssignment_eq_of_graft_eq
        D hcutoff hextent left right hgraft

#print axioms slabLinkFusionWitness_eq_of_incidentPhysical_zero
#print axioms reflectedBentGuardTerminal_leftPhysical_eq_of_graft_eq
#print axioms reflectedBentGuardTerminal_rightPhysical_eq_of_graft_eq
#print axioms reflectedBentGuardTerminal_leftAssignment_eq_of_graft_eq
#print axioms reflectedBentGuardTerminal_rightAssignment_eq_of_graft_eq
#print axioms reflectedBentGuardCanonicalPeeling_terminal_eq_of_graftComponents_eq
#print axioms reflectedBentGuardCanonicalPeeling_terminal_eq_of_graft_eq

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardTerminalRecoverability
