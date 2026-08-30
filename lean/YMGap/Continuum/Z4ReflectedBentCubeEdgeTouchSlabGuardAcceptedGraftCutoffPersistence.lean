/-
# The reflected accepted graft at every cutoff at least one

The reflected pattern and its selected auxiliary witnesses use only the
cutoff-one carrier.  Cutoff persistence embeds those same active-link
witnesses into every larger auxiliary enumeration.  Inactive links retain
the peeled terminal's native witness at the ambient cutoff.  The existing
Cartesian graft can therefore be accepted under `1 <= D.cutoff`; equality
with cutoff one is unnecessary for this layer.

This module removes the cutoff-one equality from local and global graft
acceptance.  It does not yet transport the downstream positive target and
receiver-rate estimates, and it proves no quantitative uniformity in cutoff.

Constructive contract: explicit witness persistence and structural Cartesian
assembly only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabFineIntertwinerCutoffPersistence
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraft

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraftCutoffPersistence

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerCutoffPersistence
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAssignment
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLinkWords
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPeeling
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotPairing

/-! ## 1. Active cutoff-one witnesses persist -/

theorem reflectedBentLeftFineAssignmentAt_mem_of_one_le
    {cutoff : Nat} (hcutoff : 1 ≤ cutoff)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    slabFusionWitnessAssignmentAt linked.1 reflectedBentLeftFineWitness.1 ∈
      slabLinkFusionWitnesses cutoff 5
        reflectedBentSwitchLeftPhysical linked.1 := by
  have hone :
      slabFusionWitnessAssignmentAt linked.1
          reflectedBentLeftFineWitness.1 ∈
        slabLinkFusionWitnesses 1 5
          reflectedBentSwitchLeftPhysical linked.1 :=
    slabFusionWitnessAssignmentAt_mem_local 1 5
      reflectedBentSwitchLeftPhysical (boundaryCompleteSlabLinks 5)
      reflectedBentLeftFineWitness.1 reflectedBentLeftFineWitness.2
      linked.1 linked.2
  exact slabLinkFusionWitnesses_mem_of_cutoff_le hcutoff
    reflectedBentSwitchLeftPhysical linked.1 _ hone

theorem reflectedBentRightFineAssignmentAt_mem_of_one_le
    {cutoff : Nat} (hcutoff : 1 ≤ cutoff)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    slabFusionWitnessAssignmentAt linked.1 reflectedBentRightFineWitness.1 ∈
      slabLinkFusionWitnesses cutoff 5
        reflectedBentSwitchRightPhysical linked.1 := by
  have hone :
      slabFusionWitnessAssignmentAt linked.1
          reflectedBentRightFineWitness.1 ∈
        slabLinkFusionWitnesses 1 5
          reflectedBentSwitchRightPhysical linked.1 :=
    slabFusionWitnessAssignmentAt_mem_local 1 5
      reflectedBentSwitchRightPhysical (boundaryCompleteSlabLinks 5)
      reflectedBentRightFineWitness.1 reflectedBentRightFineWitness.2
      linked.1 linked.2
  exact slabLinkFusionWitnesses_mem_of_cutoff_le hcutoff
    reflectedBentSwitchRightPhysical linked.1 _ hone

/-! ## 2. Ambient-cutoff local graft acceptance -/

private theorem reflectedBentGuardTerminalLeftAssignmentAt_mem_at_cutoff
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    slabFusionWitnessAssignmentAt linked.1
        (reflectedBentGuardCanonicalPeeling D hextent state).1.1.1.2 ∈
      slabLinkFusionWitnesses D.cutoff 5
        (reflectedBentGuardCanonicalPeeling D hextent state).1.1.1.1
        linked.1 := by
  have hglobal :=
    (mem_slabExpandedFineSources_iff.mp
      (reflectedBentGuardCanonicalPeeling D hextent state).1.1.2).2
  have hlinkedD : linked.1 ∈ boundaryCompleteSlabLinks D.extent := by
    simpa only [hextent] using linked.2
  have hlocal := slabFusionWitnessAssignmentAt_mem_local
    D.cutoff D.extent
    (reflectedBentGuardCanonicalPeeling D hextent state).1.1.1.1
    (boundaryCompleteSlabLinks D.extent)
    (reflectedBentGuardCanonicalPeeling D hextent state).1.1.1.2
    hglobal linked.1 hlinkedD
  simpa only [hextent] using hlocal

private theorem reflectedBentGuardTerminalRightAssignmentAt_mem_at_cutoff
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    slabFusionWitnessAssignmentAt linked.1
        (reflectedBentGuardCanonicalPeeling D hextent state).1.2.1.2 ∈
      slabLinkFusionWitnesses D.cutoff 5
        (reflectedBentGuardCanonicalPeeling D hextent state).1.2.1.1
        linked.1 := by
  have hglobal :=
    (mem_slabExpandedFineSources_iff.mp
      (reflectedBentGuardCanonicalPeeling D hextent state).1.2.2).2
  have hlinkedD : linked.1 ∈ boundaryCompleteSlabLinks D.extent := by
    simpa only [hextent] using linked.2
  have hlocal := slabFusionWitnessAssignmentAt_mem_local
    D.cutoff D.extent
    (reflectedBentGuardCanonicalPeeling D hextent state).1.2.1.1
    (boundaryCompleteSlabLinks D.extent)
    (reflectedBentGuardCanonicalPeeling D hextent state).1.2.1.2
    hglobal linked.1 hlinkedD
  simpa only [hextent] using hlocal

theorem reflectedBentGuardGraftLeftAuxiliary_mem_of_one_le
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    reflectedBentGuardGraftLeftAuxiliary D hextent state linked ∈
      slabLinkFusionWitnesses D.cutoff 5
        (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1 := by
  cases hactive : reflectedBentPatternActiveLinkB linked.1 with
  | false =>
      rw [reflectedBentGuardGraftLeftFusionWitnesses_eq_terminal_of_inactive
        D.cutoff D hextent state hactive]
      simpa only [reflectedBentGuardGraftLeftAuxiliary, hactive,
        Bool.false_eq_true, if_false] using
        reflectedBentGuardTerminalLeftAssignmentAt_mem_at_cutoff
          D hextent state linked
  | true =>
      rw [reflectedBentGuardGraftLeftFusionWitnesses_eq_pattern_of_active
        D.cutoff D hextent state linked.2 hactive]
      simpa only [reflectedBentGuardGraftLeftAuxiliary, hactive,
        if_true] using
        reflectedBentLeftFineAssignmentAt_mem_of_one_le hcutoff linked

theorem reflectedBentGuardGraftRightAuxiliary_mem_of_one_le
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    reflectedBentGuardGraftRightAuxiliary D hextent state linked ∈
      slabLinkFusionWitnesses D.cutoff 5
        (reflectedBentGuardGraftRightPhysical D hextent state) linked.1 := by
  cases hactive : reflectedBentPatternActiveLinkB linked.1 with
  | false =>
      rw [reflectedBentGuardGraftRightFusionWitnesses_eq_terminal
        D.cutoff D hextent state linked.1]
      simpa only [reflectedBentGuardGraftRightAuxiliary, hactive,
        Bool.false_eq_true, if_false] using
        reflectedBentGuardTerminalRightAssignmentAt_mem_at_cutoff
          D hextent state linked
  | true =>
      rw [reflectedBentGuardGraftRightFusionWitnesses_eq_pattern_of_active
        D.cutoff D hextent state linked.2 hactive]
      simpa only [reflectedBentGuardGraftRightAuxiliary, hactive,
        if_true] using
        reflectedBentRightFineAssignmentAt_mem_of_one_le hcutoff linked

/-! ## 3. Global ambient-cutoff graft acceptance -/

theorem reflectedBentGuardGraftLeftAssignmentFrom_mem_of_one_le
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5},
      reflectedBentGuardGraftLeftAssignmentFrom
          D hextent state linkedList ∈
        slabFusionWitnessAssignmentsOn D.cutoff 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (linkedList.map Subtype.val)
  | [] => List.mem_cons_self
  | linked :: rest => by
      simp only [List.map_cons, slabFusionWitnessAssignmentsOn,
        reflectedBentGuardGraftLeftAssignmentFrom]
      apply List.mem_flatMap.mpr
      refine ⟨reflectedBentGuardGraftLeftAuxiliary
          D hextent state linked,
        reflectedBentGuardGraftLeftAuxiliary_mem_of_one_le
          D hcutoff hextent state linked, ?_⟩
      exact List.mem_map.mpr
        ⟨reflectedBentGuardGraftLeftAssignmentFrom D hextent state rest,
          reflectedBentGuardGraftLeftAssignmentFrom_mem_of_one_le
            D hcutoff hextent state rest, rfl⟩

theorem reflectedBentGuardGraftRightAssignmentFrom_mem_of_one_le
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5},
      reflectedBentGuardGraftRightAssignmentFrom
          D hextent state linkedList ∈
        slabFusionWitnessAssignmentsOn D.cutoff 5
          (reflectedBentGuardGraftRightPhysical D hextent state)
          (linkedList.map Subtype.val)
  | [] => List.mem_cons_self
  | linked :: rest => by
      simp only [List.map_cons, slabFusionWitnessAssignmentsOn,
        reflectedBentGuardGraftRightAssignmentFrom]
      apply List.mem_flatMap.mpr
      refine ⟨reflectedBentGuardGraftRightAuxiliary
          D hextent state linked,
        reflectedBentGuardGraftRightAuxiliary_mem_of_one_le
          D hcutoff hextent state linked, ?_⟩
      exact List.mem_map.mpr
        ⟨reflectedBentGuardGraftRightAssignmentFrom D hextent state rest,
          reflectedBentGuardGraftRightAssignmentFrom_mem_of_one_le
            D hcutoff hextent state rest, rfl⟩

theorem reflectedBentGuardGraftLeftAssignment_mem_of_one_le
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftLeftAssignment D hextent state ∈
      slabFineFusionWitnesses D
        (reflectedBentGuardGraftLeftPhysical D hextent state) := by
  have hmem := reflectedBentGuardGraftLeftAssignmentFrom_mem_of_one_le
    D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach
  rw [List.attach_map_subtype_val] at hmem
  unfold reflectedBentGuardGraftLeftAssignment slabFineFusionWitnesses
  simpa only [hextent] using hmem

theorem reflectedBentGuardGraftRightAssignment_mem_of_one_le
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftRightAssignment D hextent state ∈
      slabFineFusionWitnesses D
        (reflectedBentGuardGraftRightPhysical D hextent state) := by
  have hmem := reflectedBentGuardGraftRightAssignmentFrom_mem_of_one_le
    D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach
  rw [List.attach_map_subtype_val] at hmem
  unfold reflectedBentGuardGraftRightAssignment slabFineFusionWitnesses
  simpa only [hextent] using hmem

/-! ## 4. The grafted physical source also persists -/

theorem reflectedBentGuardGraftLeftPhysical_bounded_of_one_le
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabFaceLabellingBounded D.cutoff D.extent
      (reflectedBentGuardGraftLeftPhysical D hextent state) := by
  intro faceId hphysical
  unfold reflectedBentGuardGraftLeftPhysical
  split
  · have hphysicalFive : faceId ∈ slabPhysicalFaceEdges 5 := by
      simpa only [hextent] using hphysical
    exact Nat.le_trans
      (reflectedBentSwitchLeftPhysical_bounded faceId hphysicalFive)
      hcutoff
  · exact SlabExpandedFineSourceEntry.physical_bounded
      (reflectedBentGuardCanonicalPeeling D hextent state).1.1
      faceId hphysical

theorem reflectedBentGuardGraftLeftPhysical_mem_of_one_le
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftLeftPhysical D hextent state ∈
      D.physicalLabellings := by
  unfold SlabPhysicalData.physicalLabellings
  apply boundedEdgeLabellings_complete
  · intro faceId hface
    have hle := reflectedBentGuardGraftLeftPhysical_bounded_of_one_le
      D hcutoff hextent state faceId hface
    omega
  · intro faceId houtside
    have houtsideFive : faceId ∉ slabPhysicalFaceEdges 5 := by
      intro hphysicalFive
      apply houtside
      unfold SlabPhysicalData.faceEdges
      simpa only [hextent] using hphysicalFive
    have hpatternZero : reflectedBentSwitchLeftPhysical faceId = 0 :=
      slabBinarySupportLabelling_eq_zero_of_not_physical houtsideFive
    have hterminalPhysical :=
      (mem_slabExpandedFineSources_iff.mp
        (reflectedBentGuardCanonicalPeeling D hextent state).1.1.2).1
    have hterminalZero :=
      (boundedEdgeLabellings_sound D.cutoff D.faceEdges
        (reflectedBentGuardCanonicalPeeling D hextent state).1.1.1.1
        hterminalPhysical).2 faceId houtside
    unfold reflectedBentGuardGraftLeftPhysical
    rw [hpatternZero, hterminalZero]
    simp

theorem reflectedBentGuardGraftLeftSource_mem_of_one_le
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (reflectedBentGuardGraftLeftPhysical D hextent state,
      reflectedBentGuardGraftLeftAssignment D hextent state) ∈
        slabExpandedFineSources D := by
  unfold slabExpandedFineSources
  apply List.mem_flatMap.mpr
  refine ⟨reflectedBentGuardGraftLeftPhysical D hextent state,
    reflectedBentGuardGraftLeftPhysical_mem_of_one_le
      D hcutoff hextent state, ?_⟩
  unfold slabExpandedFineSourceBlock
  apply List.mem_map.mpr
  exact ⟨reflectedBentGuardGraftLeftAssignment D hextent state,
    reflectedBentGuardGraftLeftAssignment_mem_of_one_le
      D hcutoff hextent state, rfl⟩

theorem reflectedBentGuardGraftRightSource_mem_of_one_le
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (reflectedBentGuardGraftRightPhysical D hextent state,
      reflectedBentGuardGraftRightAssignment D hextent state) ∈
        slabExpandedFineSources D := by
  unfold slabExpandedFineSources
  apply List.mem_flatMap.mpr
  refine ⟨reflectedBentGuardGraftRightPhysical D hextent state,
    reflectedBentGuardGraftRightPhysical_mem D hextent state, ?_⟩
  unfold slabExpandedFineSourceBlock
  apply List.mem_map.mpr
  exact ⟨reflectedBentGuardGraftRightAssignment D hextent state,
    reflectedBentGuardGraftRightAssignment_mem_of_one_le
      D hcutoff hextent state, rfl⟩

#print axioms reflectedBentLeftFineAssignmentAt_mem_of_one_le
#print axioms reflectedBentGuardGraftLeftAuxiliary_mem_of_one_le
#print axioms reflectedBentGuardGraftRightAuxiliary_mem_of_one_le
#print axioms reflectedBentGuardGraftLeftAssignment_mem_of_one_le
#print axioms reflectedBentGuardGraftRightAssignment_mem_of_one_le
#print axioms reflectedBentGuardGraftLeftPhysical_mem_of_one_le
#print axioms reflectedBentGuardGraftLeftSource_mem_of_one_le
#print axioms reflectedBentGuardGraftRightSource_mem_of_one_le

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraftCutoffPersistence
