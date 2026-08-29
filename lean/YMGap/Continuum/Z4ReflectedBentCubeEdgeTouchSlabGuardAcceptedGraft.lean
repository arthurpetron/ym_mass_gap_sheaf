/-
# Accepted global graft of the reflected channel

For a cutoff-one, extent-five corrected slab, splice the already accepted
reflected auxiliary into every pattern-active link of the guarded physical
graft and retain the peeled terminal auxiliary at every inactive link.  The
link-word dichotomy proves that each selected auxiliary belongs to the new
local fiber.  Structural recursion then assembles complete accepted left and
right assignments and hence a literal accepted two-replica graft state.

This closes acceptance of the physical surgery at the concrete cutoff-one
carrier.  Positivity of a recoupling row into this graft, weighted inverse
control, and transport to larger cutoffs or volumes remain downstream.

Constructive contract: finite Cartesian recursion and previously accepted
local witnesses only; no `Classical`, choice, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLinkWords
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetRealization

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraft

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
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
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLinkWords
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPeeling
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotPairing

/-! ## 1. Accepted local auxiliaries selected from the two known fibers -/

def reflectedBentGuardGraftLeftAuxiliary
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    SlabLabelling :=
  if reflectedBentPatternActiveLinkB linked.1 then
    slabFusionWitnessAssignmentAt linked.1 reflectedBentLeftFineWitness.1
  else
    slabFusionWitnessAssignmentAt linked.1
      (reflectedBentGuardCanonicalPeeling D hextent state).1.1.1.2

def reflectedBentGuardGraftRightAuxiliary
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    SlabLabelling :=
  slabFusionWitnessAssignmentAt linked.1
    (reflectedBentGuardCanonicalPeeling D hextent state).1.2.1.2

private theorem reflectedBentLeftFineAssignmentAt_mem
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    slabFusionWitnessAssignmentAt linked.1 reflectedBentLeftFineWitness.1 ∈
      slabLinkFusionWitnesses 1 5
        reflectedBentSwitchLeftPhysical linked.1 := by
  exact slabFusionWitnessAssignmentAt_mem_local 1 5
    reflectedBentSwitchLeftPhysical (boundaryCompleteSlabLinks 5)
    reflectedBentLeftFineWitness.1 reflectedBentLeftFineWitness.2
    linked.1 linked.2

private theorem reflectedBentGuardTerminalLeftAssignmentAt_mem
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    slabFusionWitnessAssignmentAt linked.1
        (reflectedBentGuardCanonicalPeeling D hextent state).1.1.1.2 ∈
      slabLinkFusionWitnesses 1 5
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
  simpa only [hcutoff, hextent] using hlocal

private theorem reflectedBentGuardTerminalRightAssignmentAt_mem
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    slabFusionWitnessAssignmentAt linked.1
        (reflectedBentGuardCanonicalPeeling D hextent state).1.2.1.2 ∈
      slabLinkFusionWitnesses 1 5
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
  simpa only [hcutoff, hextent] using hlocal

theorem reflectedBentGuardGraftLeftAuxiliary_mem
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    reflectedBentGuardGraftLeftAuxiliary D hextent state linked ∈
      slabLinkFusionWitnesses 1 5
        (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1 := by
  cases hactive : reflectedBentPatternActiveLinkB linked.1 with
  | false =>
      rw [reflectedBentGuardGraftLeftFusionWitnesses_eq_terminal_of_inactive
        1 D hextent state hactive]
      simpa only [reflectedBentGuardGraftLeftAuxiliary, hactive,
        Bool.false_eq_true, if_false] using
        reflectedBentGuardTerminalLeftAssignmentAt_mem
          D hcutoff hextent state linked
  | true =>
      rw [reflectedBentGuardGraftLeftFusionWitnesses_eq_pattern_of_active
        1 D hextent state linked.2 hactive]
      simpa only [reflectedBentGuardGraftLeftAuxiliary, hactive,
        if_true] using reflectedBentLeftFineAssignmentAt_mem linked

theorem reflectedBentGuardGraftRightAuxiliary_mem
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    reflectedBentGuardGraftRightAuxiliary D hextent state linked ∈
      slabLinkFusionWitnesses 1 5
        (reflectedBentGuardGraftRightPhysical D hextent state) linked.1 := by
  rw [reflectedBentGuardGraftRightFusionWitnesses_eq_terminal
    1 D hextent state linked.1]
  exact reflectedBentGuardTerminalRightAssignmentAt_mem
    D hcutoff hextent state linked

/-! ## 2. Structural Cartesian assembly of both global assignments -/

def reflectedBentGuardGraftLeftAssignmentFrom
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    List {link // link ∈ boundaryCompleteSlabLinks 5} →
      SlabFusionWitnessAssignment
  | [] => []
  | linked :: rest =>
      (linked.1, reflectedBentGuardGraftLeftAuxiliary
        D hextent state linked) ::
        reflectedBentGuardGraftLeftAssignmentFrom D hextent state rest

def reflectedBentGuardGraftRightAssignmentFrom
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    List {link // link ∈ boundaryCompleteSlabLinks 5} →
      SlabFusionWitnessAssignment
  | [] => []
  | linked :: rest =>
      (linked.1, reflectedBentGuardGraftRightAuxiliary
        D hextent state linked) ::
        reflectedBentGuardGraftRightAssignmentFrom D hextent state rest

theorem reflectedBentGuardGraftLeftAssignmentFrom_mem
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5},
      reflectedBentGuardGraftLeftAssignmentFrom
          D hextent state linkedList ∈
        slabFusionWitnessAssignmentsOn 1 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (linkedList.map Subtype.val)
  | [] => List.mem_cons_self
  | linked :: rest => by
      simp only [List.map_cons, slabFusionWitnessAssignmentsOn,
        reflectedBentGuardGraftLeftAssignmentFrom]
      apply List.mem_flatMap.mpr
      refine ⟨reflectedBentGuardGraftLeftAuxiliary
          D hextent state linked,
        reflectedBentGuardGraftLeftAuxiliary_mem
          D hcutoff hextent state linked, ?_⟩
      exact List.mem_map.mpr
        ⟨reflectedBentGuardGraftLeftAssignmentFrom D hextent state rest,
          reflectedBentGuardGraftLeftAssignmentFrom_mem
            D hcutoff hextent state rest, rfl⟩

theorem reflectedBentGuardGraftRightAssignmentFrom_mem
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5},
      reflectedBentGuardGraftRightAssignmentFrom
          D hextent state linkedList ∈
        slabFusionWitnessAssignmentsOn 1 5
          (reflectedBentGuardGraftRightPhysical D hextent state)
          (linkedList.map Subtype.val)
  | [] => List.mem_cons_self
  | linked :: rest => by
      simp only [List.map_cons, slabFusionWitnessAssignmentsOn,
        reflectedBentGuardGraftRightAssignmentFrom]
      apply List.mem_flatMap.mpr
      refine ⟨reflectedBentGuardGraftRightAuxiliary
          D hextent state linked,
        reflectedBentGuardGraftRightAuxiliary_mem
          D hcutoff hextent state linked, ?_⟩
      exact List.mem_map.mpr
        ⟨reflectedBentGuardGraftRightAssignmentFrom D hextent state rest,
          reflectedBentGuardGraftRightAssignmentFrom_mem
            D hcutoff hextent state rest, rfl⟩

def reflectedBentGuardGraftLeftAssignment
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabFusionWitnessAssignment :=
  reflectedBentGuardGraftLeftAssignmentFrom D hextent state
    (boundaryCompleteSlabLinks 5).attach

def reflectedBentGuardGraftRightAssignment
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabFusionWitnessAssignment :=
  reflectedBentGuardGraftRightAssignmentFrom D hextent state
    (boundaryCompleteSlabLinks 5).attach

theorem reflectedBentGuardGraftLeftAssignment_mem
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftLeftAssignment D hextent state ∈
      slabFineFusionWitnesses D
        (reflectedBentGuardGraftLeftPhysical D hextent state) := by
  have hmem := reflectedBentGuardGraftLeftAssignmentFrom_mem
    D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach
  rw [List.attach_map_subtype_val] at hmem
  unfold reflectedBentGuardGraftLeftAssignment slabFineFusionWitnesses
  simpa only [hcutoff, hextent] using hmem

theorem reflectedBentGuardGraftRightAssignment_mem
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftRightAssignment D hextent state ∈
      slabFineFusionWitnesses D
        (reflectedBentGuardGraftRightPhysical D hextent state) := by
  have hmem := reflectedBentGuardGraftRightAssignmentFrom_mem
    D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach
  rw [List.attach_map_subtype_val] at hmem
  unfold reflectedBentGuardGraftRightAssignment slabFineFusionWitnesses
  simpa only [hcutoff, hextent] using hmem

/-! ## 3. Physical membership and the accepted two-replica graft -/

theorem reflectedBentGuardGraftLeftPhysical_bounded
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabFaceLabellingBounded D.cutoff D.extent
      (reflectedBentGuardGraftLeftPhysical D hextent state) := by
  intro faceId hphysical
  unfold reflectedBentGuardGraftLeftPhysical
  split
  · have hphysicalFive : faceId ∈ slabPhysicalFaceEdges 5 := by
      simpa only [hextent] using hphysical
    have hbound := reflectedBentSwitchLeftPhysical_bounded
      faceId hphysicalFive
    simpa only [hcutoff] using hbound
  · exact SlabExpandedFineSourceEntry.physical_bounded
      (reflectedBentGuardCanonicalPeeling D hextent state).1.1
      faceId hphysical

theorem reflectedBentGuardGraftRightPhysical_bounded
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabFaceLabellingBounded D.cutoff D.extent
      (reflectedBentGuardGraftRightPhysical D hextent state) :=
  SlabExpandedFineSourceEntry.physical_bounded
    (reflectedBentGuardCanonicalPeeling D hextent state).1.2

private theorem reflectedBentGuardTerminalLeftPhysical_zero_outside
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (faceId : Nat) (houtside : faceId ∉ D.faceEdges) :
    (reflectedBentGuardCanonicalPeeling D hextent state).1.1.1.1 faceId = 0 := by
  have hphysical :=
    (mem_slabExpandedFineSources_iff.mp
      (reflectedBentGuardCanonicalPeeling D hextent state).1.1.2).1
  exact (boundedEdgeLabellings_sound D.cutoff D.faceEdges
    (reflectedBentGuardCanonicalPeeling D hextent state).1.1.1.1
    hphysical).2 faceId houtside

private theorem reflectedBentGuardTerminalRightPhysical_zero_outside
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (faceId : Nat) (houtside : faceId ∉ D.faceEdges) :
    (reflectedBentGuardCanonicalPeeling D hextent state).1.2.1.1 faceId = 0 := by
  have hphysical :=
    (mem_slabExpandedFineSources_iff.mp
      (reflectedBentGuardCanonicalPeeling D hextent state).1.2.2).1
  exact (boundedEdgeLabellings_sound D.cutoff D.faceEdges
    (reflectedBentGuardCanonicalPeeling D hextent state).1.2.1.1
    hphysical).2 faceId houtside

theorem reflectedBentGuardGraftLeftPhysical_mem
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftLeftPhysical D hextent state ∈
      D.physicalLabellings := by
  unfold SlabPhysicalData.physicalLabellings
  apply boundedEdgeLabellings_complete
  · intro faceId hface
    have hle := reflectedBentGuardGraftLeftPhysical_bounded
      D hcutoff hextent state faceId hface
    omega
  · intro faceId houtside
    have houtsideFive : faceId ∉ slabPhysicalFaceEdges 5 := by
      intro hphysicalFive
      apply houtside
      unfold SlabPhysicalData.faceEdges
      simpa only [hextent] using hphysicalFive
    have hpatternZero : reflectedBentSwitchLeftPhysical faceId = 0 := by
      exact slabBinarySupportLabelling_eq_zero_of_not_physical
        houtsideFive
    have hterminalZero :=
      reflectedBentGuardTerminalLeftPhysical_zero_outside
        D hextent state faceId houtside
    unfold reflectedBentGuardGraftLeftPhysical
    rw [hpatternZero, hterminalZero]
    simp

theorem reflectedBentGuardGraftRightPhysical_mem
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftRightPhysical D hextent state ∈
      D.physicalLabellings := by
  unfold SlabPhysicalData.physicalLabellings
  apply boundedEdgeLabellings_complete
  · intro faceId hface
    have hle := reflectedBentGuardGraftRightPhysical_bounded
      D hextent state faceId hface
    omega
  · intro faceId houtside
    exact reflectedBentGuardTerminalRightPhysical_zero_outside
      D hextent state faceId houtside

theorem reflectedBentGuardGraftLeftSource_mem
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (reflectedBentGuardGraftLeftPhysical D hextent state,
      reflectedBentGuardGraftLeftAssignment D hextent state) ∈
        slabExpandedFineSources D := by
  unfold slabExpandedFineSources
  apply List.mem_flatMap.mpr
  refine ⟨reflectedBentGuardGraftLeftPhysical D hextent state,
    reflectedBentGuardGraftLeftPhysical_mem
      D hcutoff hextent state, ?_⟩
  unfold slabExpandedFineSourceBlock
  apply List.mem_map.mpr
  exact ⟨reflectedBentGuardGraftLeftAssignment D hextent state,
    reflectedBentGuardGraftLeftAssignment_mem
      D hcutoff hextent state, rfl⟩

theorem reflectedBentGuardGraftRightSource_mem
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
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
    reflectedBentGuardGraftRightAssignment_mem
      D hcutoff hextent state, rfl⟩

def reflectedBentGuardGraftLeftEntry
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabExpandedFineSourceEntry D :=
  ⟨(reflectedBentGuardGraftLeftPhysical D hextent state,
        reflectedBentGuardGraftLeftAssignment D hextent state),
    reflectedBentGuardGraftLeftSource_mem D hcutoff hextent state⟩

def reflectedBentGuardGraftRightEntry
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabExpandedFineSourceEntry D :=
  ⟨(reflectedBentGuardGraftRightPhysical D hextent state,
        reflectedBentGuardGraftRightAssignment D hextent state),
    reflectedBentGuardGraftRightSource_mem D hcutoff hextent state⟩

def reflectedBentGuardGraftAcceptedState
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabAcceptedTwoReplicaState D :=
  (reflectedBentGuardGraftLeftEntry D hcutoff hextent state,
    reflectedBentGuardGraftRightEntry D hcutoff hextent state)

theorem reflectedBentGuardGraftAcceptedState_leftPhysical
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (reflectedBentGuardGraftAcceptedState
      D hcutoff hextent state).1.1.1 =
        reflectedBentGuardGraftLeftPhysical D hextent state :=
  by
    change (reflectedBentGuardGraftLeftEntry
      D hcutoff hextent state).1.1 = _
    rfl

#print axioms reflectedBentGuardGraftLeftAuxiliary_mem
#print axioms reflectedBentGuardGraftRightAuxiliary_mem
#print axioms reflectedBentGuardGraftLeftAssignmentFrom_mem
#print axioms reflectedBentGuardGraftRightAssignmentFrom_mem
#print axioms reflectedBentGuardGraftLeftAssignment_mem
#print axioms reflectedBentGuardGraftRightAssignment_mem
#print axioms reflectedBentGuardGraftLeftPhysical_mem
#print axioms reflectedBentGuardGraftRightPhysical_mem
#print axioms reflectedBentGuardGraftAcceptedState

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraft
