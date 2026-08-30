/-
# Identify the ambient guarded target graph with the standard assignment graph

Lookup in each ambient structurally assembled target assignment returns its
local realized auxiliary.  Therefore the standard global face-strand graph of
the accepted target state is exactly the cutoff-parametric projected graph
already proved to disconnect the marked faces.

Constructive contract: list recursion, proof irrelevance, and exact graph
equality only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetGraphBridge
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetDisconnectionCutoffPersistence

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetGraphBridgeCutoffPersistence

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetDisconnectionCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetEdgesCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetGraphBridge
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealizationCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableGraphBridge

/-! ## 1. Exact lookup in the two ambient assignments -/

theorem reflectedBentGuardGraftRealizedLeftAssignmentAtCutoff_lookup_eq
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5})
      (linked : {link // link ∈ boundaryCompleteSlabLinks 5}),
      linked ∈ linkedList →
      slabFusionWitnessAssignmentAt linked.1
          (reflectedBentGuardGraftRealizedLeftAssignmentFromAtCutoff
            D hcutoff hextent state linkedList) =
        reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff
          D hcutoff hextent state linked
  | [], linked, hmem => False.elim (List.not_mem_nil hmem)
  | head :: rest, linked, hmem => by
      by_cases hsame : head.1 = linked.1
      · have hsubtype : head = linked := Subtype.ext hsame
        subst head
        simp [slabFusionWitnessAssignmentAt,
          reflectedBentGuardGraftRealizedLeftAssignmentFromAtCutoff]
      · have hrest : linked ∈ rest := by
          rcases List.mem_cons.mp hmem with hhead | htail
          · exact False.elim
              (hsame (congrArg Subtype.val hhead.symm))
          · exact htail
        simp only [
          reflectedBentGuardGraftRealizedLeftAssignmentFromAtCutoff,
          slabFusionWitnessAssignmentAt, hsame, if_false]
        exact reflectedBentGuardGraftRealizedLeftAssignmentAtCutoff_lookup_eq
          D hcutoff hextent state rest linked hrest

theorem reflectedBentGuardGraftRealizedRightAssignmentAtCutoff_lookup_eq
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5})
      (linked : {link // link ∈ boundaryCompleteSlabLinks 5}),
      linked ∈ linkedList →
      slabFusionWitnessAssignmentAt linked.1
          (reflectedBentGuardGraftRealizedRightAssignmentFromAtCutoff
            D hcutoff hextent state linkedList) =
        reflectedBentGuardGraftRealizedRightAuxiliaryAtCutoff
          D hcutoff hextent state linked
  | [], linked, hmem => False.elim (List.not_mem_nil hmem)
  | head :: rest, linked, hmem => by
      by_cases hsame : head.1 = linked.1
      · have hsubtype : head = linked := Subtype.ext hsame
        subst head
        simp [slabFusionWitnessAssignmentAt,
          reflectedBentGuardGraftRealizedRightAssignmentFromAtCutoff]
      · have hrest : linked ∈ rest := by
          rcases List.mem_cons.mp hmem with hhead | htail
          · exact False.elim
              (hsame (congrArg Subtype.val hhead.symm))
          · exact htail
        simp only [
          reflectedBentGuardGraftRealizedRightAssignmentFromAtCutoff,
          slabFusionWitnessAssignmentAt, hsame, if_false]
        exact reflectedBentGuardGraftRealizedRightAssignmentAtCutoff_lookup_eq
          D hcutoff hextent state rest linked hrest

/-! ## 2. Standard global graph equals the classified ambient graph -/

def reflectedBentGuardGraftRealizedLeftFaceStrandEdgesAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :=
  slabFineFusionWitnessFaceStrandEdges D
    (reflectedBentGuardGraftLeftPhysical D hextent state)
    (reflectedBentGuardGraftRealizedLeftAssignmentAtCutoff
      D hcutoff hextent state)
    (reflectedBentGuardGraftRealizedLeftAssignmentAtCutoff_mem
      D hcutoff hextent state)

def reflectedBentGuardGraftRealizedRightFaceStrandEdgesAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :=
  slabFineFusionWitnessFaceStrandEdges D
    (reflectedBentGuardGraftRightPhysical D hextent state)
    (reflectedBentGuardGraftRealizedRightAssignmentAtCutoff
      D hcutoff hextent state)
    (reflectedBentGuardGraftRealizedRightAssignmentAtCutoff_mem
      D hcutoff hextent state)

theorem reflectedBentGuardGraftRealizedLeftFaceStrandEdgesAtCutoff_eq_local
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftRealizedLeftFaceStrandEdgesAtCutoff
        D hcutoff hextent state =
      (boundaryCompleteSlabLinks 5).attach.flatMap fun linked =>
        slabLinkFaceStrandEdges D.cutoff 5
          (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
          (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff
            D hcutoff hextent state linked)
          (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff_mem
            D hcutoff hextent state linked) := by
  have hmem :=
    reflectedBentGuardGraftRealizedLeftAssignmentFromAtCutoff_mem
      D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach
  rw [List.attach_map_subtype_val] at hmem
  have hfixed :
      slabFusionWitnessAssignmentFaceStrandEdges D.cutoff 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (boundaryCompleteSlabLinks 5)
          (reflectedBentGuardGraftRealizedLeftAssignmentAtCutoff
            D hcutoff hextent state) hmem =
        (boundaryCompleteSlabLinks 5).attach.flatMap fun linked =>
          slabLinkFaceStrandEdges D.cutoff 5
            (reflectedBentGuardGraftLeftPhysical D hextent state) linked.1
            (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff
              D hcutoff hextent state linked)
            (reflectedBentGuardGraftRealizedLeftAuxiliaryAtCutoff_mem
              D hcutoff hextent state linked) := by
    unfold slabFusionWitnessAssignmentFaceStrandEdges
    apply congrArg (fun compiler =>
      (boundaryCompleteSlabLinks 5).attach.flatMap compiler)
    funext linked
    unfold slabFusionWitnessAssignmentFaceStrandEdgesAt
      reflectedBentGuardGraftRealizedLeftAssignmentAtCutoff
    have hlookup :=
      reflectedBentGuardGraftRealizedLeftAssignmentAtCutoff_lookup_eq
        D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach linked
        (List.mem_attach (boundaryCompleteSlabLinks 5) linked)
    exact slabLinkFaceStrandEdges_eq_of_auxiliary_eq _ _ hlookup
  simpa only [reflectedBentGuardGraftRealizedLeftFaceStrandEdgesAtCutoff,
    slabFineFusionWitnessFaceStrandEdges, hextent] using hfixed

theorem reflectedBentGuardGraftRealizedRightFaceStrandEdgesAtCutoff_eq_local
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftRealizedRightFaceStrandEdgesAtCutoff
        D hcutoff hextent state =
      (boundaryCompleteSlabLinks 5).attach.flatMap fun linked =>
        slabLinkFaceStrandEdges D.cutoff 5
          (reflectedBentGuardGraftRightPhysical D hextent state) linked.1
          (reflectedBentGuardGraftRealizedRightAuxiliaryAtCutoff
            D hcutoff hextent state linked)
          (reflectedBentGuardGraftRealizedRightAuxiliaryAtCutoff_mem
            D hcutoff hextent state linked) := by
  have hmem :=
    reflectedBentGuardGraftRealizedRightAssignmentFromAtCutoff_mem
      D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach
  rw [List.attach_map_subtype_val] at hmem
  have hfixed :
      slabFusionWitnessAssignmentFaceStrandEdges D.cutoff 5
          (reflectedBentGuardGraftRightPhysical D hextent state)
          (boundaryCompleteSlabLinks 5)
          (reflectedBentGuardGraftRealizedRightAssignmentAtCutoff
            D hcutoff hextent state) hmem =
        (boundaryCompleteSlabLinks 5).attach.flatMap fun linked =>
          slabLinkFaceStrandEdges D.cutoff 5
            (reflectedBentGuardGraftRightPhysical D hextent state) linked.1
            (reflectedBentGuardGraftRealizedRightAuxiliaryAtCutoff
              D hcutoff hextent state linked)
            (reflectedBentGuardGraftRealizedRightAuxiliaryAtCutoff_mem
              D hcutoff hextent state linked) := by
    unfold slabFusionWitnessAssignmentFaceStrandEdges
    apply congrArg (fun compiler =>
      (boundaryCompleteSlabLinks 5).attach.flatMap compiler)
    funext linked
    unfold slabFusionWitnessAssignmentFaceStrandEdgesAt
      reflectedBentGuardGraftRealizedRightAssignmentAtCutoff
    have hlookup :=
      reflectedBentGuardGraftRealizedRightAssignmentAtCutoff_lookup_eq
        D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach linked
        (List.mem_attach (boundaryCompleteSlabLinks 5) linked)
    exact slabLinkFaceStrandEdges_eq_of_auxiliary_eq _ _ hlookup
  simpa only [reflectedBentGuardGraftRealizedRightFaceStrandEdgesAtCutoff,
    slabFineFusionWitnessFaceStrandEdges, hextent] using hfixed

theorem reflectedBentGuardGraftRealizedPairedProjectedFaceEdgesAtCutoff_eq_target
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    slabProjectedFaceEdges
        (reflectedBentGuardGraftRealizedLeftFaceStrandEdgesAtCutoff
          D hcutoff hextent state) ++
      slabProjectedFaceEdges
        (reflectedBentGuardGraftRealizedRightFaceStrandEdgesAtCutoff
          D hcutoff hextent state) =
      reflectedBentGuardGraftPositiveTargetProjectedFaceEdgesAtCutoff
        D hcutoff hextent state := by
  rw [reflectedBentGuardGraftRealizedLeftFaceStrandEdgesAtCutoff_eq_local,
    reflectedBentGuardGraftRealizedRightFaceStrandEdgesAtCutoff_eq_local]
  unfold reflectedBentGuardGraftPositiveTargetProjectedFaceEdgesAtCutoff
    reflectedBentGuardGraftRealizedLeftProjectedFaceEdgesAtCutoff
    reflectedBentGuardGraftRealizedRightProjectedFaceEdgesAtCutoff
    slabProjectedFaceEdges
  simp only [List.map_flatMap]

theorem reflectedBentGuardGraftRealizedPairedFaceVerticesAtCutoff_eq_target
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    slabFaceStrandFaceVertices
        (reflectedBentGuardGraftRealizedLeftFaceStrandEdgesAtCutoff
          D hcutoff hextent state) ++
      slabFaceStrandFaceVertices
        (reflectedBentGuardGraftRealizedRightFaceStrandEdgesAtCutoff
          D hcutoff hextent state) =
      reflectedBentGuardGraftPositiveTargetFaceVerticesAtCutoff
        D hcutoff hextent state := by
  rw [slabFaceStrandFaceVertices_eq_projectedEndpoints,
    slabFaceStrandFaceVertices_eq_projectedEndpoints,
    ← List.flatMap_append,
    reflectedBentGuardGraftRealizedPairedProjectedFaceEdgesAtCutoff_eq_target]
  rfl

#print axioms reflectedBentGuardGraftRealizedLeftAssignmentAtCutoff_lookup_eq
#print axioms reflectedBentGuardGraftRealizedRightAssignmentAtCutoff_lookup_eq
#print axioms reflectedBentGuardGraftRealizedLeftFaceStrandEdgesAtCutoff_eq_local
#print axioms reflectedBentGuardGraftRealizedRightFaceStrandEdgesAtCutoff_eq_local
#print axioms reflectedBentGuardGraftRealizedPairedProjectedFaceEdgesAtCutoff_eq_target
#print axioms reflectedBentGuardGraftRealizedPairedFaceVerticesAtCutoff_eq_target

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetGraphBridgeCutoffPersistence
