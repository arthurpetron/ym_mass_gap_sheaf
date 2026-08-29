/-
# Identify the guarded target graph with the standard assignment graph

Lookup in each structurally assembled target assignment returns its local
realized auxiliary.  Consequently the standard global face-strand graph of
both accepted target assignments is exactly the color-preserving projected
graph already used by the marked-face disconnection theorem.

Constructive contract: list recursion, proof irrelevance, and exact graph
equality only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetDisconnection
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableGraphBridge

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetGraphBridge

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetDisconnection
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetEdges
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealization
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableGraphBridge

/-! ## 1. Exact lookup in both assembled assignments -/

theorem reflectedBentGuardGraftRealizedLeftAssignmentAt_eq
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5})
      (linked : {link // link ∈ boundaryCompleteSlabLinks 5}),
      linked ∈ linkedList →
      slabFusionWitnessAssignmentAt linked.1
          (reflectedBentGuardGraftRealizedLeftAssignmentFrom
            D hcutoff hextent state linkedList) =
        reflectedBentGuardGraftRealizedLeftAuxiliary
          D hcutoff hextent state linked
  | [], linked, hmem => False.elim (List.not_mem_nil hmem)
  | head :: rest, linked, hmem => by
      by_cases hsame : head.1 = linked.1
      · have hsubtype : head = linked := Subtype.ext hsame
        subst head
        simp [slabFusionWitnessAssignmentAt,
          reflectedBentGuardGraftRealizedLeftAssignmentFrom]
      · have hrest : linked ∈ rest := by
          rcases List.mem_cons.mp hmem with hhead | htail
          · exact False.elim
              (hsame (congrArg Subtype.val hhead.symm))
          · exact htail
        simp only [reflectedBentGuardGraftRealizedLeftAssignmentFrom,
          slabFusionWitnessAssignmentAt, hsame, if_false]
        exact reflectedBentGuardGraftRealizedLeftAssignmentAt_eq
          D hcutoff hextent state rest linked hrest

theorem reflectedBentGuardGraftRealizedRightAssignmentAt_eq
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5})
      (linked : {link // link ∈ boundaryCompleteSlabLinks 5}),
      linked ∈ linkedList →
      slabFusionWitnessAssignmentAt linked.1
          (reflectedBentGuardGraftRealizedRightAssignmentFrom
            D hcutoff hextent state linkedList) =
        reflectedBentGuardGraftRealizedRightAuxiliary
          D hcutoff hextent state linked
  | [], linked, hmem => False.elim (List.not_mem_nil hmem)
  | head :: rest, linked, hmem => by
      by_cases hsame : head.1 = linked.1
      · have hsubtype : head = linked := Subtype.ext hsame
        subst head
        simp [slabFusionWitnessAssignmentAt,
          reflectedBentGuardGraftRealizedRightAssignmentFrom]
      · have hrest : linked ∈ rest := by
          rcases List.mem_cons.mp hmem with hhead | htail
          · exact False.elim
              (hsame (congrArg Subtype.val hhead.symm))
          · exact htail
        simp only [reflectedBentGuardGraftRealizedRightAssignmentFrom,
          slabFusionWitnessAssignmentAt, hsame, if_false]
        exact reflectedBentGuardGraftRealizedRightAssignmentAt_eq
          D hcutoff hextent state rest linked hrest

/-! ## 2. The standard global graphs equal the classified local graphs -/

def reflectedBentGuardGraftRealizedLeftFaceStrandEdges
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :=
  slabFineFusionWitnessFaceStrandEdges D
    (reflectedBentGuardGraftLeftPhysical D hextent state)
    (reflectedBentGuardGraftRealizedLeftAssignment
      D hcutoff hextent state)
    (reflectedBentGuardGraftRealizedLeftAssignment_mem
      D hcutoff hextent state)

def reflectedBentGuardGraftRealizedRightFaceStrandEdges
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :=
  slabFineFusionWitnessFaceStrandEdges D
    (reflectedBentGuardGraftRightPhysical D hextent state)
    (reflectedBentGuardGraftRealizedRightAssignment
      D hcutoff hextent state)
    (reflectedBentGuardGraftRealizedRightAssignment_mem
      D hcutoff hextent state)

theorem reflectedBentGuardGraftRealizedLeftFaceStrandEdges_eq_local
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftRealizedLeftFaceStrandEdges
        D hcutoff hextent state =
      (boundaryCompleteSlabLinks 5).attach.flatMap
        (reflectedBentGuardGraftRealizedLeftFaceStrandEdgesAt
          D hcutoff hextent state) := by
  have hmem := reflectedBentGuardGraftRealizedLeftAssignmentFrom_mem
    D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach
  rw [List.attach_map_subtype_val] at hmem
  have hfixed :
      slabFusionWitnessAssignmentFaceStrandEdges 1 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (boundaryCompleteSlabLinks 5)
          (reflectedBentGuardGraftRealizedLeftAssignment
            D hcutoff hextent state) hmem =
        (boundaryCompleteSlabLinks 5).attach.flatMap
          (reflectedBentGuardGraftRealizedLeftFaceStrandEdgesAt
            D hcutoff hextent state) := by
    unfold slabFusionWitnessAssignmentFaceStrandEdges
    apply congrArg (fun compiler =>
      (boundaryCompleteSlabLinks 5).attach.flatMap compiler)
    funext linked
    unfold slabFusionWitnessAssignmentFaceStrandEdgesAt
      reflectedBentGuardGraftRealizedLeftFaceStrandEdgesAt
      reflectedBentGuardGraftRealizedLeftAssignment
    have hlookup := reflectedBentGuardGraftRealizedLeftAssignmentAt_eq
      D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach linked
      (List.mem_attach (boundaryCompleteSlabLinks 5) linked)
    exact slabLinkFaceStrandEdges_eq_of_auxiliary_eq _ _ hlookup
  simpa only [reflectedBentGuardGraftRealizedLeftFaceStrandEdges,
    slabFineFusionWitnessFaceStrandEdges, hcutoff, hextent] using hfixed

theorem reflectedBentGuardGraftRealizedRightFaceStrandEdges_eq_local
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftRealizedRightFaceStrandEdges
        D hcutoff hextent state =
      (boundaryCompleteSlabLinks 5).attach.flatMap
        (reflectedBentGuardGraftRealizedRightFaceStrandEdgesAt
          D hcutoff hextent state) := by
  have hmem := reflectedBentGuardGraftRealizedRightAssignmentFrom_mem
    D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach
  rw [List.attach_map_subtype_val] at hmem
  have hfixed :
      slabFusionWitnessAssignmentFaceStrandEdges 1 5
          (reflectedBentGuardGraftRightPhysical D hextent state)
          (boundaryCompleteSlabLinks 5)
          (reflectedBentGuardGraftRealizedRightAssignment
            D hcutoff hextent state) hmem =
        (boundaryCompleteSlabLinks 5).attach.flatMap
          (reflectedBentGuardGraftRealizedRightFaceStrandEdgesAt
            D hcutoff hextent state) := by
    unfold slabFusionWitnessAssignmentFaceStrandEdges
    apply congrArg (fun compiler =>
      (boundaryCompleteSlabLinks 5).attach.flatMap compiler)
    funext linked
    unfold slabFusionWitnessAssignmentFaceStrandEdgesAt
      reflectedBentGuardGraftRealizedRightFaceStrandEdgesAt
      reflectedBentGuardGraftRealizedRightAssignment
    have hlookup := reflectedBentGuardGraftRealizedRightAssignmentAt_eq
      D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach linked
      (List.mem_attach (boundaryCompleteSlabLinks 5) linked)
    exact slabLinkFaceStrandEdges_eq_of_auxiliary_eq _ _ hlookup
  simpa only [reflectedBentGuardGraftRealizedRightFaceStrandEdges,
    slabFineFusionWitnessFaceStrandEdges, hcutoff, hextent] using hfixed

theorem reflectedBentGuardGraftRealizedPairedProjectedFaceEdges_eq_target
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    slabProjectedFaceEdges
        (reflectedBentGuardGraftRealizedLeftFaceStrandEdges
          D hcutoff hextent state) ++
      slabProjectedFaceEdges
        (reflectedBentGuardGraftRealizedRightFaceStrandEdges
          D hcutoff hextent state) =
      reflectedBentGuardGraftPositiveTargetProjectedFaceEdges
        D hcutoff hextent state := by
  rw [reflectedBentGuardGraftRealizedLeftFaceStrandEdges_eq_local,
    reflectedBentGuardGraftRealizedRightFaceStrandEdges_eq_local]
  unfold reflectedBentGuardGraftPositiveTargetProjectedFaceEdges
    reflectedBentGuardGraftRealizedLeftProjectedFaceEdges
    reflectedBentGuardGraftRealizedRightProjectedFaceEdges
    reflectedBentGuardGraftRealizedLeftProjectedFaceEdgesAt
    reflectedBentGuardGraftRealizedRightProjectedFaceEdgesAt
    slabProjectedFaceEdges
  simp only [List.map_flatMap]

theorem slabFaceStrandFaceVertices_eq_projectedEndpoints
    {physical : SlabLabelling}
    (edges : List (SlabFaceStrandEdge physical)) :
    slabFaceStrandFaceVertices edges =
      (slabProjectedFaceEdges edges).flatMap fun edge =>
        [edge.source, edge.target] := by
  induction edges with
  | nil => rfl
  | cons edge rest ih =>
      change
        List.map (fun copy => copy.faceId)
            ([edge.source, edge.target] ++ slabFaceStrandVertices rest) =
          [edge.source.faceId, edge.target.faceId] ++
            (slabProjectedFaceEdges rest).flatMap fun edge =>
              [edge.source, edge.target]
      rw [List.map_append]
      change
        [edge.source.faceId, edge.target.faceId] ++
            slabFaceStrandFaceVertices rest =
          [edge.source.faceId, edge.target.faceId] ++
            (slabProjectedFaceEdges rest).flatMap fun edge =>
              [edge.source, edge.target]
      rw [ih]

theorem reflectedBentGuardGraftRealizedPairedFaceVertices_eq_target
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    slabFaceStrandFaceVertices
        (reflectedBentGuardGraftRealizedLeftFaceStrandEdges
          D hcutoff hextent state) ++
      slabFaceStrandFaceVertices
        (reflectedBentGuardGraftRealizedRightFaceStrandEdges
          D hcutoff hextent state) =
      reflectedBentGuardGraftPositiveTargetFaceVertices
        D hcutoff hextent state := by
  rw [slabFaceStrandFaceVertices_eq_projectedEndpoints,
    slabFaceStrandFaceVertices_eq_projectedEndpoints,
    ← List.flatMap_append,
    reflectedBentGuardGraftRealizedPairedProjectedFaceEdges_eq_target]
  rfl

#print axioms reflectedBentGuardGraftRealizedLeftAssignmentAt_eq
#print axioms reflectedBentGuardGraftRealizedRightAssignmentAt_eq
#print axioms reflectedBentGuardGraftRealizedLeftFaceStrandEdges_eq_local
#print axioms reflectedBentGuardGraftRealizedRightFaceStrandEdges_eq_local
#print axioms reflectedBentGuardGraftRealizedPairedProjectedFaceEdges_eq_target
#print axioms slabFaceStrandFaceVertices_eq_projectedEndpoints
#print axioms reflectedBentGuardGraftRealizedPairedFaceVertices_eq_target

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetGraphBridge
