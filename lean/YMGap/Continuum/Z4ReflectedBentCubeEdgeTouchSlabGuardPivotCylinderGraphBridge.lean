/-
# Standard observable graph of an arbitrary pivot-cylinder target

The pivot-cylinder disconnection theorem uses a structurally aligned graph
over the written link list.  Observable success uses the standard global
face-strand graph of the realized assignment.  This module proves that the
two presentations agree for every dependent target column.

Constructive contract: list recursion, proof irrelevance, and exact graph
equality only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderDisconnection
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderPivotLookup
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetGraphBridge

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderGraphBridge

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSupportRefinement
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderAbstractGraph
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderGraph
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderLocalEdges
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderRealization
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetDisconnection
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetEdges
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetGraphBridge
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardTargetAssignmentRealizationCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabWholeProductPositivity

/-- Standard projected graph of the recursively realized left assignment on
an arbitrary written link list. -/
def reflectedBentGuardGraftStandardLeftProjectedFaceEdgesFromTargetAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked)) : List SlabProjectedFaceEdge :=
  let assignment :=
    reflectedBentGuardGraftRealizedLeftAssignmentFromTargetAtCutoff
      D hcutoff hextent state linkedList target
  let hmem :=
    reflectedBentGuardGraftRealizedLeftAssignmentFromTargetAtCutoff_mem
      D hcutoff hextent state linkedList target
  slabProjectedFaceEdges
    (slabFusionWitnessAssignmentFaceStrandEdges D.cutoff 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      (linkedList.map Subtype.val) assignment hmem)

/-- Standard projected graph of the recursively realized right assignment on
an arbitrary written link list. -/
def reflectedBentGuardGraftStandardRightProjectedFaceEdgesFromTargetAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked)) : List SlabProjectedFaceEdge :=
  let assignment :=
    reflectedBentGuardGraftRealizedRightAssignmentFromTargetAtCutoff
      D hcutoff hextent state linkedList target
  let hmem :=
    reflectedBentGuardGraftRealizedRightAssignmentFromTargetAtCutoff_mem
      D hcutoff hextent state linkedList target
  slabProjectedFaceEdges
    (slabFusionWitnessAssignmentFaceStrandEdges D.cutoff 5
      (reflectedBentGuardGraftRightPhysical D hextent state)
      (linkedList.map Subtype.val) assignment hmem)

/-- Every edge in the standard global graph of the left realized assignment
preserves the separating near/far color once the pivot coordinate is pinned. -/
theorem reflectedBentGuardGraftStandardLeftProjectedFaceEdge_color_eq
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked))
    (hpinned : ReflectedBentGuardGraftPivotPinnedAtCutoff
      D hcutoff hextent state linkedList target)
    (projected : SlabProjectedFaceEdge)
    (hprojected : projected ∈
      reflectedBentGuardGraftStandardLeftProjectedFaceEdgesFromTargetAtCutoff
        D hcutoff hextent state linkedList target) :
    reflectedBentGuardTargetFaceColorB projected.source =
      reflectedBentGuardTargetFaceColorB projected.target := by
  unfold reflectedBentGuardGraftStandardLeftProjectedFaceEdgesFromTargetAtCutoff
    slabProjectedFaceEdges at hprojected
  obtain ⟨edge, hedge, rfl⟩ := List.mem_map.mp hprojected
  unfold slabFusionWitnessAssignmentFaceStrandEdges at hedge
  obtain ⟨linked, _, hlocal⟩ := List.mem_flatMap.mp hedge
  unfold slabFusionWitnessAssignmentFaceStrandEdgesAt at hlocal
  unfold slabLinkFaceStrandEdges at hlocal
  obtain ⟨terminal, _, rfl⟩ := List.mem_map.mp hlocal
  let fullLinked : {link // link ∈ boundaryCompleteSlabLinks 5} :=
    ⟨linked.1, by
      obtain ⟨original, _, heq⟩ := List.mem_map.mp linked.2
      exact heq ▸ original.2⟩
  apply reflectedBentGuardGraftLeftTerminalForAuxiliary_color_eq_at_cutoff
    D hcutoff hextent state fullLinked
      (slabFusionWitnessAssignmentAt linked.1
        (reflectedBentGuardGraftRealizedLeftAssignmentFromTargetAtCutoff
          D hcutoff hextent state linkedList target))
      (slabFusionWitnessAssignmentAt_mem_local D.cutoff 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        (linkedList.map Subtype.val)
        (reflectedBentGuardGraftRealizedLeftAssignmentFromTargetAtCutoff
          D hcutoff hextent state linkedList target)
        (reflectedBentGuardGraftRealizedLeftAssignmentFromTargetAtCutoff_mem
          D hcutoff hextent state linkedList target)
        linked.1 linked.2)
  intro hpivot
  have hlookup :=
    reflectedBentGuardGraftRealizedLeftAssignmentFromTargetAtCutoff_pivot_lookup_eq
      D hcutoff hextent state linkedList target hpinned
  have hfull : fullLinked = reflectedBentSwitchPivotLinked :=
    Subtype.ext hpivot
  change linked.1 = reflectedBentSwitchPivot at hpivot
  rw [hpivot]
  simpa only [hfull] using hlookup

/-- The right realized assignment preserves the same color for every target
column; no pivot hypothesis is required. -/
theorem reflectedBentGuardGraftStandardRightProjectedFaceEdge_color_eq
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked))
    (projected : SlabProjectedFaceEdge)
    (hprojected : projected ∈
      reflectedBentGuardGraftStandardRightProjectedFaceEdgesFromTargetAtCutoff
        D hcutoff hextent state linkedList target) :
    reflectedBentGuardTargetFaceColorB projected.source =
      reflectedBentGuardTargetFaceColorB projected.target := by
  unfold reflectedBentGuardGraftStandardRightProjectedFaceEdgesFromTargetAtCutoff
    slabProjectedFaceEdges at hprojected
  obtain ⟨edge, hedge, rfl⟩ := List.mem_map.mp hprojected
  unfold slabFusionWitnessAssignmentFaceStrandEdges at hedge
  obtain ⟨linked, _, hlocal⟩ := List.mem_flatMap.mp hedge
  unfold slabFusionWitnessAssignmentFaceStrandEdgesAt at hlocal
  unfold slabLinkFaceStrandEdges at hlocal
  obtain ⟨terminal, _, rfl⟩ := List.mem_map.mp hlocal
  let fullLinked : {link // link ∈ boundaryCompleteSlabLinks 5} :=
    ⟨linked.1, by
      obtain ⟨original, _, heq⟩ := List.mem_map.mp linked.2
      exact heq ▸ original.2⟩
  exact reflectedBentGuardGraftRightTerminalForAuxiliary_color_eq_at_cutoff
    D hextent state fullLinked
      (slabFusionWitnessAssignmentAt linked.1
        (reflectedBentGuardGraftRealizedRightAssignmentFromTargetAtCutoff
          D hcutoff hextent state linkedList target))
      (slabFusionWitnessAssignmentAt_mem_local D.cutoff 5
        (reflectedBentGuardGraftRightPhysical D hextent state)
        (linkedList.map Subtype.val)
        (reflectedBentGuardGraftRealizedRightAssignmentFromTargetAtCutoff
          D hcutoff hextent state linkedList target)
        (reflectedBentGuardGraftRealizedRightAssignmentFromTargetAtCutoff_mem
          D hcutoff hextent state linkedList target)
        linked.1 linked.2)
      terminal

/-! ## The complete standard graph has no marked-face chain -/

def reflectedBentGuardGraftStandardProjectedFaceEdgesFromTargetAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked)) : List SlabProjectedFaceEdge :=
  reflectedBentGuardGraftStandardLeftProjectedFaceEdgesFromTargetAtCutoff
      D hcutoff hextent state linkedList target ++
    reflectedBentGuardGraftStandardRightProjectedFaceEdgesFromTargetAtCutoff
      D hcutoff hextent state linkedList target

def reflectedBentGuardGraftStandardFaceVerticesFromTargetAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked)) : List Nat :=
  (reflectedBentGuardGraftStandardProjectedFaceEdgesFromTargetAtCutoff
    D hcutoff hextent state linkedList target).flatMap fun edge =>
      [edge.source, edge.target]

def reflectedBentGuardGraftStandardFaceAdjacentBFromTargetAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked)) : Nat → Nat → Bool :=
  slabProjectedFaceAdjacentB
    (reflectedBentGuardGraftStandardProjectedFaceEdgesFromTargetAtCutoff
      D hcutoff hextent state linkedList target)

theorem reflectedBentGuardGraftStandardFaceAdjacentBFromTarget_color_eq
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked))
    (hpinned : ReflectedBentGuardGraftPivotPinnedAtCutoff
      D hcutoff hextent state linkedList target)
    {left right : Nat}
    (hadj : reflectedBentGuardGraftStandardFaceAdjacentBFromTargetAtCutoff
      D hcutoff hextent state linkedList target left right = true) :
    reflectedBentGuardTargetFaceColorB left =
      reflectedBentGuardTargetFaceColorB right := by
  obtain ⟨projected, hprojected, horientation⟩ :=
    slabProjectedFaceAdjacentEdgeWitness left right
      (reflectedBentGuardGraftStandardProjectedFaceEdgesFromTargetAtCutoff
        D hcutoff hextent state linkedList target) hadj
  have hcolor : reflectedBentGuardTargetFaceColorB projected.source =
      reflectedBentGuardTargetFaceColorB projected.target := by
    rcases List.mem_append.mp hprojected with hleft | hright
    · exact reflectedBentGuardGraftStandardLeftProjectedFaceEdge_color_eq
        D hcutoff hextent state linkedList target hpinned projected hleft
    · exact reflectedBentGuardGraftStandardRightProjectedFaceEdge_color_eq
        D hcutoff hextent state linkedList target projected hright
  cases horientation with
  | inl hforward =>
      rw [← hforward.1, ← hforward.2]
      exact hcolor
  | inr hreverse =>
      rw [← hreverse.2, ← hreverse.1]
      exact hcolor.symm

theorem reflectedBentGuardGraftStandardChainFromTarget_color_eq
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked))
    (hpinned : ReflectedBentGuardGraftPivotPinnedAtCutoff
      D hcutoff hextent state linkedList target)
    {first last : Nat}
    (path : ChainIn
      (reflectedBentGuardGraftStandardFaceAdjacentBFromTargetAtCutoff
        D hcutoff hextent state linkedList target)
      (reflectedBentGuardGraftStandardFaceVerticesFromTargetAtCutoff
        D hcutoff hextent state linkedList target) first last) :
    reflectedBentGuardTargetFaceColorB first =
      reflectedBentGuardTargetFaceColorB last := by
  induction path with
  | refl => rfl
  | step hadj _ rest ih =>
      exact
        (reflectedBentGuardGraftStandardFaceAdjacentBFromTarget_color_eq
          D hcutoff hextent state linkedList target hpinned hadj).trans ih

theorem reflectedBentGuardGraftStandardTarget_noMarkedFaceChainAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked))
    (hpinned : ReflectedBentGuardGraftPivotPinnedAtCutoff
      D hcutoff hextent state linkedList target) :
    ChainIn
      (reflectedBentGuardGraftStandardFaceAdjacentBFromTargetAtCutoff
        D hcutoff hextent state linkedList target)
      (reflectedBentGuardGraftStandardFaceVerticesFromTargetAtCutoff
        D hcutoff hextent state linkedList target)
      reflectedBentRootFaceId reflectedBentTargetFaceId → False :=
  fun path => by
    have hcolor :=
      reflectedBentGuardGraftStandardChainFromTarget_color_eq
        D hcutoff hextent state linkedList target hpinned path
    rw [reflectedBentGuardGraftPositiveTargetRootFace_color,
      reflectedBentGuardGraftPositiveTargetTargetFace_color] at hcolor
    cases hcolor

#print axioms reflectedBentGuardGraftStandardLeftProjectedFaceEdge_color_eq
#print axioms reflectedBentGuardGraftStandardRightProjectedFaceEdge_color_eq
#print axioms reflectedBentGuardGraftStandardTarget_noMarkedFaceChainAtCutoff

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderGraphBridge
