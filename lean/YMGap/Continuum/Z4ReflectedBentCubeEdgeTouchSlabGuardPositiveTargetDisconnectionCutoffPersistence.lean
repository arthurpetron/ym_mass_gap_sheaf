/-
# Marked-face disconnection at every representation cutoff

Every projected edge of the ambient accepted positive target preserves the
near/far face color.  Boolean adjacency and every explicit finite graph chain
therefore preserve that color.  The marked root is near and the marked target
is far, so no chain connects them at any cutoff at least one.

Constructive contract: finite projected edges and structural recursion on a
`ChainIn`; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetDisconnection
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetEdgesCutoffPersistence

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetDisconnectionCutoffPersistence

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSupportRefinement
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetDisconnection
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetEdges
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetEdgesCutoffPersistence

/-! ## 1. The ambient finite projected graph -/

def reflectedBentGuardGraftPositiveTargetFaceVerticesAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) : List Nat :=
  (reflectedBentGuardGraftPositiveTargetProjectedFaceEdgesAtCutoff
    D hcutoff hextent state).flatMap fun edge =>
      [edge.source, edge.target]

def reflectedBentGuardGraftPositiveTargetFaceAdjacentBAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (left right : Nat) : Bool :=
  slabProjectedFaceAdjacentB
    (reflectedBentGuardGraftPositiveTargetProjectedFaceEdgesAtCutoff
      D hcutoff hextent state) left right

theorem reflectedBentGuardGraftPositiveTargetFaceAdjacentBAtCutoff_color_eq
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    {left right : Nat}
    (hadj : reflectedBentGuardGraftPositiveTargetFaceAdjacentBAtCutoff
      D hcutoff hextent state left right = true) :
    reflectedBentGuardTargetFaceColorB left =
      reflectedBentGuardTargetFaceColorB right := by
  obtain ⟨projected, hprojected, horientation⟩ :=
    slabProjectedFaceAdjacentEdgeWitness left right
      (reflectedBentGuardGraftPositiveTargetProjectedFaceEdgesAtCutoff
        D hcutoff hextent state) hadj
  have hcolor :=
    reflectedBentGuardGraftPositiveTargetProjectedFaceEdge_color_eq_at_cutoff
      D hcutoff hextent state projected hprojected
  cases horientation with
  | inl hforward =>
      rw [← hforward.1, ← hforward.2]
      exact hcolor
  | inr hreverse =>
      rw [← hreverse.2, ← hreverse.1]
      exact hcolor.symm

theorem reflectedBentGuardGraftPositiveTargetChainAtCutoff_color_eq
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    {first last : Nat}
    (path : ChainIn
      (reflectedBentGuardGraftPositiveTargetFaceAdjacentBAtCutoff
        D hcutoff hextent state)
      (reflectedBentGuardGraftPositiveTargetFaceVerticesAtCutoff
        D hcutoff hextent state) first last) :
    reflectedBentGuardTargetFaceColorB first =
      reflectedBentGuardTargetFaceColorB last := by
  induction path with
  | refl => rfl
  | step hadj _ rest ih =>
      exact
        (reflectedBentGuardGraftPositiveTargetFaceAdjacentBAtCutoff_color_eq
          D hcutoff hextent state hadj).trans ih

/-! ## 2. Opposite endpoint colors exclude a marked chain -/

def reflectedBentGuardGraftPositiveTarget_noMarkedFaceChainAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ChainIn
      (reflectedBentGuardGraftPositiveTargetFaceAdjacentBAtCutoff
        D hcutoff hextent state)
      (reflectedBentGuardGraftPositiveTargetFaceVerticesAtCutoff
        D hcutoff hextent state)
      reflectedBentRootFaceId reflectedBentTargetFaceId → False :=
  fun path => by
    have hcolor :=
      reflectedBentGuardGraftPositiveTargetChainAtCutoff_color_eq
        D hcutoff hextent state path
    rw [reflectedBentGuardGraftPositiveTargetRootFace_color,
      reflectedBentGuardGraftPositiveTargetTargetFace_color] at hcolor
    cases hcolor

/-! ## 3. Data-bearing all-cutoff disconnection certificate -/

structure ReflectedBentGuardGraftPositiveTargetDisconnectionAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) : Type where
  targetEdges : List SlabProjectedFaceEdge
  targetEdges_eq : targetEdges =
    reflectedBentGuardGraftPositiveTargetProjectedFaceEdgesAtCutoff
      D hcutoff hextent state
  everyTargetEdgePreservesColor : ∀ edge, edge ∈ targetEdges →
    reflectedBentGuardTargetFaceColorB edge.source =
      reflectedBentGuardTargetFaceColorB edge.target
  markedDisconnected : ChainIn
    (reflectedBentGuardGraftPositiveTargetFaceAdjacentBAtCutoff
      D hcutoff hextent state)
    (reflectedBentGuardGraftPositiveTargetFaceVerticesAtCutoff
      D hcutoff hextent state)
    reflectedBentRootFaceId reflectedBentTargetFaceId → False

def reflectedBentGuardGraftPositiveTargetDisconnectionAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ReflectedBentGuardGraftPositiveTargetDisconnectionAtCutoff
      D hcutoff hextent state where
  targetEdges :=
    reflectedBentGuardGraftPositiveTargetProjectedFaceEdgesAtCutoff
      D hcutoff hextent state
  targetEdges_eq := rfl
  everyTargetEdgePreservesColor :=
    reflectedBentGuardGraftPositiveTargetProjectedFaceEdge_color_eq_at_cutoff
      D hcutoff hextent state
  markedDisconnected :=
    reflectedBentGuardGraftPositiveTarget_noMarkedFaceChainAtCutoff
      D hcutoff hextent state

#print axioms reflectedBentGuardGraftPositiveTargetFaceAdjacentBAtCutoff_color_eq
#print axioms reflectedBentGuardGraftPositiveTargetChainAtCutoff_color_eq
#print axioms reflectedBentGuardGraftPositiveTarget_noMarkedFaceChainAtCutoff
#print axioms reflectedBentGuardGraftPositiveTargetDisconnectionAtCutoff

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetDisconnectionCutoffPersistence
