/-
# Marked-face disconnection in the realized positive guarded target

Every projected strand edge of the accepted two-replica target preserves the
near-lobe Boolean color.  Therefore adjacency and every explicit finite graph
chain preserve that color.  The marked root is near and the marked reflected
target is far, so the realized positive target disconnects them.

Constructive contract: finite projected edges and structural recursion on a
`ChainIn`; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedFaceSupportRefinement
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetEdges

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetDisconnection

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSupportRefinement
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchCutCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetEdges
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile

/-! ## 1. The finite projected graph -/

def reflectedBentGuardGraftPositiveTargetFaceVertices
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) : List Nat :=
  (reflectedBentGuardGraftPositiveTargetProjectedFaceEdges
    D hcutoff hextent state).flatMap fun edge =>
      [edge.source, edge.target]

def reflectedBentGuardGraftPositiveTargetFaceAdjacentB
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (left right : Nat) : Bool :=
  slabProjectedFaceAdjacentB
    (reflectedBentGuardGraftPositiveTargetProjectedFaceEdges
      D hcutoff hextent state) left right

theorem reflectedBentGuardGraftPositiveTargetFaceAdjacentB_color_eq
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    {left right : Nat}
    (hadj : reflectedBentGuardGraftPositiveTargetFaceAdjacentB
      D hcutoff hextent state left right = true) :
    reflectedBentGuardTargetFaceColorB left =
      reflectedBentGuardTargetFaceColorB right := by
  obtain ⟨projected, hprojected, horientation⟩ :=
    slabProjectedFaceAdjacentEdgeWitness left right
      (reflectedBentGuardGraftPositiveTargetProjectedFaceEdges
        D hcutoff hextent state) hadj
  have hcolor :=
    reflectedBentGuardGraftPositiveTargetProjectedFaceEdge_color_eq
      D hcutoff hextent state projected hprojected
  cases horientation with
  | inl hforward =>
      rw [← hforward.1, ← hforward.2]
      exact hcolor
  | inr hreverse =>
      rw [← hreverse.2, ← hreverse.1]
      exact hcolor.symm

theorem reflectedBentGuardGraftPositiveTargetChain_color_eq
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    {first last : Nat}
    (path : ChainIn
      (reflectedBentGuardGraftPositiveTargetFaceAdjacentB
        D hcutoff hextent state)
      (reflectedBentGuardGraftPositiveTargetFaceVertices
        D hcutoff hextent state) first last) :
    reflectedBentGuardTargetFaceColorB first =
      reflectedBentGuardTargetFaceColorB last := by
  induction path with
  | refl => rfl
  | step hadj _ rest ih =>
      exact (reflectedBentGuardGraftPositiveTargetFaceAdjacentB_color_eq
        D hcutoff hextent state hadj).trans ih

/-! ## 2. The marked endpoints have opposite colors -/

theorem reflectedBentGuardGraftPositiveTargetRootFace_color :
    reflectedBentGuardTargetFaceColorB reflectedBentRootFaceId = true := by
  have hslab : reflectedBentRootPlaquette ∈
      boundaryCompleteSlabPlaquettes 5 :=
    YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile.reflectedBentSwitchSurface_subset_slab_five
      reflectedBentRootPlaquette
      (List.mem_append.mpr (Or.inl reflectedBentRoot_mem))
  unfold reflectedBentGuardTargetFaceColorB reflectedBentRootFaceId
    SlabBinarySupportConnectedCarrier.rootFaceId
    reflectedBentBinaryConnectedCarrier
  rw [slabPlaquetteAt_faceIdOfPlaquette hslab]
  exact decide_eq_true reflectedBentRoot_mem

theorem reflectedBentGuardGraftPositiveTargetTargetFace_color :
    reflectedBentGuardTargetFaceColorB reflectedBentTargetFaceId = false := by
  have hslab : reflectedBentTargetPlaquette ∈
      boundaryCompleteSlabPlaquettes 5 :=
    YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile.reflectedBentSwitchSurface_subset_slab_five
      reflectedBentTargetPlaquette
      (List.mem_append.mpr (Or.inr reflectedBentTarget_mem))
  have hnotNear : reflectedBentTargetPlaquette ∉ reflectedBentNearSurface :=
    reflectedBentGuardFarFace_not_near reflectedBentTarget_mem
  unfold reflectedBentGuardTargetFaceColorB reflectedBentTargetFaceId
    SlabBinarySupportConnectedCarrier.targetFaceId
    reflectedBentBinaryConnectedCarrier
  rw [slabPlaquetteAt_faceIdOfPlaquette hslab]
  exact decide_eq_false hnotNear

def reflectedBentGuardGraftPositiveTarget_noMarkedFaceChain
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ChainIn
      (reflectedBentGuardGraftPositiveTargetFaceAdjacentB
        D hcutoff hextent state)
      (reflectedBentGuardGraftPositiveTargetFaceVertices
        D hcutoff hextent state)
      reflectedBentRootFaceId reflectedBentTargetFaceId → False :=
  fun path => by
    have hcolor := reflectedBentGuardGraftPositiveTargetChain_color_eq
      D hcutoff hextent state path
    rw [reflectedBentGuardGraftPositiveTargetRootFace_color,
      reflectedBentGuardGraftPositiveTargetTargetFace_color] at hcolor
    cases hcolor

/-! ## 3. Data-bearing finite disconnection certificate -/

structure ReflectedBentGuardGraftPositiveTargetDisconnectionCertificate
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) : Type where
  targetEdges : List SlabProjectedFaceEdge
  targetEdges_eq : targetEdges =
    reflectedBentGuardGraftPositiveTargetProjectedFaceEdges
      D hcutoff hextent state
  everyTargetEdgePreservesColor : ∀ edge, edge ∈ targetEdges →
    reflectedBentGuardTargetFaceColorB edge.source =
      reflectedBentGuardTargetFaceColorB edge.target
  markedDisconnected : ChainIn
    (reflectedBentGuardGraftPositiveTargetFaceAdjacentB
      D hcutoff hextent state)
    (reflectedBentGuardGraftPositiveTargetFaceVertices
      D hcutoff hextent state)
    reflectedBentRootFaceId reflectedBentTargetFaceId → False

def reflectedBentGuardGraftPositiveTargetDisconnectionCertificate
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ReflectedBentGuardGraftPositiveTargetDisconnectionCertificate
      D hcutoff hextent state where
  targetEdges := reflectedBentGuardGraftPositiveTargetProjectedFaceEdges
    D hcutoff hextent state
  targetEdges_eq := rfl
  everyTargetEdgePreservesColor :=
    reflectedBentGuardGraftPositiveTargetProjectedFaceEdge_color_eq
      D hcutoff hextent state
  markedDisconnected :=
    reflectedBentGuardGraftPositiveTarget_noMarkedFaceChain
      D hcutoff hextent state

#print axioms reflectedBentGuardGraftPositiveTargetFaceAdjacentB_color_eq
#print axioms reflectedBentGuardGraftPositiveTargetChain_color_eq
#print axioms reflectedBentGuardGraftPositiveTarget_noMarkedFaceChain
#print axioms reflectedBentGuardGraftPositiveTargetDisconnectionCertificate

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetDisconnection
