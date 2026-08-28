/-
# Marked-face disconnection in the native outward Y/Z target graph

Every basis-tagged target edge stays within the Y surface or within the Z
surface.  Color a face identifier by membership in the Y surface.  Literal
projected adjacency preserves that color, hence so does every Type-valued
finite graph chain.  The marked Y root has color true and the marked Z target
has color false, so no chain can connect them.

This contracts the local native-tree pairing mathematics into global
marked-face disconnection for the basis-tagged graph.  The remaining bridge
is observational: the existing success predicate still constructs its graph
from the equal-rank left assignment rather than this native target tag.

Constructive contract: Boolean color transport and structural recursion on
an explicit `ChainIn`; no choice, `Classical`, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedFaceSupportRefinement
import YMGap.Continuum.Z4OutwardYZEdgeTouchSlabNativeTargetEdges

namespace YMGap.Continuum.Z4OutwardYZEdgeTouchSlabNativeTargetDisconnection

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSupportRefinement
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier
open YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabNativeTargetEdges
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabWholeProductPositivity

/-! ## 1. A two-color invariant on literal projected edges -/

def outwardYZNativeTargetProjectedFaceEdges :
    List SlabProjectedFaceEdge :=
  slabProjectedFaceEdges outwardYZNativeTargetFaceStrandEdges

def outwardYZNativeTargetFaceVertices : List Nat :=
  slabFaceStrandFaceVertices outwardYZNativeTargetFaceStrandEdges

def outwardYZNativeTargetFaceAdjacentB (left right : Nat) : Bool :=
  slabProjectedFaceAdjacentB outwardYZNativeTargetProjectedFaceEdges
    left right

def outwardYZFaceColorB (faceId : Nat) : Bool :=
  decide (slabPlaquetteAt 5 faceId ∈ outwardYSurface)

theorem outwardZSurface_face_not_mem_outwardYSurface
    {face : Z4Plaq} (hz : face ∈ outwardZSurface) :
    face ∉ outwardYSurface := by
  intro hy
  have hcross := (List.nodup_append.mp outwardYZSurface_nodup).2.2
  exact hcross face hy face hz rfl

theorem outwardYZNativeTargetFaceStrandEdge_color_eq
    (edge : SlabFaceStrandEdge outwardYZSwitchLeftPhysical)
    (hedge : edge ∈ outwardYZNativeTargetFaceStrandEdges) :
    outwardYZFaceColorB edge.source.faceId =
      outwardYZFaceColorB edge.target.faceId := by
  have hside := outwardYZNativeTargetFaceStrandEdge_same_side edge hedge
  rcases hside with hY | hZ
  · simp [outwardYZFaceColorB, hY.1, hY.2]
  · have hsourceNotY :=
      outwardZSurface_face_not_mem_outwardYSurface hZ.1
    have htargetNotY :=
      outwardZSurface_face_not_mem_outwardYSurface hZ.2
    simp [outwardYZFaceColorB, hsourceNotY, htargetNotY]

theorem outwardYZNativeTargetFaceAdjacentB_color_eq
    {left right : Nat}
    (hadj : outwardYZNativeTargetFaceAdjacentB left right = true) :
    outwardYZFaceColorB left = outwardYZFaceColorB right := by
  obtain ⟨projected, hprojected, horientation⟩ :=
    slabProjectedFaceAdjacentEdgeWitness left right
      outwardYZNativeTargetProjectedFaceEdges hadj
  unfold outwardYZNativeTargetProjectedFaceEdges at hprojected
  obtain ⟨edge, hedge, rfl⟩ := List.mem_map.mp hprojected
  have hcolor :=
    outwardYZNativeTargetFaceStrandEdge_color_eq edge hedge
  cases horientation with
  | inl hforward =>
      rw [← hforward.1, ← hforward.2]
      exact hcolor
  | inr hreverse =>
      rw [← hreverse.2, ← hreverse.1]
      exact hcolor.symm

/-! ## 2. Color transport along every finite graph chain -/

theorem outwardYZNativeTargetChain_color_eq
    {first last : Nat}
    (path : ChainIn outwardYZNativeTargetFaceAdjacentB
      outwardYZNativeTargetFaceVertices first last) :
    outwardYZFaceColorB first = outwardYZFaceColorB last := by
  induction path with
  | refl => rfl
  | step hadj _ rest ih =>
      exact (outwardYZNativeTargetFaceAdjacentB_color_eq hadj).trans ih

theorem outwardYZSwitchRootFace_color :
    outwardYZFaceColorB outwardYZSwitchRootFaceId = true := by
  have hslab : outwardYQueryFace ∈ boundaryCompleteSlabPlaquettes 5 :=
    outwardYZSwitchSurface_subset_slab_five
      outwardYQueryFace outwardYQueryFace_mem_YZ
  unfold outwardYZFaceColorB outwardYZSwitchRootFaceId
  rw [slabPlaquetteAt_faceIdOfPlaquette hslab]
  exact decide_eq_true outwardYQueryFace_mem_Y

theorem outwardYZSwitchTargetFace_color :
    outwardYZFaceColorB outwardYZSwitchTargetFaceId = false := by
  have hslab : outwardZQueryFace ∈ boundaryCompleteSlabPlaquettes 5 :=
    outwardYZSwitchSurface_subset_slab_five
      outwardZQueryFace outwardZQueryFace_mem_YZ
  unfold outwardYZFaceColorB outwardYZSwitchTargetFaceId
  rw [slabPlaquetteAt_faceIdOfPlaquette hslab]
  exact decide_eq_false outwardZQueryFace_not_mem_Y

/-! ## 3. Global marked-face disconnection -/

def outwardYZNativeTarget_noMarkedFaceChain :
    ChainIn outwardYZNativeTargetFaceAdjacentB
      outwardYZNativeTargetFaceVertices
      outwardYZSwitchRootFaceId outwardYZSwitchTargetFaceId -> False :=
  fun path => by
    have hcolor := outwardYZNativeTargetChain_color_eq path
    rw [outwardYZSwitchRootFace_color,
      outwardYZSwitchTargetFace_color] at hcolor
    cases hcolor

structure OutwardYZNativeTargetDisconnectionCertificate : Type where
  basisTaggedEdges : OutwardYZNativeTargetBasisTaggedEdgeCertificate
  rootColor : outwardYZFaceColorB outwardYZSwitchRootFaceId = true
  targetColor : outwardYZFaceColorB outwardYZSwitchTargetFaceId = false
  markedDisconnected : ChainIn outwardYZNativeTargetFaceAdjacentB
    outwardYZNativeTargetFaceVertices
    outwardYZSwitchRootFaceId outwardYZSwitchTargetFaceId -> False

def outwardYZNativeTargetDisconnectionCertificate :
    OutwardYZNativeTargetDisconnectionCertificate :=
  { basisTaggedEdges := outwardYZNativeTargetBasisTaggedEdgeCertificate
    rootColor := outwardYZSwitchRootFace_color
    targetColor := outwardYZSwitchTargetFace_color
    markedDisconnected := outwardYZNativeTarget_noMarkedFaceChain }

#print axioms outwardZSurface_face_not_mem_outwardYSurface
#print axioms outwardYZNativeTargetFaceStrandEdge_color_eq
#print axioms outwardYZNativeTargetFaceAdjacentB_color_eq
#print axioms outwardYZNativeTargetChain_color_eq
#print axioms outwardYZNativeTarget_noMarkedFaceChain
#print axioms outwardYZNativeTargetDisconnectionCertificate

end YMGap.Continuum.Z4OutwardYZEdgeTouchSlabNativeTargetDisconnection
