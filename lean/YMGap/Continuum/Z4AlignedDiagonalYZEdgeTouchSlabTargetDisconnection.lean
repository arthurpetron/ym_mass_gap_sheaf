/-
# Marked-face disconnection in the aligned target graph

Every selected target edge stays within the near surface or within the far
surface.  Color a face identifier by near-surface membership.  Literal
projected adjacency preserves that color, hence so does every Type-valued
finite graph chain.  The marked near root is true and the marked far target
is false, so no chain connects them.

Constructive contract: Boolean color transport and structural recursion on
an explicit `ChainIn`; no choice, `Classical`, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedFaceSupportRefinement
import YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetEdges

namespace YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetDisconnection

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSupportRefinement
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchCutCarrier
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetEdges
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabWholeProductPositivity
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. A two-color invariant on literal projected edges -/

def alignedDiagonalTargetProjectedFaceEdges :
    List SlabProjectedFaceEdge :=
  slabProjectedFaceEdges alignedDiagonalTargetFaceStrandEdges

def alignedDiagonalTargetFaceVertices : List Nat :=
  slabFaceStrandFaceVertices alignedDiagonalTargetFaceStrandEdges

def alignedDiagonalTargetFaceAdjacentB (left right : Nat) : Bool :=
  slabProjectedFaceAdjacentB alignedDiagonalTargetProjectedFaceEdges
    left right

def alignedDiagonalFaceColorB (faceId : Nat) : Bool :=
  decide (slabPlaquetteAt 5 faceId ∈ alignedDiagonalNearSurface)

theorem alignedDiagonalFarSurface_face_not_mem_nearSurface
    {face : Z4Plaq} (hfar : face ∈ alignedDiagonalFarSurface) :
    face ∉ alignedDiagonalNearSurface := by
  intro hnear
  have hcross := (List.nodup_append.mp
    alignedDiagonalYZSurface_nodup).2.2
  exact hcross face hnear face hfar rfl

theorem alignedDiagonalTargetFaceStrandEdge_color_eq
    (edge : SlabFaceStrandEdge alignedDiagonalSwitchLeftPhysical)
    (hedge : edge ∈ alignedDiagonalTargetFaceStrandEdges) :
    alignedDiagonalFaceColorB edge.source.faceId =
      alignedDiagonalFaceColorB edge.target.faceId := by
  have hside :=
    alignedDiagonalTargetFaceStrandEdge_same_side edge hedge
  rcases hside with hnear | hfar
  · simp [alignedDiagonalFaceColorB, hnear.1, hnear.2]
  · have hsourceNotNear :=
      alignedDiagonalFarSurface_face_not_mem_nearSurface hfar.1
    have htargetNotNear :=
      alignedDiagonalFarSurface_face_not_mem_nearSurface hfar.2
    simp [alignedDiagonalFaceColorB, hsourceNotNear, htargetNotNear]

theorem alignedDiagonalTargetFaceAdjacentB_color_eq
    {left right : Nat}
    (hadj : alignedDiagonalTargetFaceAdjacentB left right = true) :
    alignedDiagonalFaceColorB left =
      alignedDiagonalFaceColorB right := by
  obtain ⟨projected, hprojected, horientation⟩ :=
    slabProjectedFaceAdjacentEdgeWitness left right
      alignedDiagonalTargetProjectedFaceEdges hadj
  unfold alignedDiagonalTargetProjectedFaceEdges at hprojected
  obtain ⟨edge, hedge, rfl⟩ := List.mem_map.mp hprojected
  have hcolor :=
    alignedDiagonalTargetFaceStrandEdge_color_eq edge hedge
  cases horientation with
  | inl hforward =>
      rw [← hforward.1, ← hforward.2]
      exact hcolor
  | inr hreverse =>
      rw [← hreverse.2, ← hreverse.1]
      exact hcolor.symm

/-! ## 2. Color transport along every finite graph chain -/

theorem alignedDiagonalTargetChain_color_eq
    {first last : Nat}
    (path : ChainIn alignedDiagonalTargetFaceAdjacentB
      alignedDiagonalTargetFaceVertices first last) :
    alignedDiagonalFaceColorB first =
      alignedDiagonalFaceColorB last := by
  induction path with
  | refl => rfl
  | step hadj _ rest ih =>
      exact (alignedDiagonalTargetFaceAdjacentB_color_eq hadj).trans ih

theorem alignedDiagonalSwitchRootFace_color :
    alignedDiagonalFaceColorB alignedDiagonalSwitchRootFaceId = true := by
  have hslab : alignedDiagonalNearQueryFace ∈
      boundaryCompleteSlabPlaquettes 5 :=
    alignedDiagonalSwitchSurface_subset_slab_five
      alignedDiagonalNearQueryFace
      (List.mem_append.mpr
        (Or.inl alignedDiagonalNearQueryFace_mem))
  unfold alignedDiagonalFaceColorB alignedDiagonalSwitchRootFaceId
    YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource.SlabBinarySupportConnectedCarrier.rootFaceId
    alignedDiagonalBinaryConnectedCarrier
  rw [slabPlaquetteAt_faceIdOfPlaquette hslab]
  exact decide_eq_true alignedDiagonalNearQueryFace_mem

theorem alignedDiagonalSwitchTargetFace_color :
    alignedDiagonalFaceColorB alignedDiagonalSwitchTargetFaceId = false := by
  have hslab : alignedDiagonalFarQueryFace ∈
      boundaryCompleteSlabPlaquettes 5 :=
    alignedDiagonalSwitchSurface_subset_slab_five
      alignedDiagonalFarQueryFace
      (List.mem_append.mpr
        (Or.inr alignedDiagonalFarQueryFace_mem))
  have hnotNear : alignedDiagonalFarQueryFace ∉
      alignedDiagonalNearSurface :=
    alignedDiagonalFarSurface_face_not_mem_nearSurface
      alignedDiagonalFarQueryFace_mem
  unfold alignedDiagonalFaceColorB alignedDiagonalSwitchTargetFaceId
    YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource.SlabBinarySupportConnectedCarrier.targetFaceId
    alignedDiagonalBinaryConnectedCarrier
  rw [slabPlaquetteAt_faceIdOfPlaquette hslab]
  exact decide_eq_false hnotNear

/-! ## 3. Global marked-face disconnection -/

def alignedDiagonalTarget_noMarkedFaceChain :
    ChainIn alignedDiagonalTargetFaceAdjacentB
      alignedDiagonalTargetFaceVertices
      alignedDiagonalSwitchRootFaceId
      alignedDiagonalSwitchTargetFaceId → False :=
  fun path => by
    have hcolor := alignedDiagonalTargetChain_color_eq path
    rw [alignedDiagonalSwitchRootFace_color,
      alignedDiagonalSwitchTargetFace_color] at hcolor
    cases hcolor

structure AlignedDiagonalTargetDisconnectionCertificate : Type where
  targetEdges : AlignedDiagonalTargetEdgeCertificate
  rootColor :
    alignedDiagonalFaceColorB alignedDiagonalSwitchRootFaceId = true
  targetColor :
    alignedDiagonalFaceColorB alignedDiagonalSwitchTargetFaceId = false
  markedDisconnected : ChainIn alignedDiagonalTargetFaceAdjacentB
    alignedDiagonalTargetFaceVertices
    alignedDiagonalSwitchRootFaceId
    alignedDiagonalSwitchTargetFaceId → False

def alignedDiagonalTargetDisconnectionCertificate :
    AlignedDiagonalTargetDisconnectionCertificate :=
  { targetEdges := alignedDiagonalTargetEdgeCertificate
    rootColor := alignedDiagonalSwitchRootFace_color
    targetColor := alignedDiagonalSwitchTargetFace_color
    markedDisconnected := alignedDiagonalTarget_noMarkedFaceChain }

#print axioms alignedDiagonalFarSurface_face_not_mem_nearSurface
#print axioms alignedDiagonalTargetFaceStrandEdge_color_eq
#print axioms alignedDiagonalTargetFaceAdjacentB_color_eq
#print axioms alignedDiagonalTargetChain_color_eq
#print axioms alignedDiagonalTarget_noMarkedFaceChain
#print axioms alignedDiagonalTargetDisconnectionCertificate

end YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabTargetDisconnection
