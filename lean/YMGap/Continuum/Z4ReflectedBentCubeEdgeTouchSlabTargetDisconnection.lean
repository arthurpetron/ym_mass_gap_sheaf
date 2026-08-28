/-
# Marked-face disconnection in the reflected bent-cube target graph

Every selected target edge stays within the near lobe or within the far lobe.
Color a face identifier by near-lobe membership.  Projected adjacency and
then every Type-valued finite graph chain preserve this color.  The marked
root is near and its reflected target is far, so no chain connects them.

Constructive contract: Boolean color transport and structural recursion on
an explicit `ChainIn`; no choice, `Classical`, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedFaceSupportRefinement
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetEdges

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetDisconnection

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSupportRefinement
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchCutCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetEdges
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabWholeProductPositivity

def reflectedBentTargetProjectedFaceEdges :
    List SlabProjectedFaceEdge :=
  slabProjectedFaceEdges reflectedBentTargetFaceStrandEdges

def reflectedBentTargetFaceVertices : List Nat :=
  slabFaceStrandFaceVertices reflectedBentTargetFaceStrandEdges

def reflectedBentTargetFaceAdjacentB (left right : Nat) : Bool :=
  slabProjectedFaceAdjacentB reflectedBentTargetProjectedFaceEdges
    left right

def reflectedBentFaceColorB (faceId : Nat) : Bool :=
  decide (slabPlaquetteAt 5 faceId ∈ reflectedBentNearSurface)

theorem reflectedBentFarSurface_face_not_mem_nearSurface
    {face : Z4Plaq} (hfar : face ∈ reflectedBentFarSurface) :
    face ∉ reflectedBentNearSurface := by
  intro hnear
  have hcross := (List.nodup_append.mp
    YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchCutCarrier.reflectedBentSwitchSurface_nodup).2.2
  exact hcross face hnear face hfar rfl

theorem reflectedBentTargetFaceStrandEdge_color_eq
    (edge : SlabFaceStrandEdge reflectedBentSwitchLeftPhysical)
    (hedge : edge ∈ reflectedBentTargetFaceStrandEdges) :
    reflectedBentFaceColorB edge.source.faceId =
      reflectedBentFaceColorB edge.target.faceId := by
  have hside := reflectedBentTargetFaceStrandEdge_same_side edge hedge
  rcases hside with hnear | hfar
  · simp [reflectedBentFaceColorB, hnear.1, hnear.2]
  · have hsourceNotNear :=
      reflectedBentFarSurface_face_not_mem_nearSurface hfar.1
    have htargetNotNear :=
      reflectedBentFarSurface_face_not_mem_nearSurface hfar.2
    simp [reflectedBentFaceColorB, hsourceNotNear, htargetNotNear]

theorem reflectedBentTargetFaceAdjacentB_color_eq
    {left right : Nat}
    (hadj : reflectedBentTargetFaceAdjacentB left right = true) :
    reflectedBentFaceColorB left = reflectedBentFaceColorB right := by
  obtain ⟨projected, hprojected, horientation⟩ :=
    slabProjectedFaceAdjacentEdgeWitness left right
      reflectedBentTargetProjectedFaceEdges hadj
  unfold reflectedBentTargetProjectedFaceEdges at hprojected
  obtain ⟨edge, hedge, rfl⟩ := List.mem_map.mp hprojected
  have hcolor := reflectedBentTargetFaceStrandEdge_color_eq edge hedge
  cases horientation with
  | inl hforward =>
      rw [← hforward.1, ← hforward.2]
      exact hcolor
  | inr hreverse =>
      rw [← hreverse.2, ← hreverse.1]
      exact hcolor.symm

theorem reflectedBentTargetChain_color_eq
    {first last : Nat}
    (path : ChainIn reflectedBentTargetFaceAdjacentB
      reflectedBentTargetFaceVertices first last) :
    reflectedBentFaceColorB first = reflectedBentFaceColorB last := by
  induction path with
  | refl => rfl
  | step hadj _ rest ih =>
      exact (reflectedBentTargetFaceAdjacentB_color_eq hadj).trans ih

theorem reflectedBentSwitchRootFace_color :
    reflectedBentFaceColorB reflectedBentRootFaceId = true := by
  have hslab : reflectedBentRootPlaquette ∈
      boundaryCompleteSlabPlaquettes 5 :=
    YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile.reflectedBentSwitchSurface_subset_slab_five
      reflectedBentRootPlaquette
      (List.mem_append.mpr (Or.inl reflectedBentRoot_mem))
  unfold reflectedBentFaceColorB reflectedBentRootFaceId
    YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource.SlabBinarySupportConnectedCarrier.rootFaceId
    reflectedBentBinaryConnectedCarrier
  rw [slabPlaquetteAt_faceIdOfPlaquette hslab]
  exact decide_eq_true reflectedBentRoot_mem

theorem reflectedBentSwitchTargetFace_color :
    reflectedBentFaceColorB reflectedBentTargetFaceId = false := by
  have hslab : reflectedBentTargetPlaquette ∈
      boundaryCompleteSlabPlaquettes 5 :=
    YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile.reflectedBentSwitchSurface_subset_slab_five
      reflectedBentTargetPlaquette
      (List.mem_append.mpr (Or.inr reflectedBentTarget_mem))
  have hnotNear : reflectedBentTargetPlaquette ∉ reflectedBentNearSurface :=
    reflectedBentFarSurface_face_not_mem_nearSurface
      reflectedBentTarget_mem
  unfold reflectedBentFaceColorB reflectedBentTargetFaceId
    YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource.SlabBinarySupportConnectedCarrier.targetFaceId
    reflectedBentBinaryConnectedCarrier
  rw [slabPlaquetteAt_faceIdOfPlaquette hslab]
  exact decide_eq_false hnotNear

def reflectedBentTarget_noMarkedFaceChain :
    ChainIn reflectedBentTargetFaceAdjacentB
      reflectedBentTargetFaceVertices
      reflectedBentRootFaceId reflectedBentTargetFaceId → False :=
  fun path => by
    have hcolor := reflectedBentTargetChain_color_eq path
    rw [reflectedBentSwitchRootFace_color,
      reflectedBentSwitchTargetFace_color] at hcolor
    cases hcolor

structure ReflectedBentTargetDisconnectionCertificate : Type where
  targetEdges : ReflectedBentTargetEdgeCertificate
  rootColor : reflectedBentFaceColorB reflectedBentRootFaceId = true
  targetColor : reflectedBentFaceColorB reflectedBentTargetFaceId = false
  markedDisconnected : ChainIn reflectedBentTargetFaceAdjacentB
    reflectedBentTargetFaceVertices
    reflectedBentRootFaceId reflectedBentTargetFaceId → False

def reflectedBentTargetDisconnectionCertificate :
    ReflectedBentTargetDisconnectionCertificate :=
  { targetEdges := reflectedBentTargetEdgeCertificate
    rootColor := reflectedBentSwitchRootFace_color
    targetColor := reflectedBentSwitchTargetFace_color
    markedDisconnected := reflectedBentTarget_noMarkedFaceChain }

#print axioms reflectedBentFarSurface_face_not_mem_nearSurface
#print axioms reflectedBentTargetFaceStrandEdge_color_eq
#print axioms reflectedBentTargetFaceAdjacentB_color_eq
#print axioms reflectedBentTargetChain_color_eq
#print axioms reflectedBentTarget_noMarkedFaceChain
#print axioms reflectedBentTargetDisconnectionCertificate

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetDisconnection
