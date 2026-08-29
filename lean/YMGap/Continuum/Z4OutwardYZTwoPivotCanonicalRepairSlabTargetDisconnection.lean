/-
# Marked-face disconnection in the two-pivot outward repair target

Every selected target edge stays within the target lobe or within the root
lobe.  Color a face identifier by root-lobe membership.  Projected adjacency
and then every Type-valued finite graph chain preserve this color.  The
marked Y root is in the root lobe and the marked Z target is in the disjoint
target lobe, so no chain connects them.

Constructive contract: Boolean color transport and structural recursion on
an explicit `ChainIn`; no choice, `Classical`, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedFaceSupportRefinement
import YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabTargetEdges

namespace YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabTargetDisconnection

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
open YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairCutCarrier
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabConnectedSource
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabPivotPairing
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabSwitchingProfile
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabTargetEdges

def outwardYZCanonicalRepairTargetProjectedFaceEdges :
    List SlabProjectedFaceEdge :=
  slabProjectedFaceEdges outwardYZCanonicalRepairTargetFaceStrandEdges

def outwardYZCanonicalRepairTargetFaceVertices : List Nat :=
  slabFaceStrandFaceVertices outwardYZCanonicalRepairTargetFaceStrandEdges

def outwardYZCanonicalRepairTargetFaceAdjacentB
    (left right : Nat) : Bool :=
  slabProjectedFaceAdjacentB
    outwardYZCanonicalRepairTargetProjectedFaceEdges left right

def outwardYZCanonicalRepairRootLobeColorB (faceId : Nat) : Bool :=
  decide (slabPlaquetteAt 5 faceId ∈
    outwardYZCanonicalRepairRootLobe)

theorem outwardYZCanonicalRepairTargetLobe_face_not_mem_rootLobe
    {face : Z4Plaq}
    (htarget : face ∈ outwardYZCanonicalRepairTargetLobe) :
    face ∉ outwardYZCanonicalRepairRootLobe := by
  intro hroot
  have hcross := (List.nodup_append.mp
    outwardYZCanonicalRepairSurface_nodup).2.2
  exact hcross face htarget face hroot rfl

theorem outwardYZCanonicalRepairTargetFaceStrandEdge_color_eq
    (edge : SlabFaceStrandEdge
      outwardYZCanonicalRepairSwitchLeftPhysical)
    (hedge : edge ∈ outwardYZCanonicalRepairTargetFaceStrandEdges) :
    outwardYZCanonicalRepairRootLobeColorB edge.source.faceId =
      outwardYZCanonicalRepairRootLobeColorB edge.target.faceId := by
  have hside :=
    outwardYZCanonicalRepairTargetFaceStrandEdge_same_side edge hedge
  rcases hside with htarget | hroot
  · have hsourceNotRoot :=
      outwardYZCanonicalRepairTargetLobe_face_not_mem_rootLobe htarget.1
    have htargetNotRoot :=
      outwardYZCanonicalRepairTargetLobe_face_not_mem_rootLobe htarget.2
    simp [outwardYZCanonicalRepairRootLobeColorB,
      hsourceNotRoot, htargetNotRoot]
  · simp [outwardYZCanonicalRepairRootLobeColorB, hroot.1, hroot.2]

theorem outwardYZCanonicalRepairTargetFaceAdjacentB_color_eq
    {left right : Nat}
    (hadj : outwardYZCanonicalRepairTargetFaceAdjacentB
      left right = true) :
    outwardYZCanonicalRepairRootLobeColorB left =
      outwardYZCanonicalRepairRootLobeColorB right := by
  obtain ⟨projected, hprojected, horientation⟩ :=
    slabProjectedFaceAdjacentEdgeWitness left right
      outwardYZCanonicalRepairTargetProjectedFaceEdges hadj
  unfold outwardYZCanonicalRepairTargetProjectedFaceEdges at hprojected
  obtain ⟨edge, hedge, rfl⟩ := List.mem_map.mp hprojected
  have hcolor :=
    outwardYZCanonicalRepairTargetFaceStrandEdge_color_eq edge hedge
  cases horientation with
  | inl hforward =>
      rw [← hforward.1, ← hforward.2]
      exact hcolor
  | inr hreverse =>
      rw [← hreverse.2, ← hreverse.1]
      exact hcolor.symm

theorem outwardYZCanonicalRepairTargetChain_color_eq
    {first last : Nat}
    (path : ChainIn outwardYZCanonicalRepairTargetFaceAdjacentB
      outwardYZCanonicalRepairTargetFaceVertices first last) :
    outwardYZCanonicalRepairRootLobeColorB first =
      outwardYZCanonicalRepairRootLobeColorB last := by
  induction path with
  | refl => rfl
  | step hadj _ rest ih =>
      exact
        (outwardYZCanonicalRepairTargetFaceAdjacentB_color_eq hadj).trans ih

theorem outwardYZCanonicalRepairSwitchRootFace_color :
    outwardYZCanonicalRepairRootLobeColorB
      outwardYZCanonicalRepairRootFaceId = true := by
  have hslab : outwardYQueryFace ∈ boundaryCompleteSlabPlaquettes 5 :=
    outwardYZCanonicalRepairSwitchSurface_subset_slab_five
      outwardYQueryFace
      (List.mem_append.mpr
        (Or.inr outwardYZCanonicalRepairRoot_mem_rootLobe))
  unfold outwardYZCanonicalRepairRootLobeColorB
    outwardYZCanonicalRepairRootFaceId
    YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource.SlabBinarySupportConnectedCarrier.rootFaceId
    outwardYZCanonicalRepairBinaryConnectedCarrier
  rw [slabPlaquetteAt_faceIdOfPlaquette hslab]
  exact decide_eq_true outwardYZCanonicalRepairRoot_mem_rootLobe

theorem outwardYZCanonicalRepairSwitchTargetFace_color :
    outwardYZCanonicalRepairRootLobeColorB
      outwardYZCanonicalRepairTargetFaceId = false := by
  have hslab : outwardZQueryFace ∈ boundaryCompleteSlabPlaquettes 5 :=
    outwardYZCanonicalRepairSwitchSurface_subset_slab_five
      outwardZQueryFace
      (List.mem_append.mpr
        (Or.inl outwardYZCanonicalRepairTarget_mem_targetLobe))
  have hnotRoot : outwardZQueryFace ∉
      outwardYZCanonicalRepairRootLobe :=
    outwardYZCanonicalRepairTargetLobe_face_not_mem_rootLobe
      outwardYZCanonicalRepairTarget_mem_targetLobe
  unfold outwardYZCanonicalRepairRootLobeColorB
    outwardYZCanonicalRepairTargetFaceId
    YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource.SlabBinarySupportConnectedCarrier.targetFaceId
    outwardYZCanonicalRepairBinaryConnectedCarrier
  rw [slabPlaquetteAt_faceIdOfPlaquette hslab]
  exact decide_eq_false hnotRoot

def outwardYZCanonicalRepairTarget_noMarkedFaceChain :
    ChainIn outwardYZCanonicalRepairTargetFaceAdjacentB
      outwardYZCanonicalRepairTargetFaceVertices
      outwardYZCanonicalRepairRootFaceId
      outwardYZCanonicalRepairTargetFaceId → False :=
  fun path => by
    have hcolor := outwardYZCanonicalRepairTargetChain_color_eq path
    rw [outwardYZCanonicalRepairSwitchRootFace_color,
      outwardYZCanonicalRepairSwitchTargetFace_color] at hcolor
    cases hcolor

structure OutwardYZCanonicalRepairTargetDisconnectionCertificate : Type where
  targetEdges : OutwardYZCanonicalRepairTargetEdgeCertificate
  rootColor : outwardYZCanonicalRepairRootLobeColorB
    outwardYZCanonicalRepairRootFaceId = true
  targetColor : outwardYZCanonicalRepairRootLobeColorB
    outwardYZCanonicalRepairTargetFaceId = false
  markedDisconnected : ChainIn
    outwardYZCanonicalRepairTargetFaceAdjacentB
    outwardYZCanonicalRepairTargetFaceVertices
    outwardYZCanonicalRepairRootFaceId
    outwardYZCanonicalRepairTargetFaceId → False

def outwardYZCanonicalRepairTargetDisconnectionCertificate :
    OutwardYZCanonicalRepairTargetDisconnectionCertificate :=
  { targetEdges := outwardYZCanonicalRepairTargetEdgeCertificate
    rootColor := outwardYZCanonicalRepairSwitchRootFace_color
    targetColor := outwardYZCanonicalRepairSwitchTargetFace_color
    markedDisconnected :=
      outwardYZCanonicalRepairTarget_noMarkedFaceChain }

#print axioms outwardYZCanonicalRepairTargetLobe_face_not_mem_rootLobe
#print axioms outwardYZCanonicalRepairTargetFaceStrandEdge_color_eq
#print axioms outwardYZCanonicalRepairTargetFaceAdjacentB_color_eq
#print axioms outwardYZCanonicalRepairTargetChain_color_eq
#print axioms outwardYZCanonicalRepairTarget_noMarkedFaceChain
#print axioms outwardYZCanonicalRepairTargetDisconnectionCertificate

end YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabTargetDisconnection
