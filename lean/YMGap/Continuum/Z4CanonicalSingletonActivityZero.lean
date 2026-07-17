/-
# Exact vanishing of one-face canonical activities

A single excited plaquette has an odd fundamental spin at each of its four
boundary links.  The local SU(2) Haar projector therefore vanishes.  This
module records the resulting exact zero activity for every singleton
cutoff-one support, at every rational coupling.
-/

import YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
import YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
import YMGap.Continuum.Z4CanonicalPolymerTransport
import YMGap.Continuum.Z4CutoffOneEventBridge
import YMGap.Continuum.Z4EvenIncidenceCanonicalActivityPositive

namespace YMGap.Continuum.Z4CanonicalSingletonActivityZero

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4ExplicitExcitationIncidenceBound
open YMGap.Continuum.Z4ExplicitExcitationLocalization
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4EvenIncidenceCanonicalActivityPositive
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UnitCubeIncidenceParity

local infix:50 " ≈ " => Q'.eqv

private theorem linkProduct_eqv_zero_of_factor
    {K n : Nat} {physical : EdgeLabelling}
    {indexed : Nat × Z4Link}
    (hfactor : explicitLinkMultiplicityFactor K n physical indexed = 0) :
    ∀ (links : List (Nat × Z4Link)), indexed ∈ links →
      explicitLinkMultiplicityProduct K n physical links ≈ 0
  | [], hmem => absurd hmem List.not_mem_nil
  | head :: rest, hmem => by
      rcases List.mem_cons.mp hmem with heq | hrest
      · subst head
        change explicitLinkMultiplicityFactor K n physical indexed *
            explicitLinkMultiplicityProduct K n physical rest ≈ 0
        rw [hfactor]
        exact Q'.zero_mul_eqv _
      · change explicitLinkMultiplicityFactor K n physical head *
            explicitLinkMultiplicityProduct K n physical rest ≈ 0
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _
            (linkProduct_eqv_zero_of_factor hfactor rest hrest))
          (Q'.mul_zero_eqv _)

/-- The component label of a singleton face has exactly one excited incident
plaquette at the first boundary link of that face. -/
theorem singleton_excitedIncidence_odd
    {n face : Nat} (hsupport : [face] ∈ cutoffOneFaceSupports n) :
    let plaquette := boxPlaquetteAt n face
    let link := (plaquette.1, (dirsOf plaquette.2).1)
    (excitedIncidentPlaqIds n (componentLabel [face]) link).length % 2 = 1 := by
  dsimp
  rw [excitedIncidentPlaqIds_length_eq_geometric hsupport]
  rw [geometricIncidentPlaquettes_length_eq_faceIncidenceCount]
  unfold geometricPolymer
  have hboundary :
      ((boxPlaquetteAt n face).1,
          (dirsOf (boxPlaquetteAt n face).2).1) ∈
        edgesOf (boxPlaquetteAt n face) :=
    List.mem_cons_self
  rw [List.map_cons, List.map_nil]
  unfold faceIncidenceCount
  rw [if_pos hboundary]
  rfl

/-- Every one-face cutoff-one support has zero complete Haar link product. -/
theorem singleton_explicitLinkMultiplicityProduct_eqv_zero
    {n face : Nat} (hsupport : [face] ∈ cutoffOneFaceSupports n) :
    explicitLinkMultiplicityProduct 1 n (componentLabel [face])
        (touchedIndexedLinks n (componentLabel [face])) ≈ 0 := by
  let plaquette := boxPlaquetteAt n face
  let link : Z4Link := (plaquette.1, (dirsOf plaquette.2).1)
  have hface : face ∈ physicalFaceEdges n :=
    mem_of_mem_sublists (physicalFaceEdges n) [face]
      hsupport face List.mem_cons_self
  have hplaquette : plaquette ∈ boxPlaquettes n := by
    exact boxPlaquetteAt_mem_boxPlaquettes_of_physical hface
  have hlinkBoundary : link ∈ edgesOf plaquette := by
    unfold link
    simp [edgesOf]
  have hlinkBox : link ∈ distinctBoxLinks n := by
    unfold distinctBoxLinks
    rw [List.mem_eraseDups]
    exact boundary_mem_boxLinks hplaquette hlinkBoundary
  obtain ⟨index, hindexed⟩ := exists_mem_enumerate hlinkBox
  have hfaceLt : face < plaquetteEdgeCount n := physicalFaceId_lt hface
  have hfaceIndexed :
      (face, boxPlaquetteAt n face) ∈ enumerate (boxPlaquettes n) :=
    boxPlaquetteAt_mem_enumerate hfaceLt
  have hincident : face ∈ incidentPlaqIds n link :=
    mem_incidentPlaqIds.mpr ⟨boxPlaquetteAt n face,
      hfaceIndexed, hlinkBoundary⟩
  have hone : componentLabel [face] face = 1 :=
    componentLabel_eq_one_iff.mpr List.mem_cons_self
  have htouched : (index, link) ∈
      touchedIndexedLinks n (componentLabel [face]) := by
    unfold touchedIndexedLinks
    apply List.mem_filter.mpr
    refine ⟨hindexed, ?_⟩
    unfold linkTouchesExcitationB
    apply hasExcitedB_true_of_mem (componentLabel [face]) hincident
    rw [hone]
    omega
  have hphysical : componentLabel [face] ∈
      explicitPhysicalLabellings 1 n :=
    componentLabel_mem_explicitPhysicalLabellings_one hsupport
  have hodd :
      (excitedIncidentPlaqIds n (componentLabel [face]) link).length % 2 = 1 := by
    simpa only [plaquette, link] using
      singleton_excitedIncidence_odd hsupport
  have hfactor : explicitLinkMultiplicityFactor 1 n
      (componentLabel [face]) (index, link) = 0 :=
    explicitLinkMultiplicityFactor_eq_zero_of_odd_incidence
      hphysical hodd
  exact linkProduct_eqv_zero_of_factor hfactor
    (touchedIndexedLinks n (componentLabel [face])) htouched

/-- A singleton cutoff-one support has exactly zero canonical activity at
every coupling. -/
theorem canonicalSurfaceActivity_singleton_eqv_zero
    (coupling : Q') {n face : Nat}
    (hsupport : [face] ∈ cutoffOneFaceSupports n) :
    canonicalSurfaceActivity coupling n [face] ≈ 0 := by
  unfold canonicalSurfaceActivity parametricLocalizedSpinFoamWeight
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (singleton_explicitLinkMultiplicityProduct_eqv_zero hsupport))
    (Q'.mul_zero_eqv _)

#print axioms singleton_excitedIncidence_odd
#print axioms singleton_explicitLinkMultiplicityProduct_eqv_zero
#print axioms canonicalSurfaceActivity_singleton_eqv_zero

end YMGap.Continuum.Z4CanonicalSingletonActivityZero
