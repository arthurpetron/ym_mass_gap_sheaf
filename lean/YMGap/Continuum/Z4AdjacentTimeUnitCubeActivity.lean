/-
# Exact positive activity of the adjacent-time cube

The time-one cube used by the physical two-time cylinder is a literal
translation of the checked refined cube.  This module transports the local
incidence calculation through that genuine lattice translation: translated
links are still incident on exactly two translated faces.  Hence every local
fundamental Haar multiplicity is one and the complete time-one activity is
the twenty-fourth power of the derived fundamental heat-kernel coefficient.

This proves strict positivity of the second time-slice root.  It is not a
reflection-positivity or correlation statement.
-/

import YMGap.Continuum.Z4AdjacentTimeUnitCubeCylinder
import YMGap.Continuum.Z4DyadicUnitCubeActivity

namespace YMGap.Continuum.Z4AdjacentTimeUnitCubeActivity

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.Z4AdjacentTimeUnitCubeCylinder
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicUnitCubeActivity
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4ExplicitExcitationIncidenceBound
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Translation is injective on the cell types -/

theorem euclideanTimeTranslateVertex_injective :
    Function.Injective euclideanTimeTranslateVertex := by
  intro left right heq
  obtain ⟨a, b, c, d⟩ := left
  obtain ⟨a', b', c', d'⟩ := right
  simp only [euclideanTimeTranslateVertex, addE, Prod.mk.injEq] at heq ⊢
  exact ⟨heq.1, heq.2.1, heq.2.2.1,
    Nat.add_right_cancel heq.2.2.2⟩

theorem euclideanTimeTranslateLink_injective :
    Function.Injective euclideanTimeTranslateLink := by
  intro left right heq
  apply Prod.ext
  · apply euclideanTimeTranslateVertex_injective
    simpa only [euclideanTimeTranslateLink] using congrArg Prod.fst heq
  · simpa only [euclideanTimeTranslateLink] using congrArg Prod.snd heq

theorem euclideanTimeTranslatePlaquette_injective :
    Function.Injective euclideanTimeTranslatePlaquette := by
  intro left right heq
  apply Prod.ext
  · apply euclideanTimeTranslateVertex_injective
    simpa only [euclideanTimeTranslatePlaquette] using congrArg Prod.fst heq
  · simpa only [euclideanTimeTranslatePlaquette] using congrArg Prod.snd heq

theorem euclideanTimeTranslateLink_mem_edges_iff
    (plaquette : Z4Plaq) (link : Z4Link) :
    euclideanTimeTranslateLink link ∈
        edgesOf (euclideanTimeTranslatePlaquette plaquette) ↔
      link ∈ edgesOf plaquette := by
  rw [edgesOf_euclideanTimeTranslatePlaquette]
  constructor
  · intro hmem
    obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hmem
    have hsourceEq : source = link :=
      euclideanTimeTranslateLink_injective heq
    simpa [hsourceEq] using hsource
  · intro hmem
    exact List.mem_map.mpr ⟨link, hmem, rfl⟩

/-! ## 2. Translation preserves local face incidence -/

theorem geometricIncidentPlaquettes_timeTranslate_length
    (faces : List Z4Plaq) (link : Z4Link) :
    (geometricIncidentPlaquettes
        (faces.map euclideanTimeTranslatePlaquette)
        (euclideanTimeTranslateLink link)).length =
      (geometricIncidentPlaquettes faces link).length := by
  induction faces with
  | nil => rfl
  | cons plaquette rest ih =>
      unfold geometricIncidentPlaquettes at ih ⊢
      simp only [List.map_cons, List.filter_cons]
      by_cases hlink : link ∈ edgesOf plaquette
      · have htranslated : euclideanTimeTranslateLink link ∈
            edgesOf (euclideanTimeTranslatePlaquette plaquette) :=
          (euclideanTimeTranslateLink_mem_edges_iff plaquette link).2 hlink
        simp [hlink, htranslated, ih]
      · have htranslated : euclideanTimeTranslateLink link ∉
            edgesOf (euclideanTimeTranslatePlaquette plaquette) := by
          intro hmem
          exact hlink
            ((euclideanTimeTranslateLink_mem_edges_iff plaquette link).1 hmem)
        simp [hlink, htranslated, ih]

theorem adjacentTimeRefinedUnitCube_geometricIncidentPlaquettes_length_eq_two
    {link : Z4Link}
    (hlink : link ∈
      geometricTouchedLinks adjacentTimeRefinedUnitCubeSurface) :
    (geometricIncidentPlaquettes
      adjacentTimeRefinedUnitCubeSurface link).length = 2 := by
  obtain ⟨plaquette, hplaquette, hedge⟩ :=
    mem_geometricTouchedLinks.mp hlink
  obtain ⟨sourcePlaquette, hsourcePlaquette, hplaquetteEq⟩ :=
    decodeMapMember euclideanTimeTranslatePlaquette
      refinedUnitCubeSurface plaquette hplaquette
  rw [← hplaquetteEq,
    edgesOf_euclideanTimeTranslatePlaquette] at hedge
  obtain ⟨sourceLink, hsourceLink, hlinkEq⟩ := List.mem_map.mp hedge
  rw [← hlinkEq]
  have hsourceTouched : sourceLink ∈
      geometricTouchedLinks refinedUnitCubeSurface :=
    mem_geometricTouchedLinks.mpr
      ⟨sourcePlaquette, hsourcePlaquette, hsourceLink⟩
  exact (geometricIncidentPlaquettes_timeTranslate_length
      refinedUnitCubeSurface sourceLink).trans
    (refinedUnitCube_geometricIncidentPlaquettes_length_eq_two
      hsourceTouched)

/-! ## 3. The numerical time-one root has exact positive activity -/

theorem adjacentTimeUnitCubeSupportIds_mem_cutoffOneFaceSupports :
    adjacentTimeUnitCubeSupportIds ∈ cutoffOneFaceSupports 5 :=
  canonicalSurfacePolymer_mem_faceSupports
    adjacentTimeUnitCubeSupportIds_mem_canonicalSurfacePolymers

theorem adjacentTimeUnitCubeSupportIds_length :
    adjacentTimeUnitCubeSupportIds.length = 24 := by
  have hleftNodup :
      (geometricPolymer 5 adjacentTimeUnitCubeSupportIds).Nodup :=
    geometricPolymer_nodup
      adjacentTimeUnitCubeSupportIds_mem_cutoffOneFaceSupports
  have hrightNodup : adjacentTimeRefinedUnitCubeSurface.Nodup := by
    unfold adjacentTimeRefinedUnitCubeSurface
    exact nodup_map_of_injOn euclideanTimeTranslatePlaquette
      refinedUnitCubeSurface refinedUnitCubeSurface_nodup
      (fun _ _ _ _ heq =>
        euclideanTimeTranslatePlaquette_injective heq)
  have hlength := sameSupport_length_eq_of_nodup
    adjacentTimeUnitCubeSupportIds_sameSupport
    hleftNodup hrightNodup
  unfold geometricPolymer at hlength
  rw [List.length_map] at hlength
  unfold adjacentTimeRefinedUnitCubeSurface at hlength
  simpa only [List.length_map, refinedUnitCubeSurface_length] using hlength

private theorem adjacentTimeCubeLink_mem_of_touched
    {link : Z4Link}
    (hlink : link ∈ touchedPhysicalLinks 5
      (componentLabel adjacentTimeUnitCubeSupportIds)) :
    link ∈ geometricTouchedLinks adjacentTimeRefinedUnitCubeSurface := by
  have hgeometric :=
    (mem_touchedPhysicalLinks_iff_geometric
      adjacentTimeUnitCubeSupportIds_mem_cutoffOneFaceSupports link).mp hlink
  obtain ⟨plaquette, hplaquette, hboundary⟩ :=
    mem_geometricTouchedLinks.mp hgeometric
  exact mem_geometricTouchedLinks.mpr
    ⟨plaquette,
      adjacentTimeUnitCubeSupportIds_sameSupport.1 plaquette hplaquette,
      hboundary⟩

theorem adjacentTimeUnitCube_geometricIncidentPlaquettes_length_eq_two
    {link : Z4Link}
    (hlink : link ∈ touchedPhysicalLinks 5
      (componentLabel adjacentTimeUnitCubeSupportIds)) :
    (geometricIncidentPlaquettes
      (geometricPolymer 5 adjacentTimeUnitCubeSupportIds) link).length = 2 := by
  have hsame := geometricIncidentPlaquettes_sameSupport
    adjacentTimeUnitCubeSupportIds_sameSupport link
  have hleftNodup := geometricIncidentPlaquettes_nodup
    adjacentTimeUnitCubeSupportIds_mem_cutoffOneFaceSupports link
  have hrightNodup :
      (geometricIncidentPlaquettes
        adjacentTimeRefinedUnitCubeSurface link).Nodup := by
    unfold geometricIncidentPlaquettes
    exact List.filter_sublist.nodup
      (by
        unfold adjacentTimeRefinedUnitCubeSurface
        exact nodup_map_of_injOn euclideanTimeTranslatePlaquette
          refinedUnitCubeSurface refinedUnitCubeSurface_nodup
          (fun _ _ _ _ heq =>
            euclideanTimeTranslatePlaquette_injective heq))
  have hlength := sameSupport_length_eq_of_nodup
    hsame hleftNodup hrightNodup
  exact hlength.trans
    (adjacentTimeRefinedUnitCube_geometricIncidentPlaquettes_length_eq_two
      (adjacentTimeCubeLink_mem_of_touched hlink))

theorem adjacentTimeUnitCube_geometricLinkMultiplicityFactor_eq_one
    {link : Z4Link}
    (hlink : link ∈ touchedPhysicalLinks 5
      (componentLabel adjacentTimeUnitCubeSupportIds)) :
    geometricLinkMultiplicityFactor
      (geometricPolymer 5 adjacentTimeUnitCubeSupportIds) link = 1 := by
  unfold geometricLinkMultiplicityFactor
  rw [adjacentTimeUnitCube_geometricIncidentPlaquettes_length_eq_two hlink]
  rfl

private theorem adjacentTimeUnitCube_geometricLinkMultiplicityProduct_eqv_one_on :
    ∀ links : List Z4Link,
    (∀ link, link ∈ links →
      link ∈ touchedPhysicalLinks 5
        (componentLabel adjacentTimeUnitCubeSupportIds)) →
    geometricLinkMultiplicityProduct
      (geometricPolymer 5 adjacentTimeUnitCubeSupportIds) links ≈ 1
  | [], _ => Q'.eqv_refl _
  | link :: rest, hsubset => by
      change (geometricLinkMultiplicityFactor
          (geometricPolymer 5 adjacentTimeUnitCubeSupportIds) link *
        geometricLinkMultiplicityProduct
          (geometricPolymer 5 adjacentTimeUnitCubeSupportIds) rest) ≈ 1
      rw [adjacentTimeUnitCube_geometricLinkMultiplicityFactor_eq_one
        (hsubset link List.mem_cons_self)]
      exact Q'.eqv_trans _ (1 * 1) _
        (Q'.mul_eqv_congr_left 1 _ _
          (adjacentTimeUnitCube_geometricLinkMultiplicityProduct_eqv_one_on
            rest (fun item hitem =>
              hsubset item (List.mem_cons_of_mem link hitem))))
        (Q'.one_mul_eqv 1)

theorem adjacentTimeUnitCube_explicitLinkMultiplicityProduct_eqv_one :
    explicitLinkMultiplicityProduct 1 5
      (componentLabel adjacentTimeUnitCubeSupportIds)
      (touchedIndexedLinks 5
        (componentLabel adjacentTimeUnitCubeSupportIds)) ≈ 1 :=
  Q'.eqv_trans _ _ _
    (explicitLinkMultiplicityProduct_componentLabel_eqv_geometric
      adjacentTimeUnitCubeSupportIds_mem_cutoffOneFaceSupports)
    (adjacentTimeUnitCube_geometricLinkMultiplicityProduct_eqv_one_on _
      (fun _ hlink => hlink))

private theorem qmul_congr_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem adjacentTimeUnitCube_canonicalSurfaceActivity_eqv
    (coupling : Q') :
    canonicalSurfaceActivity coupling 5 adjacentTimeUnitCubeSupportIds ≈
      (coeffW coupling 1) ^ 24 := by
  have hface := parametricPhysicalFaceFactor_componentLabel_eqv_pow
    coupling adjacentTimeUnitCubeSupportIds_mem_cutoffOneFaceSupports
  rw [adjacentTimeUnitCubeSupportIds_length] at hface
  unfold canonicalSurfaceActivity parametricLocalizedSpinFoamWeight
  exact Q'.eqv_trans _ ((coeffW coupling 1) ^ 24 * 1) _
    (qmul_congr_local hface
      adjacentTimeUnitCube_explicitLinkMultiplicityProduct_eqv_one)
    (Q'.mul_one_eqv _)

private theorem qpow_pos_local {value : Q'}
    (hvalue : (0 : Q') < value) :
    ∀ exponent : Nat, (0 : Q') < value ^ exponent
  | 0 => by
      change (0 : Q') < 1
      decide
  | exponent + 1 => Q'.mul_pos hvalue (qpow_pos_local hvalue exponent)

theorem adjacentTimeUnitCube_canonicalSurfaceActivity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling) :
    (0 : Q') <
      canonicalSurfaceActivity coupling 5 adjacentTimeUnitCubeSupportIds := by
  have hcoefficient : (0 : Q') < coeffW coupling 1 :=
    YMGap.Continuum.FusionResidualBound.coeffW_pos hcoupling 1
  have hpower := qpow_pos_local hcoefficient 24
  exact Q'.pos_of_lt_of_le hpower
    (Q'.ge_of_eqv
      (adjacentTimeUnitCube_canonicalSurfaceActivity_eqv coupling))

end YMGap.Continuum.Z4AdjacentTimeUnitCubeActivity

#print axioms YMGap.Continuum.Z4AdjacentTimeUnitCubeActivity.euclideanTimeTranslateLink_mem_edges_iff
#print axioms YMGap.Continuum.Z4AdjacentTimeUnitCubeActivity.adjacentTimeRefinedUnitCube_geometricIncidentPlaquettes_length_eq_two
#print axioms YMGap.Continuum.Z4AdjacentTimeUnitCubeActivity.adjacentTimeUnitCube_geometricIncidentPlaquettes_length_eq_two
#print axioms YMGap.Continuum.Z4AdjacentTimeUnitCubeActivity.adjacentTimeUnitCube_canonicalSurfaceActivity_eqv
#print axioms YMGap.Continuum.Z4AdjacentTimeUnitCubeActivity.adjacentTimeUnitCube_canonicalSurfaceActivity_pos
