/-
# Exact activity of the centrally shifted coarse unit cube

The centered exhaustion places a fixed local observable away from every open
boundary.  Its first useful carrier is the six-face coarse unit cube shifted
by one lattice unit in all four coordinates and encoded in the box of side
three.  This file proves directly that the shifted surface remains closed,
that every touched link has incidence two, and that its exact cutoff-one
activity is the same sixth power of the derived fundamental coefficient.

This is local finite geometry.  The subsequent thermodynamic module transports
this central carrier through the uniformly padded centered stages.
-/

import YMGap.Continuum.Z4CoarseUnitCubeActivity
import YMGap.Continuum.Z4SignedCenteredFixedObservableRecoding
import YMGap.Continuum.Z4UniformShiftPhysicalWeights

namespace YMGap.Continuum.Z4CenteredCoarseUnitCubeActivity

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CoarseUnitCubeActivity
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4ExplicitExcitationIncidenceBound
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SignedCenteredFixedObservableRecoding
open YMGap.Continuum.Z4UniformShiftPhysicalTransport
open YMGap.Continuum.Z4UniformShiftPhysicalWeights
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The central box-three carrier -/

def centeredCoarseUnitCubeSurfaceAtThree : List Z4Plaq :=
  unitCubeSurface.map (uniformShiftPlaquette 1)

theorem centeredCoarseUnitCubeSurfaceAtThree_nodup :
    centeredCoarseUnitCubeSurfaceAtThree.Nodup := by
  unfold centeredCoarseUnitCubeSurfaceAtThree
  exact nodup_map_of_injOn (uniformShiftPlaquette 1)
    unitCubeSurface unitCubeSurface_nodup
    (fun _ _ _ _ heq => uniformShiftPlaquette_injective 1 heq)

theorem centeredCoarseUnitCubeSurfaceAtThree_subset_box :
    ∀ plaquette, plaquette ∈ centeredCoarseUnitCubeSurfaceAtThree →
      plaquette ∈ boxPlaquettes 3 := by
  intro plaquette hplaquette
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
  apply (mem_boxPlaquettes (uniformShiftPlaquette 1 source) 3).2
  simp only [unitCubeSurface, List.mem_cons, List.not_mem_nil, or_false]
    at hsource
  rcases hsource with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    dsimp [uniformShiftPlaquette, uniformShiftVertex]
    exact ⟨by omega, by omega, by omega, by omega⟩

def centeredCoarseUnitCubeSurfaceAtThree_connected :
    connectedIn (L := z4Chain.toLattice)
      centeredCoarseUnitCubeSurfaceAtThree := by
  unfold centeredCoarseUnitCubeSurfaceAtThree
  exact uniformShiftConnected 1 unitCubeSurface_connected

def centeredCoarseUnitCubeRootAtThree : List Nat :=
  geometricSupportIds 3 centeredCoarseUnitCubeSurfaceAtThree

theorem centeredCoarseUnitCubeRootAtThree_mem_cutoffOneFaceSupports :
    centeredCoarseUnitCubeRootAtThree ∈ cutoffOneFaceSupports 3 := by
  unfold centeredCoarseUnitCubeRootAtThree
  exact geometricSupportIds_mem_cutoffOneFaceSupports 3 _

theorem centeredCoarseUnitCubeRootAtThree_sameSupport :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer 3 centeredCoarseUnitCubeRootAtThree)
      centeredCoarseUnitCubeSurfaceAtThree := by
  unfold centeredCoarseUnitCubeRootAtThree
  exact geometricSupportIds_sameSupport
    centeredCoarseUnitCubeSurfaceAtThree_subset_box

theorem centeredCoarseUnitCubeRootAtThree_length :
    centeredCoarseUnitCubeRootAtThree.length = 6 := by
  have hleft :
      (geometricPolymer 3 centeredCoarseUnitCubeRootAtThree).Nodup :=
    geometricPolymer_nodup
      centeredCoarseUnitCubeRootAtThree_mem_cutoffOneFaceSupports
  have hlength := sameSupport_length_eq_of_nodup
    centeredCoarseUnitCubeRootAtThree_sameSupport hleft
      centeredCoarseUnitCubeSurfaceAtThree_nodup
  rw [geometricPolymer_length_eq_support_length] at hlength
  unfold centeredCoarseUnitCubeSurfaceAtThree at hlength
  simpa only [List.length_map, unitCubeSurface_length] using hlength

theorem centeredCoarseUnitCubeRootAtThree_mem_canonicalSurfacePolymers :
    centeredCoarseUnitCubeRootAtThree ∈ canonicalSurfacePolymers 3 := by
  apply connectedFaceSupport_mem_canonicalSurfacePolymers
  · exact centeredCoarseUnitCubeRootAtThree_mem_cutoffOneFaceSupports
  · have hsource : coarseCubeHub ∈ unitCubeSurface :=
      cubeFace_mem_unitCubeSurface .bottomXY
    have hshifted : uniformShiftPlaquette 1 coarseCubeHub ∈
          centeredCoarseUnitCubeSurfaceAtThree := by
      unfold centeredCoarseUnitCubeSurfaceAtThree
      exact List.mem_map.mpr ⟨_, hsource, rfl⟩
    have hencoded :=
      centeredCoarseUnitCubeRootAtThree_sameSupport.2 _ hshifted
    obtain ⟨identifier, hidentifier, _⟩ :=
      decodeMapMember (boxPlaquetteAt 3)
        centeredCoarseUnitCubeRootAtThree _ hencoded
    exact ⟨identifier, hidentifier⟩
  · exact centeredCoarseUnitCubeSurfaceAtThree_connected
    |> geometricSupportIds_connected
      centeredCoarseUnitCubeSurfaceAtThree_subset_box

/-! ## 2. Uniform translation preserves the local incidence count -/

theorem geometricIncidentPlaquettes_uniformShift_length
    (padding : Nat) (faces : List Z4Plaq) (link : Z4Link) :
    (geometricIncidentPlaquettes
        (faces.map (uniformShiftPlaquette padding))
        (uniformShiftLink padding link)).length =
      (geometricIncidentPlaquettes faces link).length := by
  induction faces with
  | nil => rfl
  | cons plaquette rest ih =>
      unfold geometricIncidentPlaquettes at ih ⊢
      simp only [List.map_cons, List.filter_cons]
      by_cases hlink : link ∈ edgesOf plaquette
      · have htranslated : uniformShiftLink padding link ∈
            edgesOf (uniformShiftPlaquette padding plaquette) :=
          (uniformShiftLink_mem_edges_iff padding link plaquette).2 hlink
        simp [hlink, htranslated, ih]
      · have htranslated : uniformShiftLink padding link ∉
            edgesOf (uniformShiftPlaquette padding plaquette) := by
          intro hmem
          exact hlink
            ((uniformShiftLink_mem_edges_iff padding link plaquette).1 hmem)
        simp [hlink, htranslated, ih]

theorem centeredCoarseUnitCubeSurfaceAtThree_incidence_two
    {link : Z4Link}
    (hlink : link ∈
      geometricTouchedLinks centeredCoarseUnitCubeSurfaceAtThree) :
    (geometricIncidentPlaquettes
      centeredCoarseUnitCubeSurfaceAtThree link).length = 2 := by
  obtain ⟨plaquette, hplaquette, hedge⟩ :=
    mem_geometricTouchedLinks.mp hlink
  unfold centeredCoarseUnitCubeSurfaceAtThree at hplaquette ⊢
  obtain ⟨sourcePlaquette, hsourcePlaquette, hplaquetteEq⟩ :=
    decodeMapMember (uniformShiftPlaquette 1)
      unitCubeSurface plaquette hplaquette
  rw [← hplaquetteEq, edgesOf_uniformShiftPlaquette] at hedge
  obtain ⟨sourceLink, hsourceLink, hlinkEq⟩ := List.mem_map.mp hedge
  rw [← hlinkEq]
  have hsourceTouched : sourceLink ∈
      geometricTouchedLinks unitCubeSurface :=
    mem_geometricTouchedLinks.mpr
      ⟨sourcePlaquette, hsourcePlaquette, hsourceLink⟩
  exact (geometricIncidentPlaquettes_uniformShift_length
      1 unitCubeSurface sourceLink).trans
    (unitCube_geometricIncidentPlaquettes_length_eq_two hsourceTouched)

/-! ## 3. Exact cutoff-one activity -/

private theorem centeredCubeLink_mem_of_touched
    {link : Z4Link}
    (hlink : link ∈ touchedPhysicalLinks 3
      (componentLabel centeredCoarseUnitCubeRootAtThree)) :
    link ∈ geometricTouchedLinks centeredCoarseUnitCubeSurfaceAtThree := by
  have hgeometric :=
    (mem_touchedPhysicalLinks_iff_geometric
      centeredCoarseUnitCubeRootAtThree_mem_cutoffOneFaceSupports link).mp
        hlink
  obtain ⟨plaquette, hplaquette, hboundary⟩ :=
    mem_geometricTouchedLinks.mp hgeometric
  exact mem_geometricTouchedLinks.mpr
    ⟨plaquette,
      centeredCoarseUnitCubeRootAtThree_sameSupport.1 plaquette hplaquette,
      hboundary⟩

theorem centeredCoarseUnitCube_geometricIncidentPlaquettes_length_eq_two
    {link : Z4Link}
    (hlink : link ∈ touchedPhysicalLinks 3
      (componentLabel centeredCoarseUnitCubeRootAtThree)) :
    (geometricIncidentPlaquettes
      (geometricPolymer 3 centeredCoarseUnitCubeRootAtThree) link).length =
        2 := by
  have hsame := geometricIncidentPlaquettes_sameSupport
    centeredCoarseUnitCubeRootAtThree_sameSupport link
  have hleft := geometricIncidentPlaquettes_nodup
    centeredCoarseUnitCubeRootAtThree_mem_cutoffOneFaceSupports link
  have hright :
      (geometricIncidentPlaquettes
        centeredCoarseUnitCubeSurfaceAtThree link).Nodup := by
    unfold geometricIncidentPlaquettes
    exact List.filter_sublist.nodup
      centeredCoarseUnitCubeSurfaceAtThree_nodup
  have hlength := sameSupport_length_eq_of_nodup hsame hleft hright
  exact hlength.trans
    (centeredCoarseUnitCubeSurfaceAtThree_incidence_two
      (centeredCubeLink_mem_of_touched hlink))

theorem centeredCoarseUnitCube_geometricLinkMultiplicityFactor_eq_one
    {link : Z4Link}
    (hlink : link ∈ touchedPhysicalLinks 3
      (componentLabel centeredCoarseUnitCubeRootAtThree)) :
    geometricLinkMultiplicityFactor
      (geometricPolymer 3 centeredCoarseUnitCubeRootAtThree) link = 1 := by
  unfold geometricLinkMultiplicityFactor
  rw [centeredCoarseUnitCube_geometricIncidentPlaquettes_length_eq_two hlink]
  rfl

private theorem centeredCoarseUnitCube_geometricProduct_eqv_one_on :
    ∀ links : List Z4Link,
    (∀ link, link ∈ links →
      link ∈ touchedPhysicalLinks 3
        (componentLabel centeredCoarseUnitCubeRootAtThree)) →
    geometricLinkMultiplicityProduct
      (geometricPolymer 3 centeredCoarseUnitCubeRootAtThree) links ≈ 1
  | [], _ => Q'.eqv_refl _
  | link :: rest, hsubset => by
      change (geometricLinkMultiplicityFactor
          (geometricPolymer 3 centeredCoarseUnitCubeRootAtThree) link *
        geometricLinkMultiplicityProduct
          (geometricPolymer 3 centeredCoarseUnitCubeRootAtThree) rest) ≈ 1
      rw [centeredCoarseUnitCube_geometricLinkMultiplicityFactor_eq_one
        (hsubset link List.mem_cons_self)]
      exact Q'.eqv_trans _ (1 * 1) _
        (Q'.mul_eqv_congr_left 1 _ _
          (centeredCoarseUnitCube_geometricProduct_eqv_one_on rest
            (fun item hitem =>
              hsubset item (List.mem_cons_of_mem link hitem))))
        (Q'.one_mul_eqv 1)

theorem centeredCoarseUnitCube_explicitLinkMultiplicityProduct_eqv_one :
    explicitLinkMultiplicityProduct 1 3
      (componentLabel centeredCoarseUnitCubeRootAtThree)
      (touchedIndexedLinks 3
        (componentLabel centeredCoarseUnitCubeRootAtThree)) ≈ 1 :=
  Q'.eqv_trans _ _ _
    (explicitLinkMultiplicityProduct_componentLabel_eqv_geometric
      centeredCoarseUnitCubeRootAtThree_mem_cutoffOneFaceSupports)
    (centeredCoarseUnitCube_geometricProduct_eqv_one_on _
      (fun _ hlink => hlink))

private theorem qmul_congr_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem centeredCoarseUnitCube_canonicalSurfaceActivity_eqv
    (coupling : Q') :
    canonicalSurfaceActivity coupling 3
        centeredCoarseUnitCubeRootAtThree ≈
      (coeffW coupling 1) ^ 6 := by
  have hface := parametricPhysicalFaceFactor_componentLabel_eqv_pow
    coupling centeredCoarseUnitCubeRootAtThree_mem_cutoffOneFaceSupports
  rw [centeredCoarseUnitCubeRootAtThree_length] at hface
  unfold canonicalSurfaceActivity parametricLocalizedSpinFoamWeight
  exact Q'.eqv_trans _ ((coeffW coupling 1) ^ 6 * 1) _
    (qmul_congr_local hface
      centeredCoarseUnitCube_explicitLinkMultiplicityProduct_eqv_one)
    (Q'.mul_one_eqv _)

private theorem qpow_pos_local {value : Q'}
    (hvalue : (0 : Q') < value) :
    ∀ exponent : Nat, (0 : Q') < value ^ exponent
  | 0 => by
      change (0 : Q') < 1
      decide
  | exponent + 1 => Q'.mul_pos hvalue (qpow_pos_local hvalue exponent)

theorem centeredCoarseUnitCube_canonicalSurfaceActivity_pos
    {coupling : Q'} (hcoupling : (0 : Q') < coupling) :
    (0 : Q') < canonicalSurfaceActivity coupling 3
      centeredCoarseUnitCubeRootAtThree := by
  have hcoefficient : (0 : Q') < coeffW coupling 1 :=
    YMGap.Continuum.FusionResidualBound.coeffW_pos hcoupling 1
  have hpower := qpow_pos_local hcoefficient 6
  exact Q'.pos_of_lt_of_le hpower
    (Q'.ge_of_eqv
      (centeredCoarseUnitCube_canonicalSurfaceActivity_eqv coupling))

/-! ## 4. The same carrier at every receding-centered radius -/

def recedingCenteredCoarseUnitCubeRoot (radius : Nat) : List Nat :=
  centeredOffsetCanonicalRoot radius 3
    centeredCoarseUnitCubeRootAtThree

theorem recedingCenteredCoarseUnitCubeRoot_canonical
    {radius : Nat} (hradius : 3 ≤ radius) :
    recedingCenteredCoarseUnitCubeRoot radius ∈
      canonicalSurfacePolymers (centeredBoxBase radius) := by
  unfold recedingCenteredCoarseUnitCubeRoot
  exact centeredOffsetCanonicalRoot_canonical hradius
    centeredCoarseUnitCubeRootAtThree_mem_canonicalSurfacePolymers

private theorem sameSupport_map_local
    {left right : List Z4Plaq} (mapP : Z4Plaq → Z4Plaq)
    (h : sameSupport (L := z4Chain.toLattice) left right) :
    sameSupport (L := z4Chain.toLattice)
      (left.map mapP) (right.map mapP) := by
  constructor
  · intro item hitem
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hitem
    exact List.mem_map.mpr ⟨source, h.1 _ hsource, rfl⟩
  · intro item hitem
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hitem
    exact List.mem_map.mpr ⟨source, h.2 _ hsource, rfl⟩

theorem recedingCenteredCoarseUnitCubeRoot_sameSupport
    {radius : Nat} (hradius : 3 ≤ radius) :
    sameSupport (L := z4Chain.toLattice)
      (geometricPolymer (centeredBoxBase radius)
        (recedingCenteredCoarseUnitCubeRoot radius))
      (centeredCoarseUnitCubeSurfaceAtThree.map
        (uniformShiftPlaquette radius)) := by
  unfold recedingCenteredCoarseUnitCubeRoot
  exact sameSupport_trans
    (centeredOffsetCanonicalRoot_sameSupport hradius
      centeredCoarseUnitCubeRootAtThree_mem_canonicalSurfacePolymers)
    (sameSupport_map_local (uniformShiftPlaquette radius)
      centeredCoarseUnitCubeRootAtThree_sameSupport)

theorem recedingCenteredCoarseUnitCubeRoot_length
    {radius : Nat} (hradius : 3 ≤ radius) :
    (recedingCenteredCoarseUnitCubeRoot radius).length = 6 := by
  have hroot := recedingCenteredCoarseUnitCubeRoot_canonical hradius
  have hleft :
      (geometricPolymer (centeredBoxBase radius)
        (recedingCenteredCoarseUnitCubeRoot radius)).Nodup :=
    geometricPolymer_nodup
      (canonicalSurfacePolymer_mem_faceSupports hroot)
  have hright :
      (centeredCoarseUnitCubeSurfaceAtThree.map
        (uniformShiftPlaquette radius)).Nodup :=
    nodup_map_of_injOn (uniformShiftPlaquette radius)
      centeredCoarseUnitCubeSurfaceAtThree
      centeredCoarseUnitCubeSurfaceAtThree_nodup
      (fun _ _ _ _ heq => uniformShiftPlaquette_injective radius heq)
  have hlength := sameSupport_length_eq_of_nodup
    (recedingCenteredCoarseUnitCubeRoot_sameSupport hradius)
      hleft hright
  rw [geometricPolymer_length_eq_support_length] at hlength
  simpa only [List.length_map,
    centeredCoarseUnitCubeRootAtThree_length] using hlength

private theorem shiftedCenteredSurface_incidence_two
    (radius : Nat) {link : Z4Link}
    (hlink : link ∈ geometricTouchedLinks
      (centeredCoarseUnitCubeSurfaceAtThree.map
        (uniformShiftPlaquette radius))) :
    (geometricIncidentPlaquettes
      (centeredCoarseUnitCubeSurfaceAtThree.map
        (uniformShiftPlaquette radius)) link).length = 2 := by
  obtain ⟨plaquette, hplaquette, hedge⟩ :=
    mem_geometricTouchedLinks.mp hlink
  obtain ⟨sourcePlaquette, hsourcePlaquette, rfl⟩ :=
    List.mem_map.mp hplaquette
  rw [edgesOf_uniformShiftPlaquette] at hedge
  obtain ⟨sourceLink, hsourceLink, rfl⟩ := List.mem_map.mp hedge
  have hsourceTouched : sourceLink ∈
      geometricTouchedLinks centeredCoarseUnitCubeSurfaceAtThree :=
    mem_geometricTouchedLinks.mpr
      ⟨sourcePlaquette, hsourcePlaquette, hsourceLink⟩
  exact (geometricIncidentPlaquettes_uniformShift_length radius
      centeredCoarseUnitCubeSurfaceAtThree sourceLink).trans
    (centeredCoarseUnitCubeSurfaceAtThree_incidence_two hsourceTouched)

private theorem recedingCenteredCubeLink_mem_of_touched
    {radius : Nat} (hradius : 3 ≤ radius) {link : Z4Link}
    (hlink : link ∈ touchedPhysicalLinks (centeredBoxBase radius)
      (componentLabel (recedingCenteredCoarseUnitCubeRoot radius))) :
    link ∈ geometricTouchedLinks
      (centeredCoarseUnitCubeSurfaceAtThree.map
        (uniformShiftPlaquette radius)) := by
  have hroot := recedingCenteredCoarseUnitCubeRoot_canonical hradius
  have hgeometric :=
    (mem_touchedPhysicalLinks_iff_geometric
      (canonicalSurfacePolymer_mem_faceSupports hroot) link).mp hlink
  obtain ⟨plaquette, hplaquette, hboundary⟩ :=
    mem_geometricTouchedLinks.mp hgeometric
  exact mem_geometricTouchedLinks.mpr
    ⟨plaquette,
      (recedingCenteredCoarseUnitCubeRoot_sameSupport hradius).1
        plaquette hplaquette,
      hboundary⟩

theorem recedingCenteredCoarseUnitCube_incidence_two
    {radius : Nat} (hradius : 3 ≤ radius) {link : Z4Link}
    (hlink : link ∈ touchedPhysicalLinks (centeredBoxBase radius)
      (componentLabel (recedingCenteredCoarseUnitCubeRoot radius))) :
    (geometricIncidentPlaquettes
      (geometricPolymer (centeredBoxBase radius)
        (recedingCenteredCoarseUnitCubeRoot radius)) link).length = 2 := by
  have hsame := geometricIncidentPlaquettes_sameSupport
    (recedingCenteredCoarseUnitCubeRoot_sameSupport hradius) link
  have hroot := recedingCenteredCoarseUnitCubeRoot_canonical hradius
  have hleft := geometricIncidentPlaquettes_nodup
    (canonicalSurfacePolymer_mem_faceSupports hroot) link
  have hright :
      (geometricIncidentPlaquettes
        (centeredCoarseUnitCubeSurfaceAtThree.map
          (uniformShiftPlaquette radius)) link).Nodup := by
    unfold geometricIncidentPlaquettes
    exact List.filter_sublist.nodup
      (nodup_map_of_injOn (uniformShiftPlaquette radius)
        centeredCoarseUnitCubeSurfaceAtThree
        centeredCoarseUnitCubeSurfaceAtThree_nodup
        (fun _ _ _ _ heq => uniformShiftPlaquette_injective radius heq))
  have hlength := sameSupport_length_eq_of_nodup hsame hleft hright
  exact hlength.trans
    (shiftedCenteredSurface_incidence_two radius
      (recedingCenteredCubeLink_mem_of_touched hradius hlink))

theorem recedingCenteredCoarseUnitCube_linkFactor_eq_one
    {radius : Nat} (hradius : 3 ≤ radius) {link : Z4Link}
    (hlink : link ∈ touchedPhysicalLinks (centeredBoxBase radius)
      (componentLabel (recedingCenteredCoarseUnitCubeRoot radius))) :
    geometricLinkMultiplicityFactor
      (geometricPolymer (centeredBoxBase radius)
        (recedingCenteredCoarseUnitCubeRoot radius)) link = 1 := by
  unfold geometricLinkMultiplicityFactor
  rw [recedingCenteredCoarseUnitCube_incidence_two hradius hlink]
  rfl

private theorem recedingCenteredCoarseUnitCube_product_eqv_one_on
    {radius : Nat} (hradius : 3 ≤ radius) :
    ∀ links : List Z4Link,
    (∀ link, link ∈ links →
      link ∈ touchedPhysicalLinks (centeredBoxBase radius)
        (componentLabel (recedingCenteredCoarseUnitCubeRoot radius))) →
    geometricLinkMultiplicityProduct
      (geometricPolymer (centeredBoxBase radius)
        (recedingCenteredCoarseUnitCubeRoot radius)) links ≈ 1
  | [], _ => Q'.eqv_refl _
  | link :: rest, hsubset => by
      change (geometricLinkMultiplicityFactor
          (geometricPolymer (centeredBoxBase radius)
            (recedingCenteredCoarseUnitCubeRoot radius)) link *
        geometricLinkMultiplicityProduct
          (geometricPolymer (centeredBoxBase radius)
            (recedingCenteredCoarseUnitCubeRoot radius)) rest) ≈ 1
      rw [recedingCenteredCoarseUnitCube_linkFactor_eq_one hradius
        (hsubset link List.mem_cons_self)]
      exact Q'.eqv_trans _ (1 * 1) _
        (Q'.mul_eqv_congr_left 1 _ _
          (recedingCenteredCoarseUnitCube_product_eqv_one_on hradius rest
            (fun item hitem =>
              hsubset item (List.mem_cons_of_mem link hitem))))
        (Q'.one_mul_eqv 1)

theorem recedingCenteredCoarseUnitCube_linkProduct_eqv_one
    {radius : Nat} (hradius : 3 ≤ radius) :
    explicitLinkMultiplicityProduct 1 (centeredBoxBase radius)
      (componentLabel (recedingCenteredCoarseUnitCubeRoot radius))
      (touchedIndexedLinks (centeredBoxBase radius)
        (componentLabel (recedingCenteredCoarseUnitCubeRoot radius))) ≈ 1 :=
  Q'.eqv_trans _ _ _
    (explicitLinkMultiplicityProduct_componentLabel_eqv_geometric
      (canonicalSurfacePolymer_mem_faceSupports
        (recedingCenteredCoarseUnitCubeRoot_canonical hradius)))
    (recedingCenteredCoarseUnitCube_product_eqv_one_on hradius _
      (fun _ hlink => hlink))

theorem recedingCenteredCoarseUnitCube_activity_eqv
    (coupling : Q') {radius : Nat} (hradius : 3 ≤ radius) :
    canonicalSurfaceActivity coupling (centeredBoxBase radius)
        (recedingCenteredCoarseUnitCubeRoot radius) ≈
      (coeffW coupling 1) ^ 6 := by
  have hroot := recedingCenteredCoarseUnitCubeRoot_canonical hradius
  have hface := parametricPhysicalFaceFactor_componentLabel_eqv_pow
    coupling (canonicalSurfacePolymer_mem_faceSupports hroot)
  rw [recedingCenteredCoarseUnitCubeRoot_length hradius] at hface
  unfold canonicalSurfaceActivity parametricLocalizedSpinFoamWeight
  exact Q'.eqv_trans _ ((coeffW coupling 1) ^ 6 * 1) _
    (qmul_congr_local hface
      (recedingCenteredCoarseUnitCube_linkProduct_eqv_one hradius))
    (Q'.mul_one_eqv _)

#print axioms centeredCoarseUnitCubeSurfaceAtThree_subset_box
#print axioms centeredCoarseUnitCubeSurfaceAtThree_connected
#print axioms centeredCoarseUnitCubeRootAtThree_mem_canonicalSurfacePolymers
#print axioms geometricIncidentPlaquettes_uniformShift_length
#print axioms centeredCoarseUnitCubeSurfaceAtThree_incidence_two
#print axioms centeredCoarseUnitCube_geometricIncidentPlaquettes_length_eq_two
#print axioms centeredCoarseUnitCube_canonicalSurfaceActivity_eqv
#print axioms centeredCoarseUnitCube_canonicalSurfaceActivity_pos
#print axioms recedingCenteredCoarseUnitCubeRoot_canonical
#print axioms recedingCenteredCoarseUnitCubeRoot_sameSupport
#print axioms recedingCenteredCoarseUnitCubeRoot_length
#print axioms recedingCenteredCoarseUnitCube_incidence_two
#print axioms recedingCenteredCoarseUnitCube_activity_eqv

end YMGap.Continuum.Z4CenteredCoarseUnitCubeActivity
