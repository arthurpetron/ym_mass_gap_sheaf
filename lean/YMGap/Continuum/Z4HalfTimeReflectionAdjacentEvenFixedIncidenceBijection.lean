/-
# Face-major versus link-major fixed incidence enumeration

The fixed-interface transition product can be grouped either by fixed faces or
by fixed links.  This file proves that the two literal incidence lists are a
permutation: every fixed face contributes its four ordered boundary links, and
every fixed link contributes its actual fixed incident face IDs.  No counting
or incidence multiplicity is assumed.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceTrajectoryAssembly
import YMGap.Continuum.Z4UnitCubeIncidenceParity

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceBijection

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkEndpointFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedWordTrajectoryFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4UnitCubeIncidenceParity

abbrev FixedFaceLinkIncidence := Nat × Z4Link

def adjacentEvenFixedFaceMajorIncidences
    (radius : Nat) : List FixedFaceLinkIncidence :=
  (adjacentEvenFixedFaceIds radius).flatMap (fun id =>
    (adjacentEvenFixedFaceLinks radius id).map
      (fun link => (id, link)))

def adjacentEvenFixedLinkMajorIncidences
    (radius : Nat) : List FixedFaceLinkIncidence :=
  (adjacentEvenFixedLinks radius).flatMap (fun link =>
    (adjacentEvenIncidentFixedFaceIds radius link).map
      (fun id => (id, link)))

theorem mem_adjacentEvenFixedFaceMajorIncidences
    {radius : Nat} {incidence : FixedFaceLinkIncidence} :
    incidence ∈ adjacentEvenFixedFaceMajorIncidences radius ↔
      incidence.1 ∈ adjacentEvenFixedFaceIds radius ∧
      incidence.2 ∈
        adjacentEvenFixedFaceLinks radius incidence.1 := by
  constructor
  · intro hmem
    obtain ⟨id, hid, hblock⟩ := List.mem_flatMap.mp hmem
    obtain ⟨link, hlink, heq⟩ := List.mem_map.mp hblock
    have hidEq : id = incidence.1 := by
      rw [← heq]
    have hlinkEq : link = incidence.2 := by
      rw [← heq]
    exact ⟨hidEq ▸ hid, hidEq ▸ hlinkEq ▸ hlink⟩
  · intro hparts
    apply List.mem_flatMap.mpr
    refine ⟨incidence.1, hparts.1, ?_⟩
    apply List.mem_map.mpr
    exact ⟨incidence.2, hparts.2, by cases incidence; rfl⟩

theorem mem_adjacentEvenFixedLinkMajorIncidences
    {radius : Nat} {incidence : FixedFaceLinkIncidence} :
    incidence ∈ adjacentEvenFixedLinkMajorIncidences radius ↔
      incidence.2 ∈ adjacentEvenFixedLinks radius ∧
      incidence.1 ∈
        adjacentEvenIncidentFixedFaceIds radius incidence.2 := by
  constructor
  · intro hmem
    obtain ⟨link, hlink, hblock⟩ := List.mem_flatMap.mp hmem
    obtain ⟨id, hid, heq⟩ := List.mem_map.mp hblock
    have hidEq : id = incidence.1 := by
      rw [← heq]
    have hlinkEq : link = incidence.2 := by
      rw [← heq]
    exact ⟨hlinkEq ▸ hlink, hlinkEq ▸ hidEq ▸ hid⟩
  · intro hparts
    apply List.mem_flatMap.mpr
    refine ⟨incidence.2, hparts.1, ?_⟩
    apply List.mem_map.mpr
    exact ⟨incidence.1, hparts.2, by cases incidence; rfl⟩

theorem mem_adjacentEvenIncidentFixedFaceIds
    {radius id : Nat} {link : Z4Link} :
    id ∈ adjacentEvenIncidentFixedFaceIds radius link ↔
      id ∈ slabIncidentPlaqIds
        (adjacentEvenExtent radius) link ∧
      adjacentEvenPlaquetteSide radius
        (slabPlaquetteAt (adjacentEvenExtent radius) id) = .fixed := by
  exact mem_partitionBySide_fixed _ _ _

private theorem incident_id_mem_fixedFaceLinks
    {radius id : Nat} {link : Z4Link}
    (hid : id ∈ slabIncidentPlaqIds
      (adjacentEvenExtent radius) link) :
    link ∈ adjacentEvenFixedFaceLinks radius id := by
  obtain ⟨plaquette, hindexed, hlink⟩ :=
    mem_slabIncidentPlaqIds.mp hid
  have hlookup :
      slabPlaquetteAt (adjacentEvenExtent radius) id = plaquette := by
    unfold slabPlaquetteAt
    exact enumerate_getD_of_mem fallbackPlaquette hindexed
  unfold adjacentEvenFixedFaceLinks
  rw [hlookup]
  exact hlink

theorem adjacentEvenFixedIncidence_mem_iff
    {radius : Nat} {incidence : FixedFaceLinkIncidence} :
    incidence ∈ adjacentEvenFixedFaceMajorIncidences radius ↔
      incidence ∈ adjacentEvenFixedLinkMajorIncidences radius := by
  rw [mem_adjacentEvenFixedFaceMajorIncidences,
    mem_adjacentEvenFixedLinkMajorIncidences]
  constructor
  · intro hface
    have hlinkFixed := adjacentEvenFixedFaceLink_mem_fixedSlabLinks
      hface.1 hface.2
    have hidIncident := adjacentEvenFixedFaceId_mem_linkIncidence
      hface.1 hface.2
    have hside := (mem_adjacentEvenFixedFaceIds.mp hface.1).2
    exact ⟨hlinkFixed,
      mem_adjacentEvenIncidentFixedFaceIds.mpr
        ⟨hidIncident, hside⟩⟩
  · intro hlink
    have hidParts :=
      mem_adjacentEvenIncidentFixedFaceIds.mp hlink.2
    have hidPhysical := slabIncidentPlaqId_physical hidParts.1
    have hidFixed : incidence.1 ∈
        adjacentEvenFixedFaceIds radius :=
      mem_adjacentEvenFixedFaceIds.mpr
        ⟨hidPhysical, hidParts.2⟩
    exact ⟨hidFixed,
      incident_id_mem_fixedFaceLinks hidParts.1⟩

/-! ## Duplicate-free incidence lists -/

private theorem nodup_map_of_injective
    {A B : Type} (f : A → B)
    (hf : ∀ {left right}, f left = f right → left = right) :
    ∀ {items : List A}, items.Nodup → (items.map f).Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      refine ⟨?_, nodup_map_of_injective f hf hparts.2⟩
      intro hmem
      obtain ⟨item, hitem, heq⟩ := List.mem_map.mp hmem
      exact hparts.1 ((hf heq) ▸ hitem)

private theorem nodup_flatMap_of_disjoint_blocks
    {A B : Type} (block : A → List B) :
    ∀ source : List A, source.Nodup →
      (∀ item, item ∈ source → (block item).Nodup) →
      (∀ left, left ∈ source → ∀ right, right ∈ source →
        left ≠ right → ∀ value, value ∈ block left →
          value ∉ block right) →
      (source.flatMap block).Nodup
  | [], _, _, _ => List.nodup_nil
  | head :: tail, hsource, hblocks, hdisjoint => by
      have hparts := List.nodup_cons.mp hsource
      rw [List.flatMap_cons]
      apply List.nodup_append.mpr
      refine ⟨hblocks head List.mem_cons_self,
        nodup_flatMap_of_disjoint_blocks block tail hparts.2
          (fun item hitem =>
            hblocks item (List.mem_cons_of_mem head hitem))
          (fun left hleft right hright hne =>
            hdisjoint left (List.mem_cons_of_mem head hleft)
              right (List.mem_cons_of_mem head hright) hne), ?_⟩
      intro value hhead other htail heq
      have hvalueTail : value ∈ tail.flatMap block := by
        rw [heq]
        exact htail
      obtain ⟨item, hitem, hvalueItem⟩ :=
        List.mem_flatMap.mp hvalueTail
      have hne : head ≠ item := by
        intro heqItem
        subst item
        exact hparts.1 hitem
      exact (hdisjoint head List.mem_cons_self item
        (List.mem_cons_of_mem head hitem) hne value hhead)
        hvalueItem

theorem adjacentEvenFixedFaceMajorIncidences_nodup (radius : Nat) :
    (adjacentEvenFixedFaceMajorIncidences radius).Nodup := by
  unfold adjacentEvenFixedFaceMajorIncidences
  apply nodup_flatMap_of_disjoint_blocks
  · exact adjacentEvenFixedFaceIds_nodup radius
  · intro id _
    apply nodup_map_of_injective (fun link => (id, link))
      (fun h => congrArg Prod.snd h)
    unfold adjacentEvenFixedFaceLinks
    exact edgesOf_nodup _
  · intro left _ right _ hne value hleft hright
    obtain ⟨leftLink, _, hleftEq⟩ := List.mem_map.mp hleft
    obtain ⟨rightLink, _, hrightEq⟩ := List.mem_map.mp hright
    have hfirst : left = right := by
      exact congrArg Prod.fst (hleftEq.trans hrightEq.symm)
    exact hne hfirst

theorem adjacentEvenFixedLinkMajorIncidences_nodup (radius : Nat) :
    (adjacentEvenFixedLinkMajorIncidences radius).Nodup := by
  unfold adjacentEvenFixedLinkMajorIncidences
  apply nodup_flatMap_of_disjoint_blocks
  · exact adjacentEvenFixedLinks_nodup radius
  · intro link _
    apply nodup_map_of_injective (fun id => (id, link))
      (fun h => congrArg Prod.fst h)
    exact adjacentEvenIncidentFixedFaceIds_nodup radius link
  · intro left _ right _ hne value hleft hright
    obtain ⟨leftId, _, hleftEq⟩ := List.mem_map.mp hleft
    obtain ⟨rightId, _, hrightEq⟩ := List.mem_map.mp hright
    have hsecond : left = right := by
      exact congrArg Prod.snd (hleftEq.trans hrightEq.symm)
    exact hne hsecond

/-- The load-bearing incidence interchange: face-major and link-major
enumerations are literal permutations of the same noduplicated pairs. -/
theorem adjacentEvenFixedFaceLinkIncidences_perm (radius : Nat) :
    (adjacentEvenFixedFaceMajorIncidences radius).Perm
      (adjacentEvenFixedLinkMajorIncidences radius) := by
  apply perm_of_nodup_mem_iff
    (adjacentEvenFixedFaceMajorIncidences radius)
    (adjacentEvenFixedLinkMajorIncidences radius)
    (adjacentEvenFixedFaceMajorIncidences_nodup radius)
    (adjacentEvenFixedLinkMajorIncidences_nodup radius)
  intro incidence
  exact adjacentEvenFixedIncidence_mem_iff

#print axioms adjacentEvenFixedIncidence_mem_iff
#print axioms adjacentEvenFixedFaceMajorIncidences_nodup
#print axioms adjacentEvenFixedLinkMajorIncidences_nodup
#print axioms adjacentEvenFixedFaceLinkIncidences_perm

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceBijection
