/-
# Exact production multiplicities for the difference boundary

The actual 48 lower-link and 20 fixed-link incidence words reduce, by deleting
only zero-labelled faces, to the twelve cube-edge and eight cube-corner
triples. The difference boundary makes every remaining triple admissible,
both for the source and its literal inward mate. Every production factor is
therefore exactly one, at arbitrary cutoff. This is a physical link statement,
not an auxiliary dynamics or a uniform spectral estimate.
-/

import YMGap.Continuum.BF4PhysicalCubeDifferenceBoundary
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence

namespace YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryMultiplicity

set_option autoImplicit false

open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundary
open YMGap.Continuum.BF4PhysicalHalfCubeSupport
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateHeatBound
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

def tripleFaces (triple : Nat × Nat × Nat) : List Nat :=
  [triple.1, triple.2.1, triple.2.2]

def cubeDifferenceLowerActive : List Nat :=
  centralLowerCubeFaceIds ++ cubeDifferenceBoundaryIds

def activeIncidentWord (active : List Nat) (link : Z4Link) : List Nat :=
  (slabIncidentPlaqIds 1 link).filter (fun face => decide (face ∈ active))

theorem lower_active_catalog (link : Z4Link) (hlink : link ∈ centralLowerLinks 0) :
    activeIncidentWord cubeDifferenceLowerActive link ∈
      [] :: cubeDifferenceEdges.map tripleFaces := by
  have hg : (centralLowerLinks 0).all (fun link => decide
      (activeIncidentWord cubeDifferenceLowerActive link ∈
        [] :: cubeDifferenceEdges.map tripleFaces)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hg link hlink)

theorem fixed_active_catalog (link : Z4Link) (hlink : link ∈ centralFixedLinks 0) :
    activeIncidentWord cubeDifferenceBoundaryIds link ∈
      [] :: cubeDifferenceCorners.map tripleFaces := by
  have hg : (centralFixedLinks 0).all (fun link => decide
      (activeIncidentWord cubeDifferenceBoundaryIds link ∈
        [] :: cubeDifferenceCorners.map tripleFaces)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hg link hlink)

private theorem filter_zeroExtension (active : List Nat) (physical : EdgeLabelling)
    (hz : ∀ face, face ∉ active → physical face = 0) (faces : List Nat) :
    ZeroExtension
      ((faces.filter (fun face => decide (face ∈ active))).map physical)
      (faces.map physical) := by
  induction faces with
  | nil => exact ZeroExtension.nil
  | cons face faces ih =>
      by_cases hface : face ∈ active
      · simpa only [List.filter_cons, hface, decide_true, Bool.true_eq, ↓reduceIte,
          List.map_cons] using ZeroExtension.keep (physical face) ih
      · simpa only [List.filter_cons, hface, decide_false, Bool.false_eq_true,
          ↓reduceIte, List.map_cons, hz face hface] using ZeroExtension.insertZero ih

/-- A geometry catalog and admissible triples determine the full production
count, including all zero insertions and the production auxiliary cutoff. -/
theorem linkMultiplicity_eq_one_of_catalog (K : Nat) (physical : EdgeLabelling)
    (active : List Nat) (triples : List (Nat × Nat × Nat)) (link : Z4Link)
    (hbound : ∀ face, physical face ≤ K)
    (hz : ∀ face, face ∉ active → physical face = 0)
    (hcatalog : activeIncidentWord active link ∈ [] :: triples.map tripleFaces)
    (hfusion : ∀ triple, triple ∈ triples →
      fusionOK (physical triple.1) (physical triple.2.1) (physical triple.2.2) = true) :
    slabExplicitLinkMultiplicity K 1 physical link = 1 := by
  have hlen : (activeIncidentWord active link).length ≤ 6 :=
    Nat.le_trans (List.length_filter_le _ _) (slabIncidentPlaqIds_length_le_six 1 link)
  have hb : SpinsBounded (linkAuxiliaryCutoff K)
      ((activeIncidentWord active link).map physical) := by
    intro spin hspin
    obtain ⟨face, _, rfl⟩ := List.mem_map.mp hspin
    exact Nat.le_trans (hbound face) (externalCutoff_le_linkAuxiliaryCutoff K)
  have hcount := explicitValenceMultiplicity_zeroExtension
    (filter_zeroExtension active physical hz (slabIncidentPlaqIds 1 link))
    (by simpa only [List.length_map] using hlen)
    (by simpa only [List.length_map] using slabIncidentPlaqIds_length_le_six 1 link) hb
  unfold slabExplicitLinkMultiplicity
  rw [← hcount]
  change explicitValenceMultiplicity (linkAuxiliaryCutoff K)
    ((activeIncidentWord active link).map physical).length
    (externalSpinsOfList ((activeIncidentWord active link).map physical)) = 1
  rcases List.mem_cons.mp hcatalog with hempty | htriple
  · rw [hempty]; rfl
  · obtain ⟨triple, ht, heq⟩ := List.mem_map.mp htriple
    rw [← heq]
    change boolMultiplicity
      (fusionOK (physical triple.1) (physical triple.2.1) (physical triple.2.2)) = 1
    rw [hfusion triple ht]; rfl

theorem assembled_bounded (K : Nat) (state boundary : EdgeLabelling)
    (hs : ∀ face, state face ≤ K) (hb : ∀ face, boundary face ≤ K) :
    ∀ face, assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling face ≤ K := by
  intro face
  unfold assembleReflectedSlabLabelling
  split
  · split
    · exact hs face
    · exact hb face
    · exact Nat.zero_le K
  · exact Nat.zero_le K

theorem assembled_zero_off_support (state boundary : EdgeLabelling)
    (sourceIds boundaryIds : List Nat)
    (hs : ∀ face, face ∉ sourceIds → state face = 0)
    (hb : ∀ face, face ∉ boundaryIds → boundary face = 0)
    (face : Nat) (hoff : face ∉ sourceIds ++ boundaryIds) :
    assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling face = 0 := by
  have hsource : face ∉ sourceIds := fun h => hoff (List.mem_append_left _ h)
  have hboundary : face ∉ boundaryIds := fun h => hoff (List.mem_append_right _ h)
  unfold assembleReflectedSlabLabelling
  split
  · split
    · exact hs face hsource
    · exact hb face hboundary
    · rfl
  · rfl

theorem cubeSupported_bounded (K : Nat) (state : EdgeLabelling)
    (hbound : ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K)
    (hz : ∀ face, face ∉ centralLowerCubeFaceIds → state face = 0) :
    ∀ face, state face ≤ K := by
  intro face
  by_cases hface : face ∈ centralLowerCubeFaceIds
  · exact hbound face hface
  · rw [hz face hface]; exact Nat.zero_le K

theorem cubeMate_bounded (K : Nat) (hK : 1 ≤ K) (state : EdgeLabelling)
    (hb : ∀ face, state face ≤ K) :
    ∀ face, centralLowerCubeEvenInwardMatePhysical state face ≤ K := by
  intro face
  unfold centralLowerCubeEvenInwardMatePhysical
  split
  · unfold evenInwardMateLabel
    split
    · exact hK
    · exact Nat.le_trans (Nat.sub_le _ _) (hb face)
  · exact hb face

theorem lower_multiplicity_one (K : Nat) (state boundary : EdgeLabelling)
    (hs : ∀ face, state face ≤ K) (hb : ∀ face, boundary face ≤ K)
    (hz : ∀ face, face ∉ centralLowerCubeFaceIds → state face = 0)
    (hbz : ∀ face, face ∉ cubeDifferenceBoundaryIds → boundary face = 0)
    (hf : ∀ edge, edge ∈ cubeDifferenceEdges →
      fusionOK (state edge.1) (state edge.2.1) (boundary edge.2.2) = true)
    (link : Z4Link) (hlink : link ∈ centralLowerLinks 0) :
    slabExplicitLinkMultiplicity K 1
      (assembleReflectedSlabLabelling 0 state boundary zeroEdgeLabelling) link = 1 := by
  apply linkMultiplicity_eq_one_of_catalog K _ cubeDifferenceLowerActive cubeDifferenceEdges
    link (assembled_bounded K state boundary hs hb)
    (assembled_zero_off_support state boundary _ _ hz hbz) (lower_active_catalog link hlink)
  intro edge he
  have hg := cubeDifferenceEdge_faces edge he
  rw [assembled_lower state boundary (centralLowerCubeFaceIds_subset_lower _ hg.1),
    assembled_lower state boundary (centralLowerCubeFaceIds_subset_lower _ hg.2.1),
    assembled_fixed state boundary hg.2.2]
  exact hf edge he

theorem difference_source_multiplicity_one (K : Nat) (state : EdgeLabelling)
    (hb : ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K)
    (hz : ∀ face, face ∉ centralLowerCubeFaceIds → state face = 0)
    (link : Z4Link) (hlink : link ∈ centralLowerLinks 0) :
    slabExplicitLinkMultiplicity K 1 (assembleReflectedSlabLabelling 0 state
      (cubeDifferenceBoundary state) zeroEdgeLabelling) link = 1 := by
  apply lower_multiplicity_one K state (cubeDifferenceBoundary state)
    (cubeSupported_bounded K state hb hz) (cubeDifferenceBoundary_bounded K state hb)
    hz (fun _ h => cubeDifferenceBoundary_zero_off state h) _ link hlink
  intro edge he
  rw [cubeDifferenceBoundary_on_edge state edge he]
  exact spinDistance_fusion _ _

theorem difference_mate_multiplicity_one (K : Nat) (hK : 1 ≤ K) (state : EdgeLabelling)
    (hb : ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K)
    (hz : ∀ face, face ∉ centralLowerCubeFaceIds → state face = 0)
    (link : Z4Link) (hlink : link ∈ centralLowerLinks 0) :
    slabExplicitLinkMultiplicity K 1 (assembleReflectedSlabLabelling 0
      (centralLowerCubeEvenInwardMatePhysical state)
      (cubeDifferenceBoundary state) zeroEdgeLabelling) link = 1 := by
  apply lower_multiplicity_one K _ _
    (cubeMate_bounded K hK state (cubeSupported_bounded K state hb hz))
    (cubeDifferenceBoundary_bounded K state hb) _
    (fun _ h => cubeDifferenceBoundary_zero_off state h) _ link hlink
  · intro face hf
    rw [centralLowerCubeEvenInwardMatePhysical_off_cube state hf, hz face hf]
  · intro edge he
    have hg := cubeDifferenceEdge_faces edge he
    rw [centralLowerCubeEvenInwardMatePhysical_on_cube state hg.1,
      centralLowerCubeEvenInwardMatePhysical_on_cube state hg.2.1,
      cubeDifferenceBoundary_on_edge state edge he]
    exact spinDistance_mate_fusion _ _

theorem difference_fixed_multiplicity_one (K : Nat) (state : EdgeLabelling)
    (hb : ∀ face, face ∈ centralLowerCubeFaceIds → state face ≤ K)
    (link : Z4Link) (hlink : link ∈ centralFixedLinks 0) :
    slabExplicitLinkMultiplicity K 1 (assembleReflectedSlabLabelling 0 zeroEdgeLabelling
      (cubeDifferenceBoundary state) zeroEdgeLabelling) link = 1 := by
  refine linkMultiplicity_eq_one_of_catalog K _ cubeDifferenceBoundaryIds cubeDifferenceCorners
    link (assembled_bounded K _ _ (fun _ => Nat.zero_le K)
      (cubeDifferenceBoundary_bounded K state hb)) ?_ (fixed_active_catalog link hlink) ?_
  · intro face hf
    exact assembled_zero_off_support zeroEdgeLabelling (cubeDifferenceBoundary state)
      [] cubeDifferenceBoundaryIds (fun _ _ => rfl)
      (fun _ h => cubeDifferenceBoundary_zero_off state h) face hf
  · intro corner hc
    have hg : corner.1 ∈ centralFixedFaceIds 0 ∧ corner.2.1 ∈ centralFixedFaceIds 0 ∧
        corner.2.2 ∈ centralFixedFaceIds 0 := by
      simp only [cubeDifferenceCorners, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    rw [assembled_fixed _ _ hg.1, assembled_fixed _ _ hg.2.1, assembled_fixed _ _ hg.2.2]
    exact cubeDifferenceBoundary_corner_fusion state corner hc

end YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryMultiplicity

#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryMultiplicity.lower_active_catalog
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryMultiplicity.fixed_active_catalog
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryMultiplicity.linkMultiplicity_eq_one_of_catalog
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryMultiplicity.assembled_bounded
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryMultiplicity.assembled_zero_off_support
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryMultiplicity.cubeSupported_bounded
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryMultiplicity.cubeMate_bounded
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryMultiplicity.lower_multiplicity_one
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryMultiplicity.difference_source_multiplicity_one
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryMultiplicity.difference_mate_multiplicity_one
#print axioms YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryMultiplicity.difference_fixed_multiplicity_one
