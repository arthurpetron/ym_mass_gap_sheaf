/-
# Outer-factor locality for the adjacent-even physical kernel

The lower non-interface factor of an adjacent-even reflected assembly reads
only its left half-state.  This is stronger than the corresponding odd-slab
statement: every plaquette incident to a lower adjacent-even link is itself
lower, so neither the fixed boundary nor the reflected right half can enter.

The proof is local and symbolic.  It does not evaluate any bounded labelling
enumerator.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAssembledSlabFactorization
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableFixedWordSymmetry

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOuterFactorLocality

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAssembledSlabFactorization
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkGlobalTrajectoryIntegration
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableFixedWordSymmetry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReflectedBoundaryAssembly
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneReflectedFactor
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Strict side locality of lower and upper links -/

theorem mem_adjacentEvenLowerLinks {radius : Nat} {link : Z4Link} :
    link ∈ adjacentEvenLowerLinks radius ↔
      link ∈ boundaryCompleteSlabLinks (adjacentEvenExtent radius) ∧
      adjacentEvenLinkSide radius link = .lower := by
  exact mem_partitionBySide_lower _ _ _

theorem mem_adjacentEvenUpperLinks {radius : Nat} {link : Z4Link} :
    link ∈ adjacentEvenUpperLinks radius ↔
      link ∈ boundaryCompleteSlabLinks (adjacentEvenExtent radius) ∧
      adjacentEvenLinkSide radius link = .upper := by
  exact mem_partitionBySide_upper _ _ _

/-- Every plaquette incident to a lower adjacent-even link is lower. -/
theorem adjacentEven_lower_link_incident_face_lower
    {radius : Nat} {link : Z4Link} {plaquette : Z4Plaq}
    (hlink : adjacentEvenLinkSide radius link = .lower)
    (hincidence : link ∈ edgesOf plaquette) :
    adjacentEvenPlaquetteSide radius plaquette = .lower := by
  simp only [edgesOf, List.mem_cons, List.not_mem_nil,
    or_false] at hincidence
  rcases hincidence with rfl | rfl | rfl | rfl
  all_goals obtain ⟨⟨a, b, c, time⟩, plane⟩ := plaquette
  all_goals cases plane
  all_goals simp only [dirsOf, addE, adjacentEvenLinkSide,
    adjacentEvenPlaquetteSide, adjacentEvenSpatialSide,
    adjacentEvenTemporalSide, adjacentEvenCenter] at hlink ⊢
  all_goals repeat' split at hlink
  all_goals repeat' split
  all_goals simp_all
  all_goals omega

/-- Every plaquette incident to an upper adjacent-even link is upper. -/
theorem adjacentEven_upper_link_incident_face_upper
    {radius : Nat} {link : Z4Link} {plaquette : Z4Plaq}
    (hlink : adjacentEvenLinkSide radius link = .upper)
    (hincidence : link ∈ edgesOf plaquette) :
    adjacentEvenPlaquetteSide radius plaquette = .upper := by
  simp only [edgesOf, List.mem_cons, List.not_mem_nil,
    or_false] at hincidence
  rcases hincidence with rfl | rfl | rfl | rfl
  all_goals obtain ⟨⟨a, b, c, time⟩, plane⟩ := plaquette
  all_goals cases plane
  all_goals simp only [dirsOf, addE, adjacentEvenLinkSide,
    adjacentEvenPlaquetteSide, adjacentEvenSpatialSide,
    adjacentEvenTemporalSide, adjacentEvenCenter] at hlink ⊢
  all_goals repeat' split at hlink
  all_goals repeat' split
  all_goals simp_all
  all_goals omega

theorem adjacentEvenLowerLink_incident_face_lower
    {radius id : Nat} {link : Z4Link}
    (hlink : link ∈ adjacentEvenLowerLinks radius)
    (hid : id ∈ slabIncidentPlaqIds
      (adjacentEvenExtent radius) link) :
    adjacentEvenPlaquetteSide radius
        (slabPlaquetteAt (adjacentEvenExtent radius) id) = .lower := by
  obtain ⟨plaquette, hindexed, hincidence⟩ :=
    mem_slabIncidentPlaqIds.mp hid
  have hlookup :
      slabPlaquetteAt (adjacentEvenExtent radius) id = plaquette := by
    unfold slabPlaquetteAt
    exact enumerate_getD_of_mem fallbackPlaquette hindexed
  rw [hlookup]
  exact adjacentEven_lower_link_incident_face_lower
    (mem_adjacentEvenLowerLinks.mp hlink).2 hincidence

theorem adjacentEvenUpperLink_incident_face_upper
    {radius id : Nat} {link : Z4Link}
    (hlink : link ∈ adjacentEvenUpperLinks radius)
    (hid : id ∈ slabIncidentPlaqIds
      (adjacentEvenExtent radius) link) :
    adjacentEvenPlaquetteSide radius
        (slabPlaquetteAt (adjacentEvenExtent radius) id) = .upper := by
  obtain ⟨plaquette, hindexed, hincidence⟩ :=
    mem_slabIncidentPlaqIds.mp hid
  have hlookup :
      slabPlaquetteAt (adjacentEvenExtent radius) id = plaquette := by
    unfold slabPlaquetteAt
    exact enumerate_getD_of_mem fallbackPlaquette hindexed
  rw [hlookup]
  exact adjacentEven_upper_link_incident_face_upper
    (mem_adjacentEvenUpperLinks.mp hlink).2 hincidence

/-! ## 2. Exact assembled-factor locality -/

theorem adjacentEvenLowerFactor_eq_of_eq_on_lower
    (w : Q') (K radius : Nat) (left right : EdgeLabelling)
    (hagree : ∀ id,
      id ∈ slabPhysicalFaceEdges (adjacentEvenExtent radius) →
      adjacentEvenPlaquetteSide radius
          (slabPlaquetteAt (adjacentEvenExtent radius) id) = .lower →
      left id = right id) :
    adjacentEvenLowerFactor w K radius left =
      adjacentEvenLowerFactor w K radius right := by
  have hface :
      slabFaceFactorOn w K left (adjacentEvenLowerFaceIds radius) =
        slabFaceFactorOn w K right
          (adjacentEvenLowerFaceIds radius) := by
    unfold slabFaceFactorOn
    rw [eliminateLinks_eq_listQProduct,
      eliminateLinks_eq_listQProduct]
    apply listQProduct_congr
    intro id hid
    have hparts := mem_adjacentEvenLowerFaceIds.mp hid
    rw [hagree id hparts.1 hparts.2]
  have hlinks :
      slabLinkMultiplicityProductOn K
          (adjacentEvenExtent radius) left
          (adjacentEvenLowerLinks radius) =
        slabLinkMultiplicityProductOn K
          (adjacentEvenExtent radius) right
          (adjacentEvenLowerLinks radius) := by
    unfold slabLinkMultiplicityProductOn
    apply natListProduct_congr
    intro link hlink
    unfold slabExplicitLinkMultiplicity
    have hspins :
        (slabIncidentPlaqIds
            (adjacentEvenExtent radius) link).map left =
          (slabIncidentPlaqIds
            (adjacentEvenExtent radius) link).map right := by
      apply List.map_congr_left
      intro id hid
      rw [hagree id (slabIncidentPlaqId_physical hid)
        (adjacentEvenLowerLink_incident_face_lower hlink hid)]
    rw [hspins]
  unfold adjacentEvenLowerFactor
  rw [hface, hlinks]

/-- The complete lower face/link factor of an assembled slab is the literal
lower factor of its left half-state. -/
theorem adjacentEvenLowerFactor_assemble_only_left
    (w : Q') (K radius : Nat)
    (left boundary right : EdgeLabelling) :
    adjacentEvenLowerFactor w K radius
        (assembleAdjacentEvenReflectedSlabLabelling
          radius left boundary right) =
      adjacentEvenLowerFactor w K radius left := by
  have hface :
      slabFaceFactorOn w K
          (assembleAdjacentEvenReflectedSlabLabelling
            radius left boundary right)
          (adjacentEvenLowerFaceIds radius) =
        slabFaceFactorOn w K left
          (adjacentEvenLowerFaceIds radius) := by
    unfold slabFaceFactorOn
    rw [eliminateLinks_eq_listQProduct,
      eliminateLinks_eq_listQProduct]
    apply listQProduct_congr
    intro id hid
    have hparts := mem_adjacentEvenLowerFaceIds.mp hid
    rw [assembleAdjacentEvenReflectedSlabLabelling_lower
      hparts.1 hparts.2]
  have hlinks :
      slabLinkMultiplicityProductOn K
          (adjacentEvenExtent radius)
          (assembleAdjacentEvenReflectedSlabLabelling
            radius left boundary right)
          (adjacentEvenLowerLinks radius) =
        slabLinkMultiplicityProductOn K
          (adjacentEvenExtent radius) left
          (adjacentEvenLowerLinks radius) := by
    unfold slabLinkMultiplicityProductOn
    apply natListProduct_congr
    intro link hlink
    unfold slabExplicitLinkMultiplicity
    have hspins :
        (slabIncidentPlaqIds
            (adjacentEvenExtent radius) link).map
            (assembleAdjacentEvenReflectedSlabLabelling
              radius left boundary right) =
          (slabIncidentPlaqIds
            (adjacentEvenExtent radius) link).map left := by
      apply List.map_congr_left
      intro id hid
      rw [assembleAdjacentEvenReflectedSlabLabelling_lower
        (slabIncidentPlaqId_physical hid)
        (adjacentEvenLowerLink_incident_face_lower hlink hid)]
    rw [hspins]
  unfold adjacentEvenLowerFactor
  rw [hface, hlinks]

/-- The fixed-link lower endpoint amplitude product of an assembly likewise
reads only the left half-state. -/
theorem adjacentEvenLowerAmplitudeProduct_assemble_only_left
    (K radius : Nat) (left boundary right : EdgeLabelling)
    (channel : Z4Link → Nat) :
    adjacentEvenLowerAmplitudeProduct K radius
        (assembleAdjacentEvenReflectedSlabLabelling
          radius left boundary right) channel =
      adjacentEvenLowerAmplitudeProduct K radius left channel := by
  unfold adjacentEvenLowerAmplitudeProduct
    adjacentEvenLowerLinkAmplitude
  apply listQProduct_congr
  intro link _
  rw [adjacentEvenAssembledLowerSpins_eq_left]

/-! ## 3. Reflection identifies the complete upper and lower factors -/

theorem adjacentEvenUpperFaceIds_reflection_perm (radius : Nat) :
    ((adjacentEvenUpperFaceIds radius).map
        (slabFaceReflectId (adjacentEvenExtent radius))).Perm
      (adjacentEvenLowerFaceIds radius) := by
  let faces := slabPhysicalFaceEdges (adjacentEvenExtent radius)
  let reflectId := slabFaceReflectId (adjacentEvenExtent radius)
  let side : Nat → CrossPlaneSide := fun id =>
    adjacentEvenPlaquetteSide radius
      (slabPlaquetteAt (adjacentEvenExtent radius) id)
  let lowerPredicate : Nat → Bool := fun id =>
    decide (side id = .lower)
  let upperPredicate : Nat → Bool := fun id =>
    decide (side id = .upper)
  have hfiltered :=
    (slabFaceReflectId_range_perm
      (adjacentEvenExtent radius)).filter lowerPredicate
  rw [List.filter_map] at hfiltered
  have hsource :
      faces.filter (lowerPredicate ∘ reflectId) =
        faces.filter upperPredicate := by
    apply List.filter_congr
    intro id hid
    have hside := adjacentEvenSlabFaceReflectId_side
      (radius := radius) (id := id) hid
    cases horiginal : side id <;>
      simp [lowerPredicate, upperPredicate, side, reflectId,
        horiginal, flipSide] at hside ⊢ <;> simp_all
  rw [hsource] at hfiltered
  simpa [adjacentEvenUpperFaceIds, adjacentEvenLowerFaceIds,
    adjacentEvenSlabFaceIdParts, faces, reflectId, side,
    lowerPredicate, upperPredicate,
    partitionBySide_lower_eq_filter,
    partitionBySide_upper_eq_filter] using hfiltered

theorem adjacentEvenUpperLinks_reflection_perm (radius : Nat) :
    ((adjacentEvenUpperLinks radius).map
        (timeReflectLink (adjacentEvenExtent radius))).Perm
      (adjacentEvenLowerLinks radius) := by
  let links := boundaryCompleteSlabLinks (adjacentEvenExtent radius)
  let reflectLink := timeReflectLink (adjacentEvenExtent radius)
  let side : Z4Link → CrossPlaneSide := adjacentEvenLinkSide radius
  let lowerPredicate : Z4Link → Bool := fun link =>
    decide (side link = .lower)
  let upperPredicate : Z4Link → Bool := fun link =>
    decide (side link = .upper)
  have hfiltered :=
    (timeReflect_boundaryCompleteSlabLinks_perm
      (adjacentEvenExtent radius)).filter lowerPredicate
  rw [List.filter_map] at hfiltered
  have hsource :
      links.filter (lowerPredicate ∘ reflectLink) =
        links.filter upperPredicate := by
    apply List.filter_congr
    intro link hlink
    have hside := adjacentEvenSlabLink_reflection_side
      (radius := radius) (link := link) hlink
    cases horiginal : side link <;>
      simp [lowerPredicate, upperPredicate, side, reflectLink,
        horiginal, flipSide] at hside ⊢ <;> simp_all
  rw [hsource] at hfiltered
  simpa [adjacentEvenUpperLinks, adjacentEvenLowerLinks,
    adjacentEvenSlabLinkParts, links, reflectLink, side,
    lowerPredicate, upperPredicate,
    partitionBySide_lower_eq_filter,
    partitionBySide_upper_eq_filter] using hfiltered

private theorem slabFaceFactorOn_adjacentEven_upper_reflection
    (w : Q') (K radius : Nat) (physical : EdgeLabelling) :
    slabFaceFactorOn w K physical (adjacentEvenUpperFaceIds radius) ≈
      slabFaceFactorOn w K
        (reflectSlabFaceLabelling (adjacentEvenExtent radius) physical)
        (adjacentEvenLowerFaceIds radius) := by
  have hmapAux : ∀ ids : List Nat,
      (∀ id, id ∈ ids → id ∈ adjacentEvenUpperFaceIds radius) →
      slabFaceFactorOn w K physical ids =
        slabFaceFactorOn w K
          (reflectSlabFaceLabelling (adjacentEvenExtent radius) physical)
          (ids.map (slabFaceReflectId
            (adjacentEvenExtent radius))) := by
    intro ids
    induction ids with
    | nil => intro _; rfl
    | cons id rest ih =>
        intro hsubset
        have hidUpper : id ∈ adjacentEvenUpperFaceIds radius :=
          hsubset id List.mem_cons_self
        have hidPhysical := (mem_adjacentEvenUpperFaceIds.mp hidUpper).1
        change coeffAt (heatKernelPacket K w) (physical id) *
              slabFaceFactorOn w K physical rest =
          coeffAt (heatKernelPacket K w)
              (physical (slabFaceReflectId (adjacentEvenExtent radius)
                (slabFaceReflectId (adjacentEvenExtent radius) id))) *
            slabFaceFactorOn w K
              (reflectSlabFaceLabelling
                (adjacentEvenExtent radius) physical)
              (rest.map (slabFaceReflectId
                (adjacentEvenExtent radius)))
        rw [slabFaceReflectId_involutive hidPhysical,
          ih (fun item hitem => hsubset item
            (List.mem_cons_of_mem id hitem))]
  have hmap :
      slabFaceFactorOn w K physical
          (adjacentEvenUpperFaceIds radius) =
        slabFaceFactorOn w K
          (reflectSlabFaceLabelling (adjacentEvenExtent radius) physical)
          ((adjacentEvenUpperFaceIds radius).map
            (slabFaceReflectId (adjacentEvenExtent radius))) :=
    hmapAux _ (fun id hid => hid)
  rw [hmap]
  exact eliminateLinks_perm _
    (adjacentEvenUpperFaceIds_reflection_perm radius)

private theorem slabLinkMultiplicityProductOn_adjacentEven_upper_reflection
    {K radius : Nat} {physical : EdgeLabelling}
    (hbounded : SlabFaceLabellingBounded K
      (adjacentEvenExtent radius) physical) :
    slabLinkMultiplicityProductOn K (adjacentEvenExtent radius) physical
        (adjacentEvenUpperLinks radius) =
      slabLinkMultiplicityProductOn K (adjacentEvenExtent radius)
        (reflectSlabFaceLabelling (adjacentEvenExtent radius) physical)
        (adjacentEvenLowerLinks radius) := by
  have hmapAux : ∀ links : List Z4Link,
      (∀ link, link ∈ links → link ∈ adjacentEvenUpperLinks radius) →
      slabLinkMultiplicityProductOn K (adjacentEvenExtent radius)
          physical links =
        slabLinkMultiplicityProductOn K (adjacentEvenExtent radius)
          (reflectSlabFaceLabelling (adjacentEvenExtent radius) physical)
          (links.map (timeReflectLink
            (adjacentEvenExtent radius))) := by
    intro links
    induction links with
    | nil => intro _; rfl
    | cons link rest ih =>
        intro hsubset
        have hlinkUpper : link ∈ adjacentEvenUpperLinks radius :=
          hsubset link List.mem_cons_self
        have hlinkPhysical := (mem_adjacentEvenUpperLinks.mp hlinkUpper).1
        change slabExplicitLinkMultiplicity K (adjacentEvenExtent radius)
              physical link *
              slabLinkMultiplicityProductOn K (adjacentEvenExtent radius)
                physical rest =
          slabExplicitLinkMultiplicity K (adjacentEvenExtent radius)
              (reflectSlabFaceLabelling
                (adjacentEvenExtent radius) physical)
                (timeReflectLink (adjacentEvenExtent radius) link) *
            slabLinkMultiplicityProductOn K (adjacentEvenExtent radius)
              (reflectSlabFaceLabelling
                (adjacentEvenExtent radius) physical)
              (rest.map (timeReflectLink
                (adjacentEvenExtent radius)))
        rw [slabExplicitLinkMultiplicity_reflection
          hlinkPhysical hbounded,
          ih (fun item hitem => hsubset item
            (List.mem_cons_of_mem link hitem))]
  have hmap :
      slabLinkMultiplicityProductOn K (adjacentEvenExtent radius) physical
          (adjacentEvenUpperLinks radius) =
        slabLinkMultiplicityProductOn K (adjacentEvenExtent radius)
          (reflectSlabFaceLabelling (adjacentEvenExtent radius) physical)
          ((adjacentEvenUpperLinks radius).map
            (timeReflectLink (adjacentEvenExtent radius))) :=
    hmapAux _ (fun link hlink => hlink)
  rw [hmap]
  exact natListProduct_perm _
    (adjacentEvenUpperLinks_reflection_perm radius)

theorem adjacentEvenUpperFactor_reflection
    (w : Q') {K radius : Nat} {physical : EdgeLabelling}
    (hbounded : SlabFaceLabellingBounded K
      (adjacentEvenExtent radius) physical) :
    adjacentEvenUpperFactor w K radius physical ≈
      adjacentEvenLowerFactor w K radius
        (reflectSlabFaceLabelling
          (adjacentEvenExtent radius) physical) := by
  unfold adjacentEvenUpperFactor adjacentEvenLowerFactor
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (slabFaceFactorOn_adjacentEven_upper_reflection
        w K radius physical)) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_of_eq
      (congrArg Q'.ofNat
        (slabLinkMultiplicityProductOn_adjacentEven_upper_reflection
          hbounded)))

theorem adjacentEvenUpperFactor_assemble_only_right
    (w : Q') {K radius : Nat} {left boundary right : EdgeLabelling}
    (hleft : left ∈ boundedEdgeLabellings K
      (adjacentEvenLowerFaceIds radius))
    (hboundary : boundary ∈ boundedEdgeLabellings K
      (adjacentEvenFixedFaceIds radius))
    (hright : right ∈ boundedEdgeLabellings K
      (adjacentEvenLowerFaceIds radius)) :
    adjacentEvenUpperFactor w K radius
        (assembleAdjacentEvenReflectedSlabLabelling
          radius left boundary right) ≈
      adjacentEvenLowerFactor w K radius right := by
  let assembled := assembleAdjacentEvenReflectedSlabLabelling
    radius left boundary right
  have hbounded : SlabFaceLabellingBounded K
      (adjacentEvenExtent radius) assembled :=
    assembleAdjacentEvenReflectedSlabLabelling_bounded
      hleft hboundary hright
  refine Q'.eqv_trans _
    (adjacentEvenLowerFactor w K radius
      (reflectSlabFaceLabelling
        (adjacentEvenExtent radius) assembled)) _
    (adjacentEvenUpperFactor_reflection w hbounded) ?_
  have hsupportedAgree :
      adjacentEvenLowerFactor w K radius
          (reflectSlabFaceLabelling
            (adjacentEvenExtent radius) assembled) =
        adjacentEvenLowerFactor w K radius
          (reflectSupportedSlabFaceLabelling
            (adjacentEvenExtent radius) assembled) := by
    apply adjacentEvenLowerFactor_eq_of_eq_on_lower
    intro id hid _
    exact (reflectSupportedSlabFaceLabelling_eq_on_physical
      (adjacentEvenExtent radius) assembled hid).symm
  rw [hsupportedAgree,
    assembleAdjacentEvenReflectedSlabLabelling_reflection_swap]
  exact Q'.eqv_of_eq
    (adjacentEvenLowerFactor_assemble_only_left
      w K radius right boundary left)

#print axioms adjacentEven_lower_link_incident_face_lower
#print axioms adjacentEven_upper_link_incident_face_upper
#print axioms adjacentEvenLowerLink_incident_face_lower
#print axioms adjacentEvenUpperLink_incident_face_upper
#print axioms adjacentEvenLowerFactor_assemble_only_left
#print axioms adjacentEvenLowerAmplitudeProduct_assemble_only_left
#print axioms adjacentEvenUpperFaceIds_reflection_perm
#print axioms adjacentEvenUpperLinks_reflection_perm
#print axioms adjacentEvenUpperFactor_reflection
#print axioms adjacentEvenUpperFactor_assemble_only_right

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOuterFactorLocality
