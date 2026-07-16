/-
# Finite half-state and interface labellings for corrected-slab reflection

This file constructs the literal full face labelling determined by a lower
half-state, a fixed cross-plane channel, and a second lower half-state read on
the reflected upper half.  It proves boundedness/support, the reflection swap
law, and extensionality of each lower/fixed/upper summand factor on exactly the
coordinates allowed by cross-plane incidence locality.
-/

import YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

namespace YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPartition

/-! ## 1. Factor extensionality on geometric coordinate sets -/

private theorem slabFaceFactorOn_congr
    (w : Q') (K : Nat) (left right : EdgeLabelling) : forall ids : List Nat,
    (∀ id, id ∈ ids -> left id = right id) ->
    slabFaceFactorOn w K left ids = slabFaceFactorOn w K right ids
  | [], _ => rfl
  | head :: tail, hagree => by
      change
        YMGap.Continuum.SU2CharacterVacuumHaar.coeffAt
            (YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState.heatKernelPacket K w)
            (left head) * slabFaceFactorOn w K left tail =
          YMGap.Continuum.SU2CharacterVacuumHaar.coeffAt
            (YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState.heatKernelPacket K w)
            (right head) * slabFaceFactorOn w K right tail
      rw [hagree head List.mem_cons_self,
        slabFaceFactorOn_congr w K left right tail
          (fun id hid => hagree id (List.mem_cons_of_mem head hid))]

private theorem listMap_congr_on {A B : Type}
    (left right : A -> B) : forall xs : List A,
    (∀ x, x ∈ xs -> left x = right x) ->
    xs.map left = xs.map right
  | [], _ => rfl
  | head :: tail, hagree => by
      simp only [List.map_cons]
      rw [hagree head List.mem_cons_self,
        listMap_congr_on left right tail
          (fun x hx => hagree x (List.mem_cons_of_mem head hx))]

private theorem slabExplicitLinkMultiplicity_congr_incident
    (K extent : Nat) (left right : EdgeLabelling) (link : Z4Link)
    (hagree : ∀ id, id ∈ slabIncidentPlaqIds extent link ->
      left id = right id) :
    slabExplicitLinkMultiplicity K extent left link =
      slabExplicitLinkMultiplicity K extent right link := by
  unfold slabExplicitLinkMultiplicity
  rw [listMap_congr_on left right (slabIncidentPlaqIds extent link) hagree]

private theorem slabLinkMultiplicityProductOn_congr
    (K extent : Nat) (left right : EdgeLabelling) :
    forall links : List Z4Link,
    (∀ link, link ∈ links ->
      ∀ id, id ∈ slabIncidentPlaqIds extent link ->
        left id = right id) ->
    slabLinkMultiplicityProductOn K extent left links =
      slabLinkMultiplicityProductOn K extent right links
  | [], _ => rfl
  | head :: tail, hagree => by
      change
        slabExplicitLinkMultiplicity K extent left head *
            slabLinkMultiplicityProductOn K extent left tail =
          slabExplicitLinkMultiplicity K extent right head *
            slabLinkMultiplicityProductOn K extent right tail
      rw [slabExplicitLinkMultiplicity_congr_incident K extent left right head
          (hagree head List.mem_cons_self),
        slabLinkMultiplicityProductOn_congr K extent left right tail
          (fun link hlink => hagree link
            (List.mem_cons_of_mem head hlink))]

theorem centralLowerFactor_eq_of_eq_on_not_upper
    (w : Q') (K half : Nat) (left right : EdgeLabelling)
    (hagree : ∀ id,
      id ∈ slabPhysicalFaceEdges (centralExtent half) ->
      plaquetteHalfSide half
          (slabPlaquetteAt (centralExtent half) id) ≠ .upper ->
      left id = right id) :
    centralLowerFactor w K half left =
      centralLowerFactor w K half right := by
  have hface :
      slabFaceFactorOn w K left (centralLowerFaceIds half) =
        slabFaceFactorOn w K right (centralLowerFaceIds half) := by
    apply slabFaceFactorOn_congr
    intro id hid
    have hparts := mem_centralLowerFaceIds.mp hid
    exact hagree id hparts.1 (by rw [hparts.2]; decide)
  have hlink :
      slabLinkMultiplicityProductOn K (centralExtent half) left
          (centralLowerLinks half) =
        slabLinkMultiplicityProductOn K (centralExtent half) right
          (centralLowerLinks half) := by
    apply slabLinkMultiplicityProductOn_congr
    intro link hlink id hid
    exact hagree id (slabIncidentPlaqId_physical hid)
      (incident_of_lower_link_ne_upper hlink hid)
  unfold centralLowerFactor
  rw [hface, hlink]

theorem centralFixedWeight_eq_of_eq_on_fixed
    (w : Q') (K half : Nat) (left right : EdgeLabelling)
    (hagree : ∀ id,
      id ∈ slabPhysicalFaceEdges (centralExtent half) ->
      plaquetteHalfSide half
          (slabPlaquetteAt (centralExtent half) id) = .fixed ->
      left id = right id) :
    centralFixedWeight w K half left =
      centralFixedWeight w K half right := by
  have hface :
      slabFaceFactorOn w K left (centralFixedFaceIds half) =
        slabFaceFactorOn w K right (centralFixedFaceIds half) := by
    apply slabFaceFactorOn_congr
    intro id hid
    have hparts := mem_centralFixedFaceIds.mp hid
    exact hagree id hparts.1 hparts.2
  have hlink :
      slabLinkMultiplicityProductOn K (centralExtent half) left
          (centralFixedLinks half) =
        slabLinkMultiplicityProductOn K (centralExtent half) right
          (centralFixedLinks half) := by
    apply slabLinkMultiplicityProductOn_congr
    intro link hlink id hid
    exact hagree id (slabIncidentPlaqId_physical hid)
      (incident_of_fixed_link_fixed hlink hid)
  unfold centralFixedWeight
  rw [hface, hlink]

theorem centralUpperFactor_eq_of_eq_on_not_lower
    (w : Q') (K half : Nat) (left right : EdgeLabelling)
    (hagree : ∀ id,
      id ∈ slabPhysicalFaceEdges (centralExtent half) ->
      plaquetteHalfSide half
          (slabPlaquetteAt (centralExtent half) id) ≠ .lower ->
      left id = right id) :
    centralUpperFactor w K half left =
      centralUpperFactor w K half right := by
  have hface :
      slabFaceFactorOn w K left (centralUpperFaceIds half) =
        slabFaceFactorOn w K right (centralUpperFaceIds half) := by
    apply slabFaceFactorOn_congr
    intro id hid
    have hparts := mem_centralUpperFaceIds.mp hid
    exact hagree id hparts.1 (by rw [hparts.2]; decide)
  have hlink :
      slabLinkMultiplicityProductOn K (centralExtent half) left
          (centralUpperLinks half) =
        slabLinkMultiplicityProductOn K (centralExtent half) right
          (centralUpperLinks half) := by
    apply slabLinkMultiplicityProductOn_congr
    intro link hlink id hid
    exact hagree id (slabIncidentPlaqId_physical hid)
      (incident_of_upper_link_ne_lower hlink hid)
  unfold centralUpperFactor
  rw [hface, hlink]

/-! ## 2. Full labelling assembled from two half-states and an interface -/

/-- Assemble `left`, fixed `boundary`, and the reflection of `right` on the
upper half.  The explicit physical-range guard keeps the result zero on every
unused numerical coordinate. -/
def assembleReflectedSlabLabelling
    (half : Nat) (left boundary right : EdgeLabelling) : EdgeLabelling :=
  fun id =>
    if id ∈ slabPhysicalFaceEdges (centralExtent half) then
      match plaquetteHalfSide half
          (slabPlaquetteAt (centralExtent half) id) with
      | .lower => left id
      | .fixed => boundary id
      | .upper => right (slabFaceReflectId (centralExtent half) id)
    else 0

theorem assembleReflectedSlabLabelling_lower
    {half id : Nat} {left boundary right : EdgeLabelling}
    (hid : id ∈ slabPhysicalFaceEdges (centralExtent half))
    (hside : plaquetteHalfSide half
      (slabPlaquetteAt (centralExtent half) id) = .lower) :
    assembleReflectedSlabLabelling half left boundary right id = left id := by
  simp [assembleReflectedSlabLabelling, hid, hside]

theorem assembleReflectedSlabLabelling_fixed
    {half id : Nat} {left boundary right : EdgeLabelling}
    (hid : id ∈ slabPhysicalFaceEdges (centralExtent half))
    (hside : plaquetteHalfSide half
      (slabPlaquetteAt (centralExtent half) id) = .fixed) :
    assembleReflectedSlabLabelling half left boundary right id = boundary id := by
  simp [assembleReflectedSlabLabelling, hid, hside]

theorem assembleReflectedSlabLabelling_upper
    {half id : Nat} {left boundary right : EdgeLabelling}
    (hid : id ∈ slabPhysicalFaceEdges (centralExtent half))
    (hside : plaquetteHalfSide half
      (slabPlaquetteAt (centralExtent half) id) = .upper) :
    assembleReflectedSlabLabelling half left boundary right id =
      right (slabFaceReflectId (centralExtent half) id) := by
  simp [assembleReflectedSlabLabelling, hid, hside]

theorem assembleReflectedSlabLabelling_zero_off_physical
    (half : Nat) (left boundary right : EdgeLabelling)
    {id : Nat}
    (hid : id ∉ slabPhysicalFaceEdges (centralExtent half)) :
    assembleReflectedSlabLabelling half left boundary right id = 0 := by
  simp [assembleReflectedSlabLabelling, hid]

theorem assembleReflectedSlabLabelling_bounded
    {K half : Nat} {left boundary right : EdgeLabelling}
    (hleft : left ∈ boundedEdgeLabellings K (centralLowerFaceIds half))
    (hboundary : boundary ∈
      boundedEdgeLabellings K (centralFixedFaceIds half))
    (hright : right ∈ boundedEdgeLabellings K (centralLowerFaceIds half)) :
    SlabFaceLabellingBounded K (centralExtent half)
      (assembleReflectedSlabLabelling half left boundary right) := by
  have hleftSound := boundedEdgeLabellings_sound K
    (centralLowerFaceIds half) left hleft
  have hboundarySound := boundedEdgeLabellings_sound K
    (centralFixedFaceIds half) boundary hboundary
  have hrightSound := boundedEdgeLabellings_sound K
    (centralLowerFaceIds half) right hright
  intro id hid
  cases hside : plaquetteHalfSide half
      (slabPlaquetteAt (centralExtent half) id)
  · rw [assembleReflectedSlabLabelling_lower hid hside]
    exact Nat.le_of_lt_succ
      (hleftSound.1 id (mem_centralLowerFaceIds.mpr ⟨hid, hside⟩))
  · rw [assembleReflectedSlabLabelling_fixed hid hside]
    exact Nat.le_of_lt_succ
      (hboundarySound.1 id (mem_centralFixedFaceIds.mpr ⟨hid, hside⟩))
  · rw [assembleReflectedSlabLabelling_upper hid hside]
    have hreflectedPhysical := slabFaceReflectId_physical hid
    have hreflectedSide := slabFaceReflectId_side hid
    rw [hside] at hreflectedSide
    exact Nat.le_of_lt_succ
      (hrightSound.1 _
        (mem_centralLowerFaceIds.mpr
          ⟨hreflectedPhysical, by simpa [flipSide] using hreflectedSide⟩))

theorem assembleReflectedSlabLabelling_mem_full
    {K half : Nat} {left boundary right : EdgeLabelling}
    (hleft : left ∈ boundedEdgeLabellings K (centralLowerFaceIds half))
    (hboundary : boundary ∈
      boundedEdgeLabellings K (centralFixedFaceIds half))
    (hright : right ∈ boundedEdgeLabellings K (centralLowerFaceIds half)) :
    assembleReflectedSlabLabelling half left boundary right ∈
      boundedEdgeLabellings K
        (slabPhysicalFaceEdges (centralExtent half)) := by
  apply boundedEdgeLabellings_complete
  · intro id hid
    exact Nat.lt_succ_of_le
      (assembleReflectedSlabLabelling_bounded hleft hboundary hright id hid)
  · intro id hid
    exact assembleReflectedSlabLabelling_zero_off_physical
      half left boundary right hid

/-! ## 3. Fixed coordinates and reflection swap -/

theorem timeReflectPlaquette_eq_self_of_fixed_side
    {half : Nat} {plaquette : Z4Plaq}
    (hside : plaquetteHalfSide half plaquette = .fixed) :
    timeReflectPlaquette (centralExtent half) plaquette = plaquette := by
  obtain ⟨⟨a, b, c, time⟩, plane⟩ := plaquette
  cases plane
  all_goals simp only [plaquetteHalfSide] at hside
  all_goals simp only [timeReflectPlaquette, centralExtent]
  all_goals
    simp only [spatialHalfSide, temporalHalfSide] at hside
    repeat' split at hside
    all_goals simp_all
    all_goals omega

theorem slabFaceReflectId_eq_self_of_fixed_side
    {half id : Nat}
    (hid : id ∈ slabPhysicalFaceEdges (centralExtent half))
    (hside : plaquetteHalfSide half
      (slabPlaquetteAt (centralExtent half) id) = .fixed) :
    slabFaceReflectId (centralExtent half) id = id := by
  apply slabPlaquetteAt_injective_on_physical
    (slabFaceReflectId_physical hid) hid
  rw [slabPlaquetteAt_slabFaceReflectId hid,
    timeReflectPlaquette_eq_self_of_fixed_side hside]

theorem assembleReflectedSlabLabelling_reflection_swap
    (half : Nat) (left boundary right : EdgeLabelling) :
    reflectSupportedSlabFaceLabelling (centralExtent half)
        (assembleReflectedSlabLabelling half left boundary right) =
      assembleReflectedSlabLabelling half right boundary left := by
  funext id
  by_cases hid : id ∈ slabPhysicalFaceEdges (centralExtent half)
  · have hreflectedPhysical := slabFaceReflectId_physical hid
    have hreflectedSide := slabFaceReflectId_side hid
    cases hside : plaquetteHalfSide half
        (slabPlaquetteAt (centralExtent half) id)
    · rw [hside] at hreflectedSide
      rw [reflectSupportedSlabFaceLabelling_eq_on_physical _ _ hid]
      change assembleReflectedSlabLabelling half left boundary right
          (slabFaceReflectId (centralExtent half) id) =
        assembleReflectedSlabLabelling half right boundary left id
      rw [assembleReflectedSlabLabelling_upper hreflectedPhysical
          (by simpa [flipSide] using hreflectedSide),
        assembleReflectedSlabLabelling_lower hid hside,
        slabFaceReflectId_involutive hid]
    · rw [hside] at hreflectedSide
      rw [reflectSupportedSlabFaceLabelling_eq_on_physical _ _ hid]
      change assembleReflectedSlabLabelling half left boundary right
          (slabFaceReflectId (centralExtent half) id) =
        assembleReflectedSlabLabelling half right boundary left id
      rw [assembleReflectedSlabLabelling_fixed hreflectedPhysical
          (by simpa [flipSide] using hreflectedSide),
        assembleReflectedSlabLabelling_fixed hid hside,
        slabFaceReflectId_eq_self_of_fixed_side hid hside]
    · rw [hside] at hreflectedSide
      rw [reflectSupportedSlabFaceLabelling_eq_on_physical _ _ hid]
      change assembleReflectedSlabLabelling half left boundary right
          (slabFaceReflectId (centralExtent half) id) =
        assembleReflectedSlabLabelling half right boundary left id
      rw [assembleReflectedSlabLabelling_lower hreflectedPhysical
          (by simpa [flipSide] using hreflectedSide),
        assembleReflectedSlabLabelling_upper hid hside]
  · rw [reflectSupportedSlabFaceLabelling_zero_off_physical _ _ hid,
      assembleReflectedSlabLabelling_zero_off_physical
        half right boundary left hid]

/-! ## 4. The factors of an assembled state read only their own inputs -/

theorem centralLowerFactor_assemble_independent_right
    (w : Q') (K half : Nat) (left boundary right : EdgeLabelling) :
    centralLowerFactor w K half
        (assembleReflectedSlabLabelling half left boundary right) =
      centralLowerFactor w K half
        (assembleReflectedSlabLabelling half left boundary zeroEdgeLabelling) := by
  apply centralLowerFactor_eq_of_eq_on_not_upper
  intro id hid hnotUpper
  cases hside : plaquetteHalfSide half
      (slabPlaquetteAt (centralExtent half) id)
  · rw [assembleReflectedSlabLabelling_lower hid hside,
      assembleReflectedSlabLabelling_lower hid hside]
  · rw [assembleReflectedSlabLabelling_fixed hid hside,
      assembleReflectedSlabLabelling_fixed hid hside]
  · exact False.elim (hnotUpper hside)

theorem centralFixedWeight_assemble_only_boundary
    (w : Q') (K half : Nat) (left boundary right : EdgeLabelling) :
    centralFixedWeight w K half
        (assembleReflectedSlabLabelling half left boundary right) =
      centralFixedWeight w K half
        (assembleReflectedSlabLabelling half zeroEdgeLabelling boundary
          zeroEdgeLabelling) := by
  apply centralFixedWeight_eq_of_eq_on_fixed
  intro id hid hfixed
  rw [assembleReflectedSlabLabelling_fixed hid hfixed,
    assembleReflectedSlabLabelling_fixed hid hfixed]

theorem centralUpperFactor_assemble_independent_left
    (w : Q') (K half : Nat) (left boundary right : EdgeLabelling) :
    centralUpperFactor w K half
        (assembleReflectedSlabLabelling half left boundary right) =
      centralUpperFactor w K half
        (assembleReflectedSlabLabelling half zeroEdgeLabelling boundary right) := by
  apply centralUpperFactor_eq_of_eq_on_not_lower
  intro id hid hnotLower
  cases hside : plaquetteHalfSide half
      (slabPlaquetteAt (centralExtent half) id)
  · exact False.elim (hnotLower hside)
  · rw [assembleReflectedSlabLabelling_fixed hid hside,
      assembleReflectedSlabLabelling_fixed hid hside]
  · rw [assembleReflectedSlabLabelling_upper hid hside,
      assembleReflectedSlabLabelling_upper hid hside]

end YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings.centralLowerFactor_eq_of_eq_on_not_upper
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings.centralFixedWeight_eq_of_eq_on_fixed
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings.centralUpperFactor_eq_of_eq_on_not_lower
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings.assembleReflectedSlabLabelling_bounded
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings.assembleReflectedSlabLabelling_mem_full
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings.slabFaceReflectId_eq_self_of_fixed_side
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings.assembleReflectedSlabLabelling_reflection_swap
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings.centralLowerFactor_assemble_independent_right
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings.centralFixedWeight_assemble_only_boundary
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings.centralUpperFactor_assemble_independent_left
