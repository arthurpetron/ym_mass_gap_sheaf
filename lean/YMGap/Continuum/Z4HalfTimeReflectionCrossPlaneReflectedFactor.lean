/-
# Reflection identification of the two corrected-slab half factors

The previous files split one spin-foam summand and construct the full
labelling assembled from two lower-half states.  Here the global face and
actual-link reflection permutations are filtered by geometric side.  This
proves that the literal upper factor is the same rational amplitude as the
lower factor of the reflected labelling.  No positivity argument is used.
-/

import YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings

namespace YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneReflectedFactor

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPartition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Stable partitions are literal Boolean filters -/

theorem partitionBySide_lower_eq_filter {A : Type}
    (side : A -> CrossPlaneSide) : forall xs : List A,
    (partitionBySide side xs).1 =
      xs.filter (fun x => decide (side x = .lower))
  | [] => rfl
  | head :: tail => by
      cases hside : side head <;>
        simp [partitionBySide, hside,
          partitionBySide_lower_eq_filter side tail]

theorem partitionBySide_upper_eq_filter {A : Type}
    (side : A -> CrossPlaneSide) : forall xs : List A,
    (partitionBySide side xs).2.2 =
      xs.filter (fun x => decide (side x = .upper))
  | [] => rfl
  | head :: tail => by
      cases hside : side head <;>
        simp [partitionBySide, hside,
          partitionBySide_upper_eq_filter side tail]

/-! ## 2. Reflection permutations restricted to the two open halves -/

theorem centralUpperFaceIds_reflection_perm (half : Nat) :
    ((centralUpperFaceIds half).map
        (slabFaceReflectId (centralExtent half))).Perm
      (centralLowerFaceIds half) := by
  let faces := slabPhysicalFaceEdges (centralExtent half)
  let reflectId := slabFaceReflectId (centralExtent half)
  let side : Nat -> CrossPlaneSide := fun id =>
    plaquetteHalfSide half
      (slabPlaquetteAt (centralExtent half) id)
  let lowerPredicate : Nat -> Bool := fun id =>
    decide (side id = .lower)
  let upperPredicate : Nat -> Bool := fun id =>
    decide (side id = .upper)
  have hfiltered :=
    (slabFaceReflectId_range_perm (centralExtent half)).filter
      lowerPredicate
  rw [List.filter_map] at hfiltered
  have hsource :
      faces.filter (lowerPredicate ∘ reflectId) =
        faces.filter upperPredicate := by
    apply List.filter_congr
    intro id hid
    have hside := slabFaceReflectId_side (half := half) (id := id) hid
    cases horiginal : side id <;>
      simp [lowerPredicate, upperPredicate, side, reflectId,
        horiginal, flipSide] at hside ⊢ <;> simp_all
  rw [hsource] at hfiltered
  simpa [centralUpperFaceIds, centralLowerFaceIds,
    centralSlabFaceIdParts, faces, reflectId, side,
    lowerPredicate, upperPredicate,
    partitionBySide_lower_eq_filter,
    partitionBySide_upper_eq_filter] using hfiltered

theorem centralUpperLinks_reflection_perm (half : Nat) :
    ((centralUpperLinks half).map
        (timeReflectLink (centralExtent half))).Perm
      (centralLowerLinks half) := by
  let links := boundaryCompleteSlabLinks (centralExtent half)
  let reflectLink := timeReflectLink (centralExtent half)
  let side : Z4Link -> CrossPlaneSide := linkHalfSide half
  let lowerPredicate : Z4Link -> Bool := fun link =>
    decide (side link = .lower)
  let upperPredicate : Z4Link -> Bool := fun link =>
    decide (side link = .upper)
  have hfiltered :=
    (timeReflect_boundaryCompleteSlabLinks_perm
      (centralExtent half)).filter lowerPredicate
  rw [List.filter_map] at hfiltered
  have hsource :
      links.filter (lowerPredicate ∘ reflectLink) =
        links.filter upperPredicate := by
    apply List.filter_congr
    intro link hlink
    have hside := centralSlabLink_reflection_side
      (half := half) (link := link) hlink
    cases horiginal : side link <;>
      simp [lowerPredicate, upperPredicate, side, reflectLink,
        horiginal, flipSide] at hside ⊢ <;> simp_all
  rw [hsource] at hfiltered
  simpa [centralUpperLinks, centralLowerLinks,
    centralSlabLinkParts, links, reflectLink, side,
    lowerPredicate, upperPredicate,
    partitionBySide_lower_eq_filter,
    partitionBySide_upper_eq_filter] using hfiltered

/-! ## 3. Upper factor equals the reflected lower factor -/

private theorem slabFaceFactorOn_upper_reflection
    (w : Q') (K half : Nat) (physical : EdgeLabelling) :
    slabFaceFactorOn w K physical (centralUpperFaceIds half) ≈
      slabFaceFactorOn w K
        (reflectSlabFaceLabelling (centralExtent half) physical)
        (centralLowerFaceIds half) := by
  have hmapAux : forall ids : List Nat,
      (∀ id, id ∈ ids -> id ∈ centralUpperFaceIds half) ->
      slabFaceFactorOn w K physical ids =
        slabFaceFactorOn w K
          (reflectSlabFaceLabelling (centralExtent half) physical)
          (ids.map (slabFaceReflectId (centralExtent half))) := by
    intro ids
    induction ids with
    | nil => intro _; rfl
    | cons id rest ih =>
        intro hsubset
        have hidUpper : id ∈ centralUpperFaceIds half :=
          hsubset id List.mem_cons_self
        have hidPhysical := (mem_centralUpperFaceIds.mp hidUpper).1
        change coeffAt (heatKernelPacket K w) (physical id) *
              slabFaceFactorOn w K physical rest =
          coeffAt (heatKernelPacket K w)
              (physical (slabFaceReflectId (centralExtent half)
                (slabFaceReflectId (centralExtent half) id))) *
            slabFaceFactorOn w K
              (reflectSlabFaceLabelling (centralExtent half) physical)
              (rest.map (slabFaceReflectId (centralExtent half)))
        rw [slabFaceReflectId_involutive hidPhysical,
          ih (fun item hitem => hsubset item
            (List.mem_cons_of_mem id hitem))]
  have hmap :
      slabFaceFactorOn w K physical (centralUpperFaceIds half) =
        slabFaceFactorOn w K
          (reflectSlabFaceLabelling (centralExtent half) physical)
          ((centralUpperFaceIds half).map
            (slabFaceReflectId (centralExtent half))) :=
    hmapAux _ (fun id hid => hid)
  rw [hmap]
  exact eliminateLinks_perm _ (centralUpperFaceIds_reflection_perm half)

private theorem slabLinkMultiplicityProductOn_upper_reflection
    {K half : Nat} {physical : EdgeLabelling}
    (hbounded : SlabFaceLabellingBounded K
      (centralExtent half) physical) :
    slabLinkMultiplicityProductOn K (centralExtent half) physical
        (centralUpperLinks half) =
      slabLinkMultiplicityProductOn K (centralExtent half)
        (reflectSlabFaceLabelling (centralExtent half) physical)
        (centralLowerLinks half) := by
  have hmapAux : forall links : List Z4Link,
      (∀ link, link ∈ links -> link ∈ centralUpperLinks half) ->
      slabLinkMultiplicityProductOn K (centralExtent half) physical links =
        slabLinkMultiplicityProductOn K (centralExtent half)
          (reflectSlabFaceLabelling (centralExtent half) physical)
          (links.map (timeReflectLink (centralExtent half))) := by
    intro links
    induction links with
    | nil => intro _; rfl
    | cons link rest ih =>
        intro hsubset
        have hlinkUpper : link ∈ centralUpperLinks half :=
          hsubset link List.mem_cons_self
        have hlinkPhysical := (mem_centralUpperLinks.mp hlinkUpper).1
        change slabExplicitLinkMultiplicity K (centralExtent half)
              physical link *
              slabLinkMultiplicityProductOn K (centralExtent half)
                physical rest =
          slabExplicitLinkMultiplicity K (centralExtent half)
              (reflectSlabFaceLabelling (centralExtent half) physical)
                (timeReflectLink (centralExtent half) link) *
            slabLinkMultiplicityProductOn K (centralExtent half)
              (reflectSlabFaceLabelling (centralExtent half) physical)
              (rest.map (timeReflectLink (centralExtent half)))
        rw [slabExplicitLinkMultiplicity_reflection
          hlinkPhysical hbounded,
          ih (fun item hitem => hsubset item
            (List.mem_cons_of_mem link hitem))]
  have hmap :
      slabLinkMultiplicityProductOn K (centralExtent half) physical
          (centralUpperLinks half) =
        slabLinkMultiplicityProductOn K (centralExtent half)
          (reflectSlabFaceLabelling (centralExtent half) physical)
          ((centralUpperLinks half).map
            (timeReflectLink (centralExtent half))) :=
    hmapAux _ (fun link hlink => hlink)
  rw [hmap]
  exact natListProduct_perm _ (centralUpperLinks_reflection_perm half)

theorem centralUpperFactor_reflection
    (w : Q') {K half : Nat} {physical : EdgeLabelling}
    (hbounded : SlabFaceLabellingBounded K
      (centralExtent half) physical) :
    centralUpperFactor w K half physical ≈
      centralLowerFactor w K half
        (reflectSlabFaceLabelling (centralExtent half) physical) := by
  unfold centralUpperFactor centralLowerFactor
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (slabFaceFactorOn_upper_reflection w K half physical)) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_of_eq
      (congrArg Q'.ofNat
        (slabLinkMultiplicityProductOn_upper_reflection hbounded)))

theorem centralUpperFactor_assembled_eq_lowerAmplitude
    (w : Q') {K half : Nat} {left boundary right : EdgeLabelling}
    (hleft : left ∈ boundedEdgeLabellings K (centralLowerFaceIds half))
    (hboundary : boundary ∈
      boundedEdgeLabellings K (centralFixedFaceIds half))
    (hright : right ∈ boundedEdgeLabellings K (centralLowerFaceIds half)) :
    centralUpperFactor w K half
        (assembleReflectedSlabLabelling half left boundary right) ≈
      centralLowerFactor w K half
        (assembleReflectedSlabLabelling half right boundary zeroEdgeLabelling) := by
  let assembled := assembleReflectedSlabLabelling half left boundary right
  have hbounded : SlabFaceLabellingBounded K (centralExtent half) assembled :=
    assembleReflectedSlabLabelling_bounded hleft hboundary hright
  refine Q'.eqv_trans _
    (centralLowerFactor w K half
      (reflectSlabFaceLabelling (centralExtent half) assembled)) _
    (centralUpperFactor_reflection w hbounded) ?_
  have hsupportedAgree :
      centralLowerFactor w K half
          (reflectSlabFaceLabelling (centralExtent half) assembled) =
        centralLowerFactor w K half
          (reflectSupportedSlabFaceLabelling
            (centralExtent half) assembled) := by
    apply centralLowerFactor_eq_of_eq_on_not_upper
    intro id hid _
    exact (reflectSupportedSlabFaceLabelling_eq_on_physical
      (centralExtent half) assembled hid).symm
  rw [hsupportedAgree,
    assembleReflectedSlabLabelling_reflection_swap]
  exact Q'.eqv_of_eq
    (centralLowerFactor_assemble_independent_right
      w K half right boundary left)

end YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneReflectedFactor

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneReflectedFactor.partitionBySide_lower_eq_filter
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneReflectedFactor.partitionBySide_upper_eq_filter
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneReflectedFactor.centralUpperFaceIds_reflection_perm
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneReflectedFactor.centralUpperLinks_reflection_perm
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneReflectedFactor.centralUpperFactor_reflection
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneReflectedFactor.centralUpperFactor_assembled_eq_lowerAmplitude
