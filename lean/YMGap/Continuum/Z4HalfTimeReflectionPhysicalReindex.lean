/-
# Cartesian coverage of the finite reflected slab Gram

The finite Gram theorem is physically meaningful only after proving that its
assembled lower/right/interface labellings enumerate the pre-existing full
corrected-slab Cartesian state space exactly once.  This file supplies that
missing coverage theorem.

For every supported full slab labelling we construct its lower restriction,
its fixed-plane restriction, and the lower labelling obtained by reflecting
its upper restriction.  Assembly and restriction are proved inverse in both
directions.  The resulting mapped Cartesian triple list is then proved a
literal permutation of `boundedEdgeLabellings` on all physical slab faces.
Finally the independently defined full reflection numerator is identified
with the assembled Gram quadratic and hence is nonnegative.
-/

import YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

namespace YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4BoundedEdgeLabellingNodup
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The three restrictions of a full supported labelling -/

/-- Restriction of a full labelling to the lower face identifiers, extended
by zero away from that finite support. -/
def centralLowerRestriction (half : Nat)
    (physical : EdgeLabelling) : EdgeLabelling :=
  fun id => if id ∈ centralLowerFaceIds half then physical id else 0

/-- Restriction of a full labelling to the fixed cross-plane face identifiers,
extended by zero away from that finite support. -/
def centralBoundaryRestriction (half : Nat)
    (physical : EdgeLabelling) : EdgeLabelling :=
  fun id => if id ∈ centralFixedFaceIds half then physical id else 0

/-- Read the upper half through reflection as a lower-half labelling, extended
by zero away from the lower face identifiers. -/
def centralReflectedUpperRestriction (half : Nat)
    (physical : EdgeLabelling) : EdgeLabelling :=
  fun id => if id ∈ centralLowerFaceIds half then
    physical (slabFaceReflectId (centralExtent half) id)
  else 0

theorem centralLowerRestriction_mem
    {K half : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (slabPhysicalFaceEdges (centralExtent half))) :
    centralLowerRestriction half physical ∈
      boundedEdgeLabellings K (centralLowerFaceIds half) := by
  have hsound := boundedEdgeLabellings_sound K
    (slabPhysicalFaceEdges (centralExtent half)) physical hphysical
  apply boundedEdgeLabellings_complete
  · intro id hid
    simp only [centralLowerRestriction, if_pos hid]
    exact hsound.1 id (mem_centralLowerFaceIds.mp hid).1
  · intro id hid
    simp [centralLowerRestriction, hid]

theorem centralBoundaryRestriction_mem
    {K half : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (slabPhysicalFaceEdges (centralExtent half))) :
    centralBoundaryRestriction half physical ∈
      boundedEdgeLabellings K (centralFixedFaceIds half) := by
  have hsound := boundedEdgeLabellings_sound K
    (slabPhysicalFaceEdges (centralExtent half)) physical hphysical
  apply boundedEdgeLabellings_complete
  · intro id hid
    simp only [centralBoundaryRestriction, if_pos hid]
    exact hsound.1 id (mem_centralFixedFaceIds.mp hid).1
  · intro id hid
    simp [centralBoundaryRestriction, hid]

theorem centralReflectedUpperRestriction_mem
    {K half : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (slabPhysicalFaceEdges (centralExtent half))) :
    centralReflectedUpperRestriction half physical ∈
      boundedEdgeLabellings K (centralLowerFaceIds half) := by
  have hsound := boundedEdgeLabellings_sound K
    (slabPhysicalFaceEdges (centralExtent half)) physical hphysical
  apply boundedEdgeLabellings_complete
  · intro id hid
    simp only [centralReflectedUpperRestriction, if_pos hid]
    exact hsound.1 _
      (slabFaceReflectId_physical (mem_centralLowerFaceIds.mp hid).1)
  · intro id hid
    simp [centralReflectedUpperRestriction, hid]

/-! ## 2. Restricting after assembly recovers every bounded input -/

theorem centralLowerRestriction_assemble
    {K half : Nat} {left boundary right : EdgeLabelling}
    (hleft : left ∈ boundedEdgeLabellings K (centralLowerFaceIds half)) :
    centralLowerRestriction half
      (assembleReflectedSlabLabelling half left boundary right) = left := by
  have hsound := boundedEdgeLabellings_sound K
    (centralLowerFaceIds half) left hleft
  funext id
  by_cases hid : id ∈ centralLowerFaceIds half
  · have hparts := mem_centralLowerFaceIds.mp hid
    simp only [centralLowerRestriction, if_pos hid]
    exact assembleReflectedSlabLabelling_lower hparts.1 hparts.2
  · rw [hsound.2 id hid]
    simp [centralLowerRestriction, hid]

theorem centralBoundaryRestriction_assemble
    {K half : Nat} {left boundary right : EdgeLabelling}
    (hboundary : boundary ∈
      boundedEdgeLabellings K (centralFixedFaceIds half)) :
    centralBoundaryRestriction half
      (assembleReflectedSlabLabelling half left boundary right) = boundary := by
  have hsound := boundedEdgeLabellings_sound K
    (centralFixedFaceIds half) boundary hboundary
  funext id
  by_cases hid : id ∈ centralFixedFaceIds half
  · have hparts := mem_centralFixedFaceIds.mp hid
    simp only [centralBoundaryRestriction, if_pos hid]
    exact assembleReflectedSlabLabelling_fixed hparts.1 hparts.2
  · rw [hsound.2 id hid]
    simp [centralBoundaryRestriction, hid]

theorem centralReflectedUpperRestriction_assemble
    {K half : Nat} {left boundary right : EdgeLabelling}
    (hright : right ∈ boundedEdgeLabellings K (centralLowerFaceIds half)) :
    centralReflectedUpperRestriction half
      (assembleReflectedSlabLabelling half left boundary right) = right := by
  have hsound := boundedEdgeLabellings_sound K
    (centralLowerFaceIds half) right hright
  funext id
  by_cases hid : id ∈ centralLowerFaceIds half
  · have hparts := mem_centralLowerFaceIds.mp hid
    have hreflectedPhysical := slabFaceReflectId_physical hparts.1
    have hreflectedSide := slabFaceReflectId_side hparts.1
    rw [hparts.2] at hreflectedSide
    simp only [centralReflectedUpperRestriction, if_pos hid]
    rw [assembleReflectedSlabLabelling_upper hreflectedPhysical
        (by simpa [flipSide] using hreflectedSide),
      slabFaceReflectId_involutive hparts.1]
  · rw [hsound.2 id hid]
    simp [centralReflectedUpperRestriction, hid]

/-! ## 3. Assembling the three restrictions recovers every full labelling -/

theorem assembleReflectedSlabLabelling_restrictions
    {K half : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (slabPhysicalFaceEdges (centralExtent half))) :
    assembleReflectedSlabLabelling half
        (centralLowerRestriction half physical)
        (centralBoundaryRestriction half physical)
        (centralReflectedUpperRestriction half physical) = physical := by
  have hsound := boundedEdgeLabellings_sound K
    (slabPhysicalFaceEdges (centralExtent half)) physical hphysical
  funext id
  by_cases hid : id ∈ slabPhysicalFaceEdges (centralExtent half)
  · cases hside : plaquetteHalfSide half
        (slabPlaquetteAt (centralExtent half) id)
    · rw [assembleReflectedSlabLabelling_lower hid hside]
      simp [centralLowerRestriction,
        mem_centralLowerFaceIds.mpr ⟨hid, hside⟩]
    · rw [assembleReflectedSlabLabelling_fixed hid hside]
      simp [centralBoundaryRestriction,
        mem_centralFixedFaceIds.mpr ⟨hid, hside⟩]
    · rw [assembleReflectedSlabLabelling_upper hid hside]
      have hreflectedPhysical := slabFaceReflectId_physical hid
      have hreflectedSide := slabFaceReflectId_side hid
      rw [hside] at hreflectedSide
      have hreflectedLower :
          slabFaceReflectId (centralExtent half) id ∈
            centralLowerFaceIds half :=
        mem_centralLowerFaceIds.mpr
          ⟨hreflectedPhysical, by simpa [flipSide] using hreflectedSide⟩
      simp only [centralReflectedUpperRestriction,
        if_pos hreflectedLower]
      rw [slabFaceReflectId_involutive hid]
  · rw [assembleReflectedSlabLabelling_zero_off_physical
        half _ _ _ hid,
      hsound.2 id hid]

/-! ## 4. The literal Cartesian triple list -/

/-- Convention: `triple.1` is the lower input, `triple.2.1` is the lower
input read from the upper half, and `triple.2.2` is the fixed-plane channel. -/
abbrev CentralReflectionTriple :=
  EdgeLabelling × (EdgeLabelling × EdgeLabelling)

def centralReflectionTriples (K half : Nat) :
    List CentralReflectionTriple :=
  (centralHalfStates K half).flatMap (fun left =>
    (centralHalfStates K half).flatMap (fun right =>
      (centralBoundaryChannels K half).map (fun boundary =>
        (left, (right, boundary)))))

def assembleCentralReflectionTriple (half : Nat)
    (triple : CentralReflectionTriple) : EdgeLabelling :=
  assembleReflectedSlabLabelling half
    triple.1 triple.2.2 triple.2.1

theorem mem_centralReflectionTriples
    {K half : Nat} {triple : CentralReflectionTriple} :
    triple ∈ centralReflectionTriples K half ↔
      triple.1 ∈ centralHalfStates K half ∧
      triple.2.1 ∈ centralHalfStates K half ∧
      triple.2.2 ∈ centralBoundaryChannels K half := by
  constructor
  · intro htriple
    unfold centralReflectionTriples at htriple
    obtain ⟨left, hleft, hrightBlock⟩ := List.mem_flatMap.mp htriple
    obtain ⟨right, hright, hboundaryMap⟩ :=
      List.mem_flatMap.mp hrightBlock
    obtain ⟨boundary, hboundary, heq⟩ := List.mem_map.mp hboundaryMap
    rw [← heq]
    exact ⟨hleft, hright, hboundary⟩
  · intro hparts
    unfold centralReflectionTriples
    apply List.mem_flatMap.mpr
    refine ⟨triple.1, hparts.1, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨triple.2.1, hparts.2.1, ?_⟩
    exact List.mem_map.mpr ⟨triple.2.2, hparts.2.2, rfl⟩

private theorem rangeNodupLocal (N : Nat) : (List.range N).Nodup := by
  induction N with
  | zero => exact List.nodup_nil
  | succ N ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr
          ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro x hx y hy hxy
      have hyN : y = N := List.mem_singleton.mp hy
      rw [hxy, hyN] at hx
      exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl N)

private theorem centralFaceIdParts_nodup (half : Nat) :
    (centralLowerFaceIds half).Nodup ∧
    (centralFixedFaceIds half).Nodup ∧
    (centralUpperFaceIds half).Nodup := by
  have hfull :
      (slabPhysicalFaceEdges (centralExtent half)).Nodup := by
    unfold slabPhysicalFaceEdges
    exact rangeNodupLocal _
  have hall :
      ((centralLowerFaceIds half ++ centralFixedFaceIds half) ++
        centralUpperFaceIds half).Nodup := by
    simpa [centralLowerFaceIds, centralFixedFaceIds,
      centralUpperFaceIds] using
      ((centralSlabFaceIdParts_perm half).symm.nodup hfull)
  have houter := List.nodup_append.mp hall
  have hlowerFixed := List.nodup_append.mp houter.1
  exact ⟨hlowerFixed.1, hlowerFixed.2.1, houter.2.1⟩

theorem centralHalfStates_nodup (K half : Nat) :
    (centralHalfStates K half).Nodup := by
  exact boundedEdgeLabellings_nodup K (centralLowerFaceIds half)
    (centralFaceIdParts_nodup half).1

theorem centralBoundaryChannels_nodup (K half : Nat) :
    (centralBoundaryChannels K half).Nodup := by
  exact boundedEdgeLabellings_nodup K (centralFixedFaceIds half)
    (centralFaceIdParts_nodup half).2.1

private theorem nodupCartesian {A B : Type}
    (xs : List A) (ys : List B)
    (hxs : xs.Nodup) (hys : ys.Nodup) :
    (xs.flatMap (fun x => ys.map (fun y => (x, y)))).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
      have hparts := List.nodup_cons.mp hxs
      simp only [List.flatMap_cons]
      apply List.nodup_append.mpr
      refine ⟨?_, ih hparts.2, ?_⟩
      · exact nodup_map_of_injOn (fun y => (x, y)) ys hys
          (fun _ _ _ _ heq => by injection heq)
      · intro left hleft right hright heq
        obtain ⟨y, _, hleftEq⟩ := List.mem_map.mp hleft
        obtain ⟨z, hz, hrightMap⟩ := List.mem_flatMap.mp hright
        obtain ⟨t, _, hrightEq⟩ := List.mem_map.mp hrightMap
        rw [← hleftEq, ← hrightEq] at heq
        have hxz : x = z := by injection heq
        exact hparts.1 (hxz ▸ hz)

theorem centralReflectionTriples_nodup (K half : Nat) :
    (centralReflectionTriples K half).Nodup := by
  unfold centralReflectionTriples
  have houter := nodupCartesian
      (centralHalfStates K half)
      ((centralHalfStates K half).flatMap (fun right =>
        (centralBoundaryChannels K half).map (fun boundary =>
          (right, boundary))))
      (centralHalfStates_nodup K half)
      (nodupCartesian
        (centralHalfStates K half)
        (centralBoundaryChannels K half)
        (centralHalfStates_nodup K half)
        (centralBoundaryChannels_nodup K half))
  simpa only [List.map_flatMap, List.map_map,
    Function.comp_apply] using houter

theorem assembleCentralReflectionTriple_injective_on
    {K half : Nat} {left right : CentralReflectionTriple}
    (hleft : left ∈ centralReflectionTriples K half)
    (hright : right ∈ centralReflectionTriples K half)
    (heq : assembleCentralReflectionTriple half left =
      assembleCentralReflectionTriple half right) :
    left = right := by
  have hleftParts := mem_centralReflectionTriples.mp hleft
  have hrightParts := mem_centralReflectionTriples.mp hright
  have hlower : left.1 = right.1 := by
    have h := congrArg (centralLowerRestriction half) heq
    simpa [assembleCentralReflectionTriple,
      centralLowerRestriction_assemble hleftParts.1,
      centralLowerRestriction_assemble hrightParts.1] using h
  have hupper : left.2.1 = right.2.1 := by
    have h := congrArg (centralReflectedUpperRestriction half) heq
    simpa [assembleCentralReflectionTriple,
      centralReflectedUpperRestriction_assemble hleftParts.2.1,
      centralReflectedUpperRestriction_assemble hrightParts.2.1] using h
  have hboundary : left.2.2 = right.2.2 := by
    have h := congrArg (centralBoundaryRestriction half) heq
    simpa [assembleCentralReflectionTriple,
      centralBoundaryRestriction_assemble hleftParts.2.2,
      centralBoundaryRestriction_assemble hrightParts.2.2] using h
  exact Prod.ext hlower (Prod.ext hupper hboundary)

/-! ## 5. Exact list permutation against the pre-existing full enumeration -/

def centralAssembledSlabLabellings (K half : Nat) : List EdgeLabelling :=
  (centralReflectionTriples K half).map
    (assembleCentralReflectionTriple half)

theorem centralAssembledSlabLabellings_nodup (K half : Nat) :
    (centralAssembledSlabLabellings K half).Nodup := by
  unfold centralAssembledSlabLabellings
  apply nodup_map_of_injOn
    (assembleCentralReflectionTriple half)
    (centralReflectionTriples K half)
    (centralReflectionTriples_nodup K half)
  intro left hleft right hright heq
  exact assembleCentralReflectionTriple_injective_on hleft hright heq

private theorem fullSlabLabellings_nodup (K half : Nat) :
    (boundedEdgeLabellings K
      (slabPhysicalFaceEdges (centralExtent half))).Nodup := by
  apply boundedEdgeLabellings_nodup
  unfold slabPhysicalFaceEdges
  exact rangeNodupLocal _

theorem mem_centralAssembledSlabLabellings_iff
    {K half : Nat} {physical : EdgeLabelling} :
    physical ∈ centralAssembledSlabLabellings K half ↔
      physical ∈ boundedEdgeLabellings K
        (slabPhysicalFaceEdges (centralExtent half)) := by
  constructor
  · intro hphysical
    obtain ⟨triple, htriple, heq⟩ := List.mem_map.mp hphysical
    rw [← heq]
    have hparts := mem_centralReflectionTriples.mp htriple
    exact assembleReflectedSlabLabelling_mem_full
      hparts.1 hparts.2.2 hparts.2.1
  · intro hphysical
    let triple : CentralReflectionTriple :=
      (centralLowerRestriction half physical,
        (centralReflectedUpperRestriction half physical,
          centralBoundaryRestriction half physical))
    have htriple : triple ∈ centralReflectionTriples K half := by
      apply mem_centralReflectionTriples.mpr
      exact ⟨centralLowerRestriction_mem hphysical,
        centralReflectedUpperRestriction_mem hphysical,
        centralBoundaryRestriction_mem hphysical⟩
    apply List.mem_map.mpr
    refine ⟨triple, htriple, ?_⟩
    exact assembleReflectedSlabLabelling_restrictions hphysical

private theorem permOfNodupMemIff {A : Type} :
    ∀ (left right : List A), left.Nodup -> right.Nodup ->
      (∀ item, item ∈ left ↔ item ∈ right) -> left.Perm right
  | [], [], _, _, _ => List.Perm.nil
  | [], head :: tail, _, _, hmem => by
      have hfalse : head ∈ ([] : List A) :=
        (hmem head).2 List.mem_cons_self
      cases hfalse
  | head :: tail, right, hleft, hright, hmem => by
      have hleftParts := List.nodup_cons.mp hleft
      have hheadRight : head ∈ right :=
        (hmem head).1 List.mem_cons_self
      obtain ⟨before, after, hsplit⟩ :=
        List.append_of_mem hheadRight
      subst right
      have hmiddle : (head :: (before ++ after)).Perm
          (before ++ head :: after) := List.perm_middle.symm
      have hmiddleNodup : (head :: (before ++ after)).Nodup :=
        hmiddle.symm.nodup hright
      have hmiddleParts := List.nodup_cons.mp hmiddleNodup
      have htailMem : ∀ item,
          item ∈ tail ↔ item ∈ before ++ after := by
        intro item
        constructor
        · intro hitem
          have hne : item ≠ head := by
            intro heq
            subst item
            exact hleftParts.1 hitem
          have hrightItem :=
            (hmem item).1 (List.mem_cons_of_mem head hitem)
          rcases List.mem_append.mp hrightItem with hbefore | hrest
          · exact List.mem_append_left after hbefore
          · exact List.mem_append_right before
              ((List.mem_cons.mp hrest).resolve_left hne)
        · intro hitem
          have hne : item ≠ head := by
            intro heq
            subst item
            exact hmiddleParts.1 hitem
          have hrightItem : item ∈ before ++ head :: after := by
            rcases List.mem_append.mp hitem with hbefore | hafter
            · exact List.mem_append_left (head :: after) hbefore
            · exact List.mem_append_right before
                (List.mem_cons_of_mem head hafter)
          exact (List.mem_cons.mp
            ((hmem item).2 hrightItem)).resolve_left hne
      have htailPerm := permOfNodupMemIff
        tail (before ++ after) hleftParts.2 hmiddleParts.2 htailMem
      exact (List.Perm.cons head htailPerm).trans hmiddle

/-- The assembled lower/right/interface Cartesian list is exactly the full
pre-existing corrected-slab labelling list, with no omissions or duplicates. -/
theorem centralAssembledSlabLabellings_perm_full (K half : Nat) :
    (centralAssembledSlabLabellings K half).Perm
      (boundedEdgeLabellings K
        (slabPhysicalFaceEdges (centralExtent half))) := by
  apply permOfNodupMemIff
  · exact centralAssembledSlabLabellings_nodup K half
  · exact fullSlabLabellings_nodup K half
  · intro physical
    exact mem_centralAssembledSlabLabellings_iff

private theorem listQSumPerm {A : Type} (value : A -> Q') :
    ∀ {left right : List A}, left.Perm right ->
      listQSum value left ≈ listQSum value right
  | _, _, List.Perm.nil => Q'.eqv_refl 0
  | _, _, List.Perm.cons _ hperm =>
      Q'.add_eqv_congr_left _ _ _ (listQSumPerm value hperm)
  | _, _, List.Perm.swap first second rest => by
      change value second + (value first + listQSum value rest) ≈
        value first + (value second + listQSum value rest)
      refine Q'.eqv_trans _
        ((value second + value first) + listQSum value rest) _
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _
        ((value first + value second) + listQSum value rest) _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.add_comm_eqv _ _)) ?_
      exact Q'.add_assoc_eqv _ _ _
  | _, _, List.Perm.trans hleft hright =>
      Q'.eqv_trans _ _ _
        (listQSumPerm value hleft) (listQSumPerm value hright)

private theorem listQSumCongrMem {A : Type} {left right : A -> Q'} :
    ∀ xs : List A, (∀ x, x ∈ xs -> left x ≈ right x) ->
      listQSum left xs ≈ listQSum right xs
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hagree =>
      Q'.add_eqv_congr'
        (hagree head List.mem_cons_self)
        (listQSumCongrMem tail
          (fun x hx => hagree x (List.mem_cons_of_mem head hx)))

theorem listQSum_centralAssembledSlabLabellings
    (value : EdgeLabelling -> Q') (K half : Nat) :
    listQSum value (centralAssembledSlabLabellings K half) ≈
      listQSum value (boundedEdgeLabellings K
        (slabPhysicalFaceEdges (centralExtent half))) := by
  exact listQSumPerm value
    (centralAssembledSlabLabellings_perm_full K half)

/-! ## 6. Full partition and full OS numerator equalities -/

def centralCartesianPhysicalPartition
    (w : Q') (K half : Nat) : Q' :=
  listQSum
    (fun triple => slabParametricKPhysicalTerm w K (centralExtent half)
      (assembleCentralReflectionTriple half triple))
    (centralReflectionTriples K half)

theorem centralCartesianPhysicalPartition_eq_full
    (w : Q') (K half : Nat) :
    centralCartesianPhysicalPartition w K half ≈
      slabParametricKPhysicalPartition w K (centralExtent half) := by
  refine Q'.eqv_trans _
    (listQSum (slabParametricKPhysicalTerm w K (centralExtent half))
      (centralAssembledSlabLabellings K half)) _ ?_ ?_
  · exact Q'.eqv_of_eq (Eq.symm
      (listQSum_map
        (slabParametricKPhysicalTerm w K (centralExtent half))
        (assembleCentralReflectionTriple half)
        (centralReflectionTriples K half)))
  · unfold slabParametricKPhysicalPartition
    exact listQSum_centralAssembledSlabLabellings _ K half

/-- Independently defined full finite-volume reflection numerator: sum over
the pre-existing full slab Cartesian space, with a test function on the lower
restriction and its reflected upper restriction. -/
def centralFullPhysicalReflectionQuadratic
    (w : Q') (K half : Nat)
    (coefficient : EdgeLabelling -> Q') : Q' :=
  listQSum
    (fun physical =>
      (coefficient (centralLowerRestriction half physical) *
        coefficient (centralReflectedUpperRestriction half physical)) *
      slabParametricKPhysicalTerm w K (centralExtent half) physical)
    (boundedEdgeLabellings K
      (slabPhysicalFaceEdges (centralExtent half)))

private def centralTripleReflectionTerm
    (w : Q') (K half : Nat)
    (coefficient : EdgeLabelling -> Q')
    (triple : CentralReflectionTriple) : Q' :=
  (coefficient triple.1 * coefficient triple.2.1) *
    slabParametricKPhysicalTerm w K (centralExtent half)
      (assembleCentralReflectionTriple half triple)

private theorem centralTripleReflectionSum_eq_nested
    (w : Q') (K half : Nat)
    (coefficient : EdgeLabelling -> Q') :
    listQSum (centralTripleReflectionTerm w K half coefficient)
        (centralReflectionTriples K half) ≈
      listQSum
        (fun left => listQSum
          (fun right => listQSum
            (fun boundary =>
              (coefficient left * coefficient right) *
                slabParametricKPhysicalTerm w K (centralExtent half)
                  (assembleReflectedSlabLabelling half
                    left boundary right))
            (centralBoundaryChannels K half))
          (centralHalfStates K half))
        (centralHalfStates K half) := by
  unfold centralReflectionTriples
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap
      (centralTripleReflectionTerm w K half coefficient)
      (fun left =>
        (centralHalfStates K half).flatMap (fun right =>
          (centralBoundaryChannels K half).map (fun boundary =>
            (left, (right, boundary)))))
      (centralHalfStates K half)) ?_
  apply listQSum_congr
  intro left
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap
      (centralTripleReflectionTerm w K half coefficient)
      (fun right =>
        (centralBoundaryChannels K half).map (fun boundary =>
          (left, (right, boundary))))
      (centralHalfStates K half)) ?_
  apply listQSum_congr
  intro right
  rw [listQSum_map]
  exact Q'.eqv_refl _

private theorem centralPhysicalReflectionQuadratic_eq_tripleSum
    (w : Q') (K half : Nat)
    (coefficient : EdgeLabelling -> Q') :
    centralPhysicalReflectionQuadratic w K half coefficient ≈
      listQSum (centralTripleReflectionTerm w K half coefficient)
        (centralReflectionTriples K half) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun left => listQSum
        (fun right => listQSum
          (fun boundary =>
            (coefficient left * coefficient right) *
              slabParametricKPhysicalTerm w K (centralExtent half)
                (assembleReflectedSlabLabelling half
                  left boundary right))
          (centralBoundaryChannels K half))
        (centralHalfStates K half))
      (centralHalfStates K half)) _ ?_ ?_
  · unfold centralPhysicalReflectionQuadratic
    apply listQSum_congr
    intro left
    apply listQSum_congr
    intro right
    unfold centralPhysicalReflectedKernel
    exact Q'.eqv_symm
      (listQSum_mul_left
        (coefficient left * coefficient right)
        (fun boundary =>
          slabParametricKPhysicalTerm w K (centralExtent half)
            (assembleReflectedSlabLabelling half left boundary right))
        (centralBoundaryChannels K half))
  · exact Q'.eqv_symm
      (centralTripleReflectionSum_eq_nested w K half coefficient)

private theorem centralTripleReflectionSum_eq_assembledFullWeight
    (w : Q') (K half : Nat)
    (coefficient : EdgeLabelling -> Q') :
    listQSum (centralTripleReflectionTerm w K half coefficient)
        (centralReflectionTriples K half) ≈
      listQSum
        (fun physical =>
          (coefficient (centralLowerRestriction half physical) *
            coefficient (centralReflectedUpperRestriction half physical)) *
          slabParametricKPhysicalTerm w K (centralExtent half) physical)
        (centralAssembledSlabLabellings K half) := by
  unfold centralAssembledSlabLabellings
  rw [listQSum_map]
  apply listQSumCongrMem
  intro triple htriple
  have hparts := mem_centralReflectionTriples.mp htriple
  unfold centralTripleReflectionTerm assembleCentralReflectionTriple
  rw [centralLowerRestriction_assemble hparts.1,
    centralReflectedUpperRestriction_assemble hparts.2.1]
  exact Q'.eqv_refl _

/-- The assembled Gram quadratic is exactly the independently defined full
finite-volume Osterwalder--Schrader numerator.  Coverage and multiplicity are
certified by the literal list permutation above. -/
theorem centralPhysicalReflectionQuadratic_eq_full
    (w : Q') (K half : Nat)
    (coefficient : EdgeLabelling -> Q') :
    centralPhysicalReflectionQuadratic w K half coefficient ≈
      centralFullPhysicalReflectionQuadratic w K half coefficient := by
  refine Q'.eqv_trans _ _ _
    (centralPhysicalReflectionQuadratic_eq_tripleSum
      w K half coefficient) ?_
  refine Q'.eqv_trans _
    (listQSum
      (fun physical =>
        (coefficient (centralLowerRestriction half physical) *
          coefficient (centralReflectedUpperRestriction half physical)) *
        slabParametricKPhysicalTerm w K (centralExtent half) physical)
      (centralAssembledSlabLabellings K half)) _
    (centralTripleReflectionSum_eq_assembledFullWeight
      w K half coefficient) ?_
  unfold centralFullPhysicalReflectionQuadratic
  exact listQSum_centralAssembledSlabLabellings _ K half

/-- Constructive OS positivity for the independently defined complete full
slab numerator. -/
theorem centralFullPhysicalReflectionQuadratic_nonnegative
    {w : Q'} {K half : Nat} (hw : (0 : Q') <= w)
    (coefficient : EdgeLabelling -> Q') :
    (0 : Q') <=
      centralFullPhysicalReflectionQuadratic w K half coefficient := by
  exact Q'.le_trans' _ _ _
    (centralPhysicalReflectionQuadratic_nonnegative hw coefficient)
    (Q'.le_of_eqv
      (centralPhysicalReflectionQuadratic_eq_full
        w K half coefficient))

end YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralLowerRestriction_mem
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralBoundaryRestriction_mem
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralReflectedUpperRestriction_mem
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralLowerRestriction_assemble
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralBoundaryRestriction_assemble
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralReflectedUpperRestriction_assemble
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.assembleReflectedSlabLabelling_restrictions
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.mem_centralReflectionTriples
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralHalfStates_nodup
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralBoundaryChannels_nodup
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralReflectionTriples_nodup
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.assembleCentralReflectionTriple_injective_on
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralAssembledSlabLabellings_nodup
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.mem_centralAssembledSlabLabellings_iff
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralAssembledSlabLabellings_perm_full
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.listQSum_centralAssembledSlabLabellings
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralCartesianPhysicalPartition_eq_full
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralPhysicalReflectionQuadratic_eq_full
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex.centralFullPhysicalReflectionQuadratic_nonnegative
