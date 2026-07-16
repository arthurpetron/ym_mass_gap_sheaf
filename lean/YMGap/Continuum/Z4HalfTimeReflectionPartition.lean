/-
# Exact reflection reindexing of the corrected-slab partition

The geometric reflection is only an involution on the finite physical face
coordinates.  Composing a labelling with it naively can therefore create
spurious nonzero values outside the Cartesian support.  This file supplies
the required zero extension, proves that it is an involution on every
enumerated labelling, and constructs the resulting permutation of the
literal `boundedEdgeLabellings` list.

The local corrected-slab term is already reflection invariant.  Combining
that theorem with the genuine Cartesian permutation gives exact partition
and reflected-event equalities.  These are symmetry statements only; no
reflection-positivity or Gram-factorization claim is made here.
-/

import YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
import YMGap.Continuum.Z4BoundedEdgeLabellingNodup

namespace YMGap.Continuum.Z4HalfTimeReflectionPartition

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4BoundedEdgeLabellingNodup
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

private theorem rangeNodupLocal (n : Nat) : (List.range n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ k ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr
          ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro x hx y hy hxy
      have hyk : y = k := List.mem_singleton.mp hy
      rw [hxy, hyk] at hx
      exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl k)

/-! ## 1. The supported reflection involution -/

/-- Reflection on the finite physical face coordinates, extended by zero on
every other numerical identifier.  The zero branch is essential: the raw
list-search reflection has no geometric meaning outside the physical range. -/
def reflectSupportedSlabFaceLabelling
    (extent : Nat) (physical : EdgeLabelling) : EdgeLabelling :=
  fun id =>
    if id ∈ slabPhysicalFaceEdges extent then
      physical (slabFaceReflectId extent id)
    else 0

theorem reflectSupportedSlabFaceLabelling_eq_on_physical
    (extent : Nat) (physical : EdgeLabelling)
    {id : Nat} (hid : id ∈ slabPhysicalFaceEdges extent) :
    reflectSupportedSlabFaceLabelling extent physical id =
      reflectSlabFaceLabelling extent physical id := by
  simp [reflectSupportedSlabFaceLabelling,
    reflectSlabFaceLabelling, hid]

theorem reflectSupportedSlabFaceLabelling_zero_off_physical
    (extent : Nat) (physical : EdgeLabelling)
    {id : Nat} (hid : id ∉ slabPhysicalFaceEdges extent) :
    reflectSupportedSlabFaceLabelling extent physical id = 0 := by
  simp [reflectSupportedSlabFaceLabelling, hid]

theorem reflectSupportedSlabFaceLabelling_bounded
    {K extent : Nat} {physical : EdgeLabelling}
    (hbounded : SlabFaceLabellingBounded K extent physical) :
    SlabFaceLabellingBounded K extent
      (reflectSupportedSlabFaceLabelling extent physical) := by
  intro id hid
  rw [reflectSupportedSlabFaceLabelling_eq_on_physical extent physical hid]
  exact hbounded _ (slabFaceReflectId_physical hid)

/-- On labellings supported on the physical coordinate list, the supported
reflection is a genuine equality-level involution on the whole function. -/
theorem reflectSupportedSlabFaceLabelling_involutive
    (extent : Nat) (physical : EdgeLabelling)
    (hsupported : ∀ id, id ∉ slabPhysicalFaceEdges extent ->
      physical id = 0) :
    reflectSupportedSlabFaceLabelling extent
        (reflectSupportedSlabFaceLabelling extent physical) = physical := by
  funext id
  by_cases hid : id ∈ slabPhysicalFaceEdges extent
  · simp only [reflectSupportedSlabFaceLabelling, if_pos hid]
    rw [if_pos (slabFaceReflectId_physical hid),
      slabFaceReflectId_involutive hid]
  · rw [reflectSupportedSlabFaceLabelling_zero_off_physical
      extent (reflectSupportedSlabFaceLabelling extent physical) hid,
      hsupported id hid]

/-! ## 2. Extensionality of the exact corrected-slab summand -/

private theorem eliminateLinks_eq_on
    (left right : Nat -> Q') : ∀ ids : List Nat,
    (∀ id, id ∈ ids -> left id = right id) ->
      eliminateLinks left ids = eliminateLinks right ids
  | [], _ => rfl
  | head :: tail, hagree => by
      simp only [eliminateLinks]
      rw [hagree head List.mem_cons_self,
        eliminateLinks_eq_on left right tail
          (fun id hid => hagree id (List.mem_cons_of_mem head hid))]

private theorem listMap_eq_on {A B : Type}
    (left right : A -> B) : ∀ xs : List A,
    (∀ x, x ∈ xs -> left x = right x) ->
      xs.map left = xs.map right
  | [], _ => rfl
  | head :: tail, hagree => by
      simp only [List.map_cons]
      rw [hagree head List.mem_cons_self,
        listMap_eq_on left right tail
          (fun x hx => hagree x (List.mem_cons_of_mem head hx))]

/-- The corrected-slab term depends only on the displayed physical face
coordinates.  This closes the zero-extension bookkeeping at both the face
product and every incident-spin list. -/
theorem slabParametricKPhysicalTerm_eq_of_eq_on_physical
    (w : Q') (K extent : Nat) (left right : EdgeLabelling)
    (hagree : ∀ id, id ∈ slabPhysicalFaceEdges extent ->
      left id = right id) :
    slabParametricKPhysicalTerm w K extent left =
      slabParametricKPhysicalTerm w K extent right := by
  have hface :
      slabParametricKPhysicalFaceFactor w K extent left =
        slabParametricKPhysicalFaceFactor w K extent right := by
    unfold slabParametricKPhysicalFaceFactor
    apply eliminateLinks_eq_on
    intro id hid
    rw [hagree id hid]
  have hlinks :
      slabExplicitLinkMultiplicityProduct K extent left =
        slabExplicitLinkMultiplicityProduct K extent right := by
    unfold slabExplicitLinkMultiplicityProduct
    apply natListProduct_congr
    intro link _
    unfold slabExplicitLinkMultiplicity
    have hspins :
        (slabIncidentPlaqIds extent link).map left =
          (slabIncidentPlaqIds extent link).map right := by
      apply listMap_eq_on
      intro id hid
      exact hagree id (slabIncidentPlaqId_physical hid)
    rw [hspins]
  unfold slabParametricKPhysicalTerm
  rw [hface, hlinks]

/-- The zero-extended reflection has the same exact term as the raw physical
reflection and hence preserves the complete corrected-slab summand. -/
theorem slabParametricKPhysicalTerm_supported_reflection
    (w : Q') {K extent : Nat} {physical : EdgeLabelling}
    (hbounded : SlabFaceLabellingBounded K extent physical) :
    slabParametricKPhysicalTerm w K extent
        (reflectSupportedSlabFaceLabelling extent physical) ≈
      slabParametricKPhysicalTerm w K extent physical := by
  refine Q'.eqv_trans _
    (slabParametricKPhysicalTerm w K extent
      (reflectSlabFaceLabelling extent physical)) _ ?_ ?_
  · apply Q'.eqv_of_eq
    apply slabParametricKPhysicalTerm_eq_of_eq_on_physical
    intro id hid
    exact reflectSupportedSlabFaceLabelling_eq_on_physical
      extent physical hid
  · exact slabParametricKPhysicalTerm_reflection w hbounded

/-! ## 3. Literal Cartesian permutation -/

theorem reflectSupportedSlabFaceLabelling_mem
    {K extent : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (slabPhysicalFaceEdges extent)) :
    reflectSupportedSlabFaceLabelling extent physical ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges extent) := by
  have hsound := boundedEdgeLabellings_sound K
    (slabPhysicalFaceEdges extent) physical hphysical
  apply boundedEdgeLabellings_complete
  · intro id hid
    rw [reflectSupportedSlabFaceLabelling_eq_on_physical
      extent physical hid]
    exact hsound.1 _ (slabFaceReflectId_physical hid)
  · intro id hid
    exact reflectSupportedSlabFaceLabelling_zero_off_physical
      extent physical hid

theorem reflectSupportedSlabFaceLabelling_injective_on_bounded
    {K extent : Nat} {left right : EdgeLabelling}
    (hleft : left ∈ boundedEdgeLabellings K
      (slabPhysicalFaceEdges extent))
    (hright : right ∈ boundedEdgeLabellings K
      (slabPhysicalFaceEdges extent))
    (heq : reflectSupportedSlabFaceLabelling extent left =
      reflectSupportedSlabFaceLabelling extent right) :
    left = right := by
  have hleftSound := boundedEdgeLabellings_sound K
    (slabPhysicalFaceEdges extent) left hleft
  have hrightSound := boundedEdgeLabellings_sound K
    (slabPhysicalFaceEdges extent) right hright
  have hreflected := congrArg
    (reflectSupportedSlabFaceLabelling extent) heq
  rw [reflectSupportedSlabFaceLabelling_involutive
        extent left hleftSound.2,
      reflectSupportedSlabFaceLabelling_involutive
        extent right hrightSound.2] at hreflected
  exact hreflected

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
          have hy := (hmem item).1
            (List.mem_cons_of_mem head hitem)
          rcases List.mem_append.mp hy with hbefore | hrest
          · exact List.mem_append_left after hbefore
          · exact List.mem_append_right before
              ((List.mem_cons.mp hrest).resolve_left hne)
        · intro hitem
          have hne : item ≠ head := by
            intro heq
            subst item
            exact hmiddleParts.1 hitem
          have hy : item ∈ before ++ head :: after := by
            rcases List.mem_append.mp hitem with hbefore | hafter
            · exact List.mem_append_left (head :: after) hbefore
            · exact List.mem_append_right before
                (List.mem_cons_of_mem head hafter)
          exact (List.mem_cons.mp ((hmem item).2 hy)).resolve_left hne
      have htailPerm := permOfNodupMemIff tail (before ++ after)
        hleftParts.2 hmiddleParts.2 htailMem
      exact (List.Perm.cons head htailPerm).trans hmiddle

/-- The literal finite Cartesian enumeration is permuted by the supported
face reflection.  This is the constructive finite-volume change of
variables, not merely an extensional statement about its support. -/
theorem boundedSlabFaceLabellings_reflection_perm (K extent : Nat) :
    ((boundedEdgeLabellings K (slabPhysicalFaceEdges extent)).map
        (reflectSupportedSlabFaceLabelling extent)).Perm
      (boundedEdgeLabellings K (slabPhysicalFaceEdges extent)) := by
  let labels := boundedEdgeLabellings K (slabPhysicalFaceEdges extent)
  have hedgeNodup : (slabPhysicalFaceEdges extent).Nodup := by
    unfold slabPhysicalFaceEdges
    exact rangeNodupLocal _
  have hlabelsNodup : labels.Nodup :=
    boundedEdgeLabellings_nodup K
      (slabPhysicalFaceEdges extent) hedgeNodup
  apply permOfNodupMemIff
  · apply nodup_map_of_injOn
      (reflectSupportedSlabFaceLabelling extent) labels hlabelsNodup
    intro left hleft right hright heq
    exact reflectSupportedSlabFaceLabelling_injective_on_bounded
      hleft hright heq
  · exact hlabelsNodup
  · intro physical
    constructor
    · intro hphysical
      obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hphysical
      rw [← hsourceEq]
      exact reflectSupportedSlabFaceLabelling_mem hsource
    · intro hphysical
      have hreflected := reflectSupportedSlabFaceLabelling_mem hphysical
      apply List.mem_map.mpr
      refine ⟨reflectSupportedSlabFaceLabelling extent physical,
        hreflected, ?_⟩
      exact reflectSupportedSlabFaceLabelling_involutive extent physical
        (boundedEdgeLabellings_sound K
          (slabPhysicalFaceEdges extent) physical hphysical).2

/-! ## 4. Partition and event symmetry -/

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

def slabParametricKPhysicalPartition
    (w : Q') (K extent : Nat) : Q' :=
  listQSum (slabParametricKPhysicalTerm w K extent)
    (boundedEdgeLabellings K (slabPhysicalFaceEdges extent))

/-- Exact finite-volume partition invariance under the literal reflected
Cartesian reindexing. -/
theorem slabParametricKPhysicalPartition_reflection_reindex
    (w : Q') (K extent : Nat) :
    listQSum
        (fun physical => slabParametricKPhysicalTerm w K extent
          (reflectSupportedSlabFaceLabelling extent physical))
        (boundedEdgeLabellings K (slabPhysicalFaceEdges extent)) ≈
      slabParametricKPhysicalPartition w K extent := by
  rw [← listQSum_map
    (slabParametricKPhysicalTerm w K extent)
    (reflectSupportedSlabFaceLabelling extent)
    (boundedEdgeLabellings K (slabPhysicalFaceEdges extent))]
  unfold slabParametricKPhysicalPartition
  exact listQSumPerm _
    (boundedSlabFaceLabellings_reflection_perm K extent)

/-- The same partition identity proved pointwise from local term symmetry.
Keeping both proofs in the kernel separates the local weight theorem from the
global Cartesian change of variables. -/
theorem slabParametricKPhysicalPartition_reflection_pointwise
    (w : Q') (K extent : Nat) :
    listQSum
        (fun physical => slabParametricKPhysicalTerm w K extent
          (reflectSupportedSlabFaceLabelling extent physical))
        (boundedEdgeLabellings K (slabPhysicalFaceEdges extent)) ≈
      slabParametricKPhysicalPartition w K extent := by
  unfold slabParametricKPhysicalPartition
  apply listQSumCongrMem
  intro physical hphysical
  exact slabParametricKPhysicalTerm_supported_reflection w
    (fun id hid => Nat.le_of_lt_succ
      ((boundedEdgeLabellings_sound K
        (slabPhysicalFaceEdges extent) physical hphysical).1 id hid))

def slabEventNumerator
    (w : Q') (K extent : Nat)
    (event : EdgeLabelling -> Bool) : Q' :=
  listQSum
    (fun physical =>
      if event physical = true then
        slabParametricKPhysicalTerm w K extent physical
      else 0)
    (boundedEdgeLabellings K (slabPhysicalFaceEdges extent))

def reflectSlabEvent (extent : Nat)
    (event : EdgeLabelling -> Bool) : EdgeLabelling -> Bool :=
  fun physical =>
    event (reflectSupportedSlabFaceLabelling extent physical)

/-- Every Boolean cylinder event and its reflected event have the same exact
unnormalized finite-volume weight.  This is the strongest event-level result
that follows from reflection symmetry alone. -/
theorem slabEventNumerator_reflection
    (w : Q') (K extent : Nat)
    (event : EdgeLabelling -> Bool) :
    slabEventNumerator w K extent (reflectSlabEvent extent event) ≈
      slabEventNumerator w K extent event := by
  let labels := boundedEdgeLabellings K (slabPhysicalFaceEdges extent)
  let reflect := reflectSupportedSlabFaceLabelling extent
  let weight := slabParametricKPhysicalTerm w K extent
  let eventWeight : EdgeLabelling -> Q' := fun physical =>
    if event physical = true then weight physical else 0
  have hpoint : listQSum
      (fun physical =>
        if event (reflect physical) = true then weight physical else 0)
      labels ≈
      listQSum (fun physical => eventWeight (reflect physical)) labels := by
    apply listQSumCongrMem
    intro physical hphysical
    by_cases hevent : event (reflect physical) = true
    · simp only [eventWeight, hevent, if_true]
      exact Q'.eqv_symm
        (slabParametricKPhysicalTerm_supported_reflection w
          (fun id hid => Nat.le_of_lt_succ
            ((boundedEdgeLabellings_sound K
              (slabPhysicalFaceEdges extent) physical hphysical).1 id hid)))
    · simp [eventWeight, hevent]
      exact Q'.eqv_refl 0
  unfold slabEventNumerator reflectSlabEvent
  change listQSum
      (fun physical =>
        if event (reflect physical) = true then weight physical else 0)
      labels ≈ listQSum eventWeight labels
  refine Q'.eqv_trans _ _ _ hpoint ?_
  rw [← listQSum_map eventWeight reflect labels]
  exact listQSumPerm eventWeight
    (boundedSlabFaceLabellings_reflection_perm K extent)

end YMGap.Continuum.Z4HalfTimeReflectionPartition

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4HalfTimeReflectionPartition.reflectSupportedSlabFaceLabelling_involutive
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPartition.slabParametricKPhysicalTerm_eq_of_eq_on_physical
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPartition.slabParametricKPhysicalTerm_supported_reflection
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPartition.reflectSupportedSlabFaceLabelling_mem
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPartition.reflectSupportedSlabFaceLabelling_injective_on_bounded
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPartition.boundedSlabFaceLabellings_reflection_perm
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPartition.slabParametricKPhysicalPartition_reflection_reindex
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPartition.slabParametricKPhysicalPartition_reflection_pointwise
#print axioms YMGap.Continuum.Z4HalfTimeReflectionPartition.slabEventNumerator_reflection
