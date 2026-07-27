/-
# Exact full-carrier reindexing for the orientation-correct U(1) slab

The conditional twisted-Gram theorem is stated on independent lower,
fixed-face, and reflected-upper carriers.  This module proves that their
orientation-correct assembly enumerates the pre-existing complete signed
charge carrier exactly once.

The upper restriction is not the orientation-blind pullback used for
unsigned spin labels: it applies `reflectChargeLabel` after reading the
reflected face.  Consequently it is a literal inverse to
`assembleU1ReflectedSlabLabelling`, including on temporal plaquettes.

After proving the mapped Cartesian triple list is a permutation of
`U1SlabData.states`, the conditional quadratic is identified with an
independently defined all-label physical numerator.  Thus the fixed-face
conditional integration loses neither states nor multiplicities.

## Axiom gate

Finite lists, integers, and exact `Q'` arithmetic only.  No `Classical.*`,
`native_decide`, custom axiom, noncomputable declaration, or placeholder.
-/

import YMGap.Continuum.BF4U1TwistedReflectionGram

namespace YMGap.Continuum.BF4U1TwistedPhysicalReindex

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4U1ReflectionCovariance
open YMGap.Continuum.BF4U1SameCarrierPushforward
open YMGap.Continuum.BF4U1TwistedReflectionGram
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
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Orientation-correct restriction of the upper half -/

/-- Read an upper-half signed-charge labelling through reflection as a
lower-half labelling.  Temporal face charges acquire the reflection
orientation sign. -/
def u1ReflectedUpperRestriction
    (half : Nat) (physical : ChargeLabelling) : ChargeLabelling :=
  fun id =>
    if id ∈ centralLowerFaceIds half then
      reflectChargeLabel
        (slabPlaquetteAt (centralExtent half) id).2
        (physical (slabFaceReflectId (centralExtent half) id))
    else 0

theorem u1ReflectedUpperRestriction_mem
    {cutoff half : Nat} {physical : ChargeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings (2 * cutoff)
      (slabPhysicalFaceEdges (centralExtent half))) :
    u1ReflectedUpperRestriction half physical ∈
      boundedEdgeLabellings (2 * cutoff)
        (centralLowerFaceIds half) := by
  have hsound := boundedEdgeLabellings_sound (2 * cutoff)
    (slabPhysicalFaceEdges (centralExtent half)) physical hphysical
  apply boundedEdgeLabellings_complete
  · intro id hid
    simp only [u1ReflectedUpperRestriction, if_pos hid]
    apply reflectChargeLabel_lt_cutoff
    exact hsound.1 _
      (slabFaceReflectId_physical
        (mem_centralLowerFaceIds.mp hid).1)
  · intro id hid
    simp [u1ReflectedUpperRestriction, hid]

/-! ## 2. Restriction and assembly are inverse -/

theorem centralLowerRestriction_assembleU1
    {cutoff half : Nat}
    {left boundary right : ChargeLabelling}
    (hleft : left ∈ boundedEdgeLabellings (2 * cutoff)
      (centralLowerFaceIds half)) :
    centralLowerRestriction half
      (assembleU1ReflectedSlabLabelling half left boundary right) =
        left := by
  have hsound := boundedEdgeLabellings_sound (2 * cutoff)
    (centralLowerFaceIds half) left hleft
  funext id
  by_cases hid : id ∈ centralLowerFaceIds half
  · have hparts := mem_centralLowerFaceIds.mp hid
    simp only [centralLowerRestriction, if_pos hid]
    exact assembleU1ReflectedSlabLabelling_lower hparts.1 hparts.2
  · rw [hsound.2 id hid]
    simp [centralLowerRestriction, hid]

theorem centralBoundaryRestriction_assembleU1
    {cutoff half : Nat}
    {left boundary right : ChargeLabelling}
    (hboundary : boundary ∈ boundedEdgeLabellings (2 * cutoff)
      (centralFixedFaceIds half)) :
    centralBoundaryRestriction half
      (assembleU1ReflectedSlabLabelling half left boundary right) =
        boundary := by
  have hsound := boundedEdgeLabellings_sound (2 * cutoff)
    (centralFixedFaceIds half) boundary hboundary
  funext id
  by_cases hid : id ∈ centralFixedFaceIds half
  · have hparts := mem_centralFixedFaceIds.mp hid
    simp only [centralBoundaryRestriction, if_pos hid]
    exact assembleU1ReflectedSlabLabelling_fixed hparts.1 hparts.2
  · rw [hsound.2 id hid]
    simp [centralBoundaryRestriction, hid]

theorem u1ReflectedUpperRestriction_assembleU1
    {cutoff half : Nat}
    {left boundary right : ChargeLabelling}
    (hright : right ∈ boundedEdgeLabellings (2 * cutoff)
      (centralLowerFaceIds half)) :
    u1ReflectedUpperRestriction half
      (assembleU1ReflectedSlabLabelling half left boundary right) =
        right := by
  have hsound := boundedEdgeLabellings_sound (2 * cutoff)
    (centralLowerFaceIds half) right hright
  funext id
  by_cases hid : id ∈ centralLowerFaceIds half
  · have hparts := mem_centralLowerFaceIds.mp hid
    have hreflectedPhysical := slabFaceReflectId_physical hparts.1
    have hreflectedSide := slabFaceReflectId_side hparts.1
    rw [hparts.2] at hreflectedSide
    simp only [u1ReflectedUpperRestriction, if_pos hid]
    rw [assembleU1ReflectedSlabLabelling_upper
        hreflectedPhysical
        (by simpa [flipSide] using hreflectedSide),
      slabPlaquetteAt_slabFaceReflectId hparts.1,
      timeReflectPlaquette_plane,
      slabFaceReflectId_involutive hparts.1,
      reflectChargeLabel_involutive]
  · rw [hsound.2 id hid]
    simp [u1ReflectedUpperRestriction, hid]

theorem assembleU1ReflectedSlabLabelling_zero_off_physical
    (half : Nat) (left boundary right : ChargeLabelling)
    {id : Nat}
    (hid : id ∉ slabPhysicalFaceEdges (centralExtent half)) :
    assembleU1ReflectedSlabLabelling half left boundary right id = 0 := by
  simp [assembleU1ReflectedSlabLabelling, hid]

theorem assembleU1ReflectedSlabLabelling_restrictions
    {cutoff half : Nat} {physical : ChargeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings (2 * cutoff)
      (slabPhysicalFaceEdges (centralExtent half))) :
    assembleU1ReflectedSlabLabelling half
        (centralLowerRestriction half physical)
        (centralBoundaryRestriction half physical)
        (u1ReflectedUpperRestriction half physical) =
      physical := by
  have hsound := boundedEdgeLabellings_sound (2 * cutoff)
    (slabPhysicalFaceEdges (centralExtent half)) physical hphysical
  funext id
  by_cases hid : id ∈ slabPhysicalFaceEdges (centralExtent half)
  · cases hside : plaquetteHalfSide half
        (slabPlaquetteAt (centralExtent half) id)
    · rw [assembleU1ReflectedSlabLabelling_lower hid hside]
      simp [centralLowerRestriction,
        mem_centralLowerFaceIds.mpr ⟨hid, hside⟩]
    · rw [assembleU1ReflectedSlabLabelling_fixed hid hside]
      simp [centralBoundaryRestriction,
        mem_centralFixedFaceIds.mpr ⟨hid, hside⟩]
    · rw [assembleU1ReflectedSlabLabelling_upper hid hside]
      have hreflectedPhysical := slabFaceReflectId_physical hid
      have hreflectedSide := slabFaceReflectId_side hid
      rw [hside] at hreflectedSide
      have hreflectedLower :
          slabFaceReflectId (centralExtent half) id ∈
            centralLowerFaceIds half :=
        mem_centralLowerFaceIds.mpr
          ⟨hreflectedPhysical,
            by simpa [flipSide] using hreflectedSide⟩
      simp only [u1ReflectedUpperRestriction,
        if_pos hreflectedLower]
      rw [slabPlaquetteAt_slabFaceReflectId hid,
        timeReflectPlaquette_plane,
        slabFaceReflectId_involutive hid,
        reflectChargeLabel_involutive]
  · rw [assembleU1ReflectedSlabLabelling_zero_off_physical
        half _ _ _ hid,
      hsound.2 id hid]

/-! ## 3. Boundedness of the orientation-correct assembly -/

theorem assembleU1ReflectedSlabLabelling_mem_full
    {cutoff half : Nat}
    {left boundary right : ChargeLabelling}
    (hleft : left ∈ boundedEdgeLabellings (2 * cutoff)
      (centralLowerFaceIds half))
    (hboundary : boundary ∈ boundedEdgeLabellings (2 * cutoff)
      (centralFixedFaceIds half))
    (hright : right ∈ boundedEdgeLabellings (2 * cutoff)
      (centralLowerFaceIds half)) :
    assembleU1ReflectedSlabLabelling half left boundary right ∈
      boundedEdgeLabellings (2 * cutoff)
        (slabPhysicalFaceEdges (centralExtent half)) := by
  have hleftSound := boundedEdgeLabellings_sound (2 * cutoff)
    (centralLowerFaceIds half) left hleft
  have hboundarySound := boundedEdgeLabellings_sound (2 * cutoff)
    (centralFixedFaceIds half) boundary hboundary
  have hrightSound := boundedEdgeLabellings_sound (2 * cutoff)
    (centralLowerFaceIds half) right hright
  apply boundedEdgeLabellings_complete
  · intro id hid
    cases hside : plaquetteHalfSide half
        (slabPlaquetteAt (centralExtent half) id)
    · rw [assembleU1ReflectedSlabLabelling_lower hid hside]
      exact hleftSound.1 id
        (mem_centralLowerFaceIds.mpr ⟨hid, hside⟩)
    · rw [assembleU1ReflectedSlabLabelling_fixed hid hside]
      exact hboundarySound.1 id
        (mem_centralFixedFaceIds.mpr ⟨hid, hside⟩)
    · rw [assembleU1ReflectedSlabLabelling_upper hid hside]
      apply reflectChargeLabel_lt_cutoff
      have hreflectedPhysical := slabFaceReflectId_physical hid
      have hreflectedSide := slabFaceReflectId_side hid
      rw [hside] at hreflectedSide
      exact hrightSound.1 _
        (mem_centralLowerFaceIds.mpr
          ⟨hreflectedPhysical,
            by simpa [flipSide] using hreflectedSide⟩)
  · intro id hid
    exact assembleU1ReflectedSlabLabelling_zero_off_physical
      half left boundary right hid

/-! ## 4. Exact Cartesian coverage -/

def assembleU1ReflectionTriple
    (half : Nat) (triple : CentralReflectionTriple) :
    ChargeLabelling :=
  assembleU1ReflectedSlabLabelling half
    triple.1 triple.2.2 triple.2.1

theorem assembleU1ReflectionTriple_injective_on
    {cutoff half : Nat} {left right : CentralReflectionTriple}
    (hleft : left ∈ centralReflectionTriples (2 * cutoff) half)
    (hright : right ∈ centralReflectionTriples (2 * cutoff) half)
    (heq : assembleU1ReflectionTriple half left =
      assembleU1ReflectionTriple half right) :
    left = right := by
  have hleftParts := mem_centralReflectionTriples.mp hleft
  have hrightParts := mem_centralReflectionTriples.mp hright
  have hlower : left.1 = right.1 := by
    have h := congrArg (centralLowerRestriction half) heq
    simpa [assembleU1ReflectionTriple,
      centralLowerRestriction_assembleU1 hleftParts.1,
      centralLowerRestriction_assembleU1 hrightParts.1] using h
  have hupper : left.2.1 = right.2.1 := by
    have h := congrArg (u1ReflectedUpperRestriction half) heq
    simpa [assembleU1ReflectionTriple,
      u1ReflectedUpperRestriction_assembleU1 hleftParts.2.1,
      u1ReflectedUpperRestriction_assembleU1 hrightParts.2.1] using h
  have hboundary : left.2.2 = right.2.2 := by
    have h := congrArg (centralBoundaryRestriction half) heq
    simpa [assembleU1ReflectionTriple,
      centralBoundaryRestriction_assembleU1 hleftParts.2.2,
      centralBoundaryRestriction_assembleU1 hrightParts.2.2] using h
  exact Prod.ext hlower (Prod.ext hupper hboundary)

def u1AssembledSlabLabellings
    (cutoff half : Nat) : List ChargeLabelling :=
  (centralReflectionTriples (2 * cutoff) half).map
    (assembleU1ReflectionTriple half)

theorem u1AssembledSlabLabellings_nodup
    (cutoff half : Nat) :
    (u1AssembledSlabLabellings cutoff half).Nodup := by
  unfold u1AssembledSlabLabellings
  apply nodup_map_of_injOn
    (assembleU1ReflectionTriple half)
    (centralReflectionTriples (2 * cutoff) half)
    (centralReflectionTriples_nodup (2 * cutoff) half)
  intro left hleft right hright heq
  exact assembleU1ReflectionTriple_injective_on
    hleft hright heq

theorem mem_u1AssembledSlabLabellings_iff
    {cutoff half : Nat} {physical : ChargeLabelling} :
    physical ∈ u1AssembledSlabLabellings cutoff half ↔
      physical ∈ boundedEdgeLabellings (2 * cutoff)
        (slabPhysicalFaceEdges (centralExtent half)) := by
  constructor
  · intro hphysical
    obtain ⟨triple, htriple, heq⟩ := List.mem_map.mp hphysical
    rw [← heq]
    have hparts := mem_centralReflectionTriples.mp htriple
    exact assembleU1ReflectedSlabLabelling_mem_full
      hparts.1 hparts.2.2 hparts.2.1
  · intro hphysical
    let triple : CentralReflectionTriple :=
      (centralLowerRestriction half physical,
        (u1ReflectedUpperRestriction half physical,
          centralBoundaryRestriction half physical))
    have htriple :
        triple ∈ centralReflectionTriples (2 * cutoff) half := by
      apply mem_centralReflectionTriples.mpr
      exact ⟨centralLowerRestriction_mem hphysical,
        u1ReflectedUpperRestriction_mem hphysical,
        centralBoundaryRestriction_mem hphysical⟩
    apply List.mem_map.mpr
    refine ⟨triple, htriple, ?_⟩
    exact assembleU1ReflectedSlabLabelling_restrictions hphysical

private theorem permOfNodupMemIff {A : Type} :
    ∀ (left right : List A), left.Nodup → right.Nodup →
      (∀ item, item ∈ left ↔ item ∈ right) → left.Perm right
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

private theorem fullU1SlabLabellings_nodup
    (cutoff half : Nat) :
    (boundedEdgeLabellings (2 * cutoff)
      (slabPhysicalFaceEdges (centralExtent half))).Nodup := by
  have hperm :=
    centralAssembledSlabLabellings_perm_full
      (2 * cutoff) half
  exact hperm.nodup
    (centralAssembledSlabLabellings_nodup
      (2 * cutoff) half)

/-- The orientation-correct Cartesian assembly is a literal permutation of
the full bounded signed-charge carrier. -/
theorem u1AssembledSlabLabellings_perm_full
    (cutoff half : Nat) :
    (u1AssembledSlabLabellings cutoff half).Perm
      (boundedEdgeLabellings (2 * cutoff)
        (slabPhysicalFaceEdges (centralExtent half))) := by
  apply permOfNodupMemIff
  · exact u1AssembledSlabLabellings_nodup cutoff half
  · exact fullU1SlabLabellings_nodup cutoff half
  · intro physical
    exact mem_u1AssembledSlabLabellings_iff

private theorem listQSumPerm {A : Type} (value : A → Q') :
    ∀ {left right : List A}, left.Perm right →
      listQSum value left ≈ listQSum value right
  | _, _, List.Perm.nil => Q'.eqv_refl 0
  | _, _, List.Perm.cons _ hperm =>
      Q'.add_eqv_congr_left _ _ _
        (listQSumPerm value hperm)
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
        (listQSumPerm value hleft)
        (listQSumPerm value hright)

theorem listQSum_u1AssembledSlabLabellings
    (value : ChargeLabelling → Q') (cutoff half : Nat) :
    listQSum value (u1AssembledSlabLabellings cutoff half) ≈
      listQSum value
        (boundedEdgeLabellings (2 * cutoff)
          (slabPhysicalFaceEdges (centralExtent half))) :=
  listQSumPerm value
    (u1AssembledSlabLabellings_perm_full cutoff half)

/-! ## 5. Conditional and all-label physical quadratics coincide -/

/-- The independently defined all-label reflection numerator.  Its upper
argument is the orientation-correct reflected restriction. -/
def u1FullPhysicalReflectionQuadratic
    (D : U1SlabData)
    (coefficient : ChargeLabelling → Q') : Q' :=
  listQSum
    (fun physical =>
      (coefficient (centralLowerRestriction D.half physical) *
        coefficient (u1ReflectedUpperRestriction D.half physical)) *
      D.physicalTerm physical)
    D.states

private def u1TriplePhysicalReflectionTerm
    (D : U1SlabData)
    (coefficient : ChargeLabelling → Q')
    (triple : CentralReflectionTriple) : Q' :=
  (coefficient triple.1 * coefficient triple.2.1) *
    D.physicalTerm
      (assembleU1ReflectionTriple D.half triple)

private theorem u1TriplePhysicalReflectionSum_eq_nested
    (D : U1SlabData)
    (coefficient : ChargeLabelling → Q') :
    listQSum (u1TriplePhysicalReflectionTerm D coefficient)
        (centralReflectionTriples
          (2 * D.chargeCutoff) D.half) ≈
      listQSum
        (fun left =>
          listQSum
            (fun right =>
              listQSum
                (fun boundary =>
                  (coefficient left * coefficient right) *
                    D.physicalTerm
                      (assembleU1ReflectedSlabLabelling D.half
                        left boundary right))
                (u1BoundaryChannels D))
            (u1HalfStates D))
        (u1HalfStates D) := by
  unfold centralReflectionTriples
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap
      (u1TriplePhysicalReflectionTerm D coefficient)
      (fun left =>
        (centralHalfStates (2 * D.chargeCutoff) D.half).flatMap
          (fun right =>
            (centralBoundaryChannels (2 * D.chargeCutoff) D.half).map
              (fun boundary => (left, (right, boundary)))))
      (centralHalfStates (2 * D.chargeCutoff) D.half)) ?_
  apply listQSum_congr
  intro left
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap
      (u1TriplePhysicalReflectionTerm D coefficient)
      (fun right =>
        (centralBoundaryChannels (2 * D.chargeCutoff) D.half).map
          (fun boundary => (left, (right, boundary))))
      (centralHalfStates (2 * D.chargeCutoff) D.half)) ?_
  apply listQSum_congr
  intro right
  rw [listQSum_map]
  exact Q'.eqv_refl _

private theorem u1PhysicalReflectionQuadratic_eq_tripleSum
    (D : U1SlabData)
    (coefficient : ChargeLabelling → Q') :
    u1PhysicalReflectionQuadratic D coefficient ≈
      listQSum (u1TriplePhysicalReflectionTerm D coefficient)
        (centralReflectionTriples
          (2 * D.chargeCutoff) D.half) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        listQSum
          (fun right =>
            listQSum
              (fun boundary =>
                (coefficient left * coefficient right) *
                  D.physicalTerm
                    (assembleU1ReflectedSlabLabelling D.half
                      left boundary right))
              (u1BoundaryChannels D))
          (u1HalfStates D))
      (u1HalfStates D)) _ ?_ ?_
  · unfold u1PhysicalReflectionQuadratic
    apply listQSum_congr
    intro left
    apply listQSum_congr
    intro right
    unfold u1PhysicalReflectedKernel
    exact Q'.eqv_symm
      (listQSum_mul_left
        (coefficient left * coefficient right)
        (fun boundary =>
          D.physicalTerm
            (assembleU1ReflectedSlabLabelling D.half
              left boundary right))
        (u1BoundaryChannels D))
  · exact Q'.eqv_symm
      (u1TriplePhysicalReflectionSum_eq_nested D coefficient)

private theorem listQSumCongrMem {A : Type}
    {left right : A → Q'} :
    ∀ xs : List A, (∀ x, x ∈ xs → left x ≈ right x) →
      listQSum left xs ≈ listQSum right xs
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hagree =>
      Q'.add_eqv_congr'
        (hagree head List.mem_cons_self)
        (listQSumCongrMem tail
          (fun x hx =>
            hagree x (List.mem_cons_of_mem head hx)))

private theorem u1TriplePhysicalReflectionSum_eq_assembled
    (D : U1SlabData)
    (coefficient : ChargeLabelling → Q') :
    listQSum (u1TriplePhysicalReflectionTerm D coefficient)
        (centralReflectionTriples
          (2 * D.chargeCutoff) D.half) ≈
      listQSum
        (fun physical =>
          (coefficient
              (centralLowerRestriction D.half physical) *
            coefficient
              (u1ReflectedUpperRestriction D.half physical)) *
          D.physicalTerm physical)
        (u1AssembledSlabLabellings
          D.chargeCutoff D.half) := by
  unfold u1AssembledSlabLabellings
  rw [listQSum_map]
  apply listQSumCongrMem
  intro triple htriple
  have hparts := mem_centralReflectionTriples.mp htriple
  unfold u1TriplePhysicalReflectionTerm
    assembleU1ReflectionTriple
  rw [centralLowerRestriction_assembleU1 hparts.1,
    u1ReflectedUpperRestriction_assembleU1 hparts.2.1]
  exact Q'.eqv_refl _

private theorem u1States_eq_bounded (D : U1SlabData) :
    D.states =
      boundedEdgeLabellings (2 * D.chargeCutoff)
        (slabPhysicalFaceEdges (centralExtent D.half)) := by
  rfl

/-- Exact equality between the conditionally integrated twisted quadratic
and the independently defined full signed-charge numerator. -/
theorem u1PhysicalReflectionQuadratic_eq_full
    (D : U1SlabData)
    (coefficient : ChargeLabelling → Q') :
    u1PhysicalReflectionQuadratic D coefficient ≈
      u1FullPhysicalReflectionQuadratic D coefficient := by
  refine Q'.eqv_trans _ _ _
    (u1PhysicalReflectionQuadratic_eq_tripleSum
      D coefficient) ?_
  refine Q'.eqv_trans _
    (listQSum
      (fun physical =>
        (coefficient
            (centralLowerRestriction D.half physical) *
          coefficient
            (u1ReflectedUpperRestriction D.half physical)) *
        D.physicalTerm physical)
      (u1AssembledSlabLabellings
        D.chargeCutoff D.half)) _
    (u1TriplePhysicalReflectionSum_eq_assembled
      D coefficient) ?_
  unfold u1FullPhysicalReflectionQuadratic
  rw [u1States_eq_bounded]
  exact listQSum_u1AssembledSlabLabellings
    _ D.chargeCutoff D.half

/-- Constructive all-label reflection positivity for every
charge-conjugation-even lower-half observable. -/
theorem u1FullPhysicalReflectionQuadratic_nonnegative
    (D : U1SlabData)
    (coefficient : ChargeLabelling → Q')
    (heven : ChargeConjugationEvenOn D coefficient) :
    (0 : Q') ≤
      u1FullPhysicalReflectionQuadratic D coefficient := by
  exact Q'.le_trans' _ _ _
    (u1PhysicalReflectionQuadratic_nonnegative
      D coefficient heven)
    (Q'.le_of_eqv
      (u1PhysicalReflectionQuadratic_eq_full
        D coefficient))

/-! ## 6. Normalized all-label law -/

def u1NormalizedFullPhysicalReflectionQuadratic
    (D : U1SlabData)
    (coefficient : ChargeLabelling → Q') : Q' :=
  Q'.divPos
    (u1FullPhysicalReflectionQuadratic D coefficient)
    D.partition D.partition_pos

/-- The same normalized quadratic written directly as an expectation against
`D.normalizedMass` on the pre-existing all-label carrier. -/
def u1FullNormalizedMassReflectionQuadratic
    (D : U1SlabData)
    (coefficient : ChargeLabelling → Q') : Q' :=
  listQSum
    (fun physical =>
      (coefficient (centralLowerRestriction D.half physical) *
        coefficient
          (u1ReflectedUpperRestriction D.half physical)) *
      D.normalizedMass physical)
    D.states

theorem u1FullNormalizedMassReflectionQuadratic_eq_normalized
    (D : U1SlabData)
    (coefficient : ChargeLabelling → Q') :
    u1FullNormalizedMassReflectionQuadratic D coefficient ≈
      u1NormalizedFullPhysicalReflectionQuadratic
        D coefficient := by
  let reciprocal :=
    Q'.recipPos D.partition D.partition_pos
  refine Q'.eqv_trans _
    (listQSum
      (fun physical =>
        ((coefficient
              (centralLowerRestriction D.half physical) *
            coefficient
              (u1ReflectedUpperRestriction D.half physical)) *
          D.physicalTerm physical) * reciprocal)
      D.states) _ ?_ ?_
  · unfold u1FullNormalizedMassReflectionQuadratic
      U1SlabData.normalizedMass Q'.divPos
    apply listQSum_congr_on
    intro physical _
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (coefficient
            (centralLowerRestriction D.half physical) *
          coefficient
            (u1ReflectedUpperRestriction D.half physical))
        (D.physicalTerm physical) reciprocal)
  · refine Q'.eqv_trans _
      (u1FullPhysicalReflectionQuadratic D coefficient *
        reciprocal) _
      (listQSum_mul_right
        (fun physical =>
          (coefficient
              (centralLowerRestriction D.half physical) *
            coefficient
              (u1ReflectedUpperRestriction D.half physical)) *
          D.physicalTerm physical)
        reciprocal D.states) ?_
    unfold u1NormalizedFullPhysicalReflectionQuadratic Q'.divPos
      u1FullPhysicalReflectionQuadratic
    exact Q'.eqv_refl _

theorem u1NormalizedFullPhysicalReflectionQuadratic_nonnegative
    (D : U1SlabData)
    (coefficient : ChargeLabelling → Q')
    (heven : ChargeConjugationEvenOn D coefficient) :
    (0 : Q') ≤
      u1NormalizedFullPhysicalReflectionQuadratic
        D coefficient := by
  unfold u1NormalizedFullPhysicalReflectionQuadratic Q'.divPos
  exact Q'.mul_nonneg _ _
    (u1FullPhysicalReflectionQuadratic_nonnegative
      D coefficient heven)
    (Q'.le_of_lt
      (Q'.recipPos_pos D.partition D.partition_pos))

/-- Reflection positivity in the direct normalized-mass expectation form. -/
theorem u1FullNormalizedMassReflectionQuadratic_nonnegative
    (D : U1SlabData)
    (coefficient : ChargeLabelling → Q')
    (heven : ChargeConjugationEvenOn D coefficient) :
    (0 : Q') ≤
      u1FullNormalizedMassReflectionQuadratic
        D coefficient := by
  exact Q'.le_trans' _ _ _
    (u1NormalizedFullPhysicalReflectionQuadratic_nonnegative
      D coefficient heven)
    (Q'.ge_of_eqv
      (u1FullNormalizedMassReflectionQuadratic_eq_normalized
        D coefficient))

end YMGap.Continuum.BF4U1TwistedPhysicalReindex

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4U1TwistedPhysicalReindex.u1ReflectedUpperRestriction_mem
#print axioms YMGap.Continuum.BF4U1TwistedPhysicalReindex.centralLowerRestriction_assembleU1
#print axioms YMGap.Continuum.BF4U1TwistedPhysicalReindex.centralBoundaryRestriction_assembleU1
#print axioms YMGap.Continuum.BF4U1TwistedPhysicalReindex.u1ReflectedUpperRestriction_assembleU1
#print axioms YMGap.Continuum.BF4U1TwistedPhysicalReindex.assembleU1ReflectedSlabLabelling_restrictions
#print axioms YMGap.Continuum.BF4U1TwistedPhysicalReindex.assembleU1ReflectedSlabLabelling_mem_full
#print axioms YMGap.Continuum.BF4U1TwistedPhysicalReindex.assembleU1ReflectionTriple_injective_on
#print axioms YMGap.Continuum.BF4U1TwistedPhysicalReindex.u1AssembledSlabLabellings_nodup
#print axioms YMGap.Continuum.BF4U1TwistedPhysicalReindex.mem_u1AssembledSlabLabellings_iff
#print axioms YMGap.Continuum.BF4U1TwistedPhysicalReindex.u1AssembledSlabLabellings_perm_full
#print axioms YMGap.Continuum.BF4U1TwistedPhysicalReindex.listQSum_u1AssembledSlabLabellings
#print axioms YMGap.Continuum.BF4U1TwistedPhysicalReindex.u1PhysicalReflectionQuadratic_eq_full
#print axioms YMGap.Continuum.BF4U1TwistedPhysicalReindex.u1FullPhysicalReflectionQuadratic_nonnegative
#print axioms YMGap.Continuum.BF4U1TwistedPhysicalReindex.u1FullNormalizedMassReflectionQuadratic_eq_normalized
#print axioms YMGap.Continuum.BF4U1TwistedPhysicalReindex.u1NormalizedFullPhysicalReflectionQuadratic_nonnegative
#print axioms YMGap.Continuum.BF4U1TwistedPhysicalReindex.u1FullNormalizedMassReflectionQuadratic_nonnegative
