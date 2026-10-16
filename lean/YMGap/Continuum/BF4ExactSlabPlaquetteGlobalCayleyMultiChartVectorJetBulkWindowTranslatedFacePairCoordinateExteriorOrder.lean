/-
# Canonical omitted-face order for the translated selected action

The complete physical target-face order is filtered by nonmembership in the
zero-placement translated selected action.  The resulting omitted list is
duplicate-free, physical, disjoint from the selected IDs, and appending it to
the selected IDs gives a permutation of the complete target action.

This is only the finite ordering input for the sequential covariance
telescope.  No response bound, geometric sum, volume limit, continuum
Hamiltonian, or mass gap is proved here.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorMargin

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorOrder

set_option autoImplicit false

open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair
open YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding
open YMGap.Continuum.BF4ExactSlabTranslatedSelectedAction
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private theorem rangeNodupLocal : ∀ length : Nat, (List.range length).Nodup
  | 0 => List.nodup_nil
  | length + 1 => by
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨rangeNodupLocal length,
          List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hrightEq : right = length := List.mem_singleton.mp hright
      rw [heq, hrightEq] at hleft
      exact (Nat.lt_irrefl length) (List.mem_range.mp hleft)

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
      obtain ⟨before, after, hsplit⟩ := List.append_of_mem hheadRight
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
      have htailPerm := permOfNodupMemIff
        tail (before ++ after) hleftParts.2 hmiddleParts.2 htailMem
      exact (List.Perm.cons head htailPerm).trans hmiddle

/-- The translated selected IDs are duplicate-free. -/
theorem zeroPlacement_selectedIds_nodup
    (s n L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target) :
    (selectedIds (zeroPlacement s n L target hroom)
      (originalBulkVectorQuadraticJetIds s n L)).Nodup := by
  let P := zeroPlacement s n L target hroom
  unfold selectedIds
  apply YMGap.Continuum.CayleyPruferInjection.nodup_map_of_injOn
    P.faceId (originalBulkVectorQuadraticJetIds s n L)
  · unfold originalBulkVectorQuadraticJetIds
      originalBulkScalarSquareRemainderIds
    exact chainIds_nodup _ _ _ _
  · intro left hleft right hright heq
    exact P.faceId_injective
      (originalBulkVectorQuadraticJetIds_physical s n L left hleft)
      (originalBulkVectorQuadraticJetIds_physical s n L right hright)
      heq

/-- Canonical omitted target faces, retaining the complete physical target
order. -/
def zeroPlacementExteriorIds
    (s n L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target) : List Nat :=
  (slabPhysicalFaceEdges target).filter fun id =>
    decide (id ∉ selectedIds (zeroPlacement s n L target hroom)
      (originalBulkVectorQuadraticJetIds s n L))

theorem zeroPlacementExteriorIds_mem_iff
    (s n L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target)
    (id : Nat) :
    id ∈ zeroPlacementExteriorIds s n L target hroom ↔
      id ∈ slabPhysicalFaceEdges target ∧
        id ∉ selectedIds (zeroPlacement s n L target hroom)
          (originalBulkVectorQuadraticJetIds s n L) := by
  simp [zeroPlacementExteriorIds]

theorem zeroPlacementExteriorIds_physical
    (s n L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target) :
    ∀ id, id ∈ zeroPlacementExteriorIds s n L target hroom →
      id ∈ slabPhysicalFaceEdges target := by
  intro id hid
  exact (zeroPlacementExteriorIds_mem_iff
    s n L target hroom id).mp hid |>.1

theorem zeroPlacementExteriorIds_omitted
    (s n L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target) :
    ∀ id, id ∈ zeroPlacementExteriorIds s n L target hroom →
      id ∉ selectedIds (zeroPlacement s n L target hroom)
        (originalBulkVectorQuadraticJetIds s n L) := by
  intro id hid
  exact (zeroPlacementExteriorIds_mem_iff
    s n L target hroom id).mp hid |>.2

theorem zeroPlacementExteriorIds_nodup
    (s n L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target) :
    (zeroPlacementExteriorIds s n L target hroom).Nodup := by
  unfold zeroPlacementExteriorIds slabPhysicalFaceEdges
  exact List.filter_sublist.nodup (rangeNodupLocal _)

/-- Selected and omitted IDs are disjoint and duplicate-free when appended. -/
theorem zeroPlacement_selected_append_exterior_nodup
    (s n L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target) :
    (selectedIds (zeroPlacement s n L target hroom)
        (originalBulkVectorQuadraticJetIds s n L) ++
      zeroPlacementExteriorIds s n L target hroom).Nodup := by
  refine List.nodup_append.mpr
    ⟨zeroPlacement_selectedIds_nodup s n L target hroom,
      zeroPlacementExteriorIds_nodup s n L target hroom, ?_⟩
  intro selected hselected omitted homitted heq
  subst omitted
  exact (zeroPlacementExteriorIds_omitted
    s n L target hroom selected homitted) hselected

/-- The chosen order is complete: translated selected IDs followed by the
canonical omitted complement are a permutation of the full target action. -/
theorem zeroPlacement_selected_append_exterior_perm_full
    (s n L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target) :
    (selectedIds (zeroPlacement s n L target hroom)
        (originalBulkVectorQuadraticJetIds s n L) ++
      zeroPlacementExteriorIds s n L target hroom).Perm
        (slabPhysicalFaceEdges target) := by
  apply permOfNodupMemIff
  · exact zeroPlacement_selected_append_exterior_nodup
      s n L target hroom
  · unfold slabPhysicalFaceEdges
    exact rangeNodupLocal _
  · intro id
    constructor
    · intro hid
      rcases List.mem_append.mp hid with hselected | hexterior
      · exact selectedIds_physical
          (zeroPlacement s n L target hroom)
          (originalBulkVectorQuadraticJetIds s n L)
          (originalBulkVectorQuadraticJetIds_physical_at_placement
            (zeroPlacement s n L target hroom) s n L rfl)
          id hselected
      · exact zeroPlacementExteriorIds_physical
          s n L target hroom id hexterior
    · intro hphysical
      by_cases hselected :
          id ∈ selectedIds (zeroPlacement s n L target hroom)
            (originalBulkVectorQuadraticJetIds s n L)
      · exact List.mem_append.mpr (Or.inl hselected)
      · exact List.mem_append.mpr (Or.inr
          ((zeroPlacementExteriorIds_mem_iff
            s n L target hroom id).mpr ⟨hphysical, hselected⟩))

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorOrder

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorOrder.zeroPlacement_selectedIds_nodup
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorOrder.zeroPlacementExteriorIds_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorOrder.zeroPlacementExteriorIds_nodup
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorOrder.zeroPlacement_selected_append_exterior_nodup
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorOrder.zeroPlacement_selected_append_exterior_perm_full
