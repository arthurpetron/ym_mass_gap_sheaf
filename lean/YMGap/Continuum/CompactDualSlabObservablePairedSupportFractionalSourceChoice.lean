/-
# Duplicate-free dependent paired-support source choices

Each separated paired-support source carries the duplicate-free target list of
its physical-only whole-slab recoupling matrix.  Tagging every target by its
source turns the source-dependent family into one ordinary finite list.  The
tags make different source blocks disjoint, so the flattened list is also
duplicate free.

This is the finite carrier on which a concrete-target preimage can be taken
without losing multiplicity information.

Constructive contract: structural finite lists and dependent records only;
no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRow
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetNodup

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalSourceChoice

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRow
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetNodup

/-! ## 1. One ordinary carrier for a dependent family -/

abbrev SlabObservablePairedSupportRecouplingSourceChoice
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :=
  Sigma fun source : SlabObservablePairedSupportSeparatedSource
    D rootFaceId targetFaceId =>
      SlabObservablePairedSupportRecouplingChoice
        D rootFaceId targetFaceId source

def slabObservablePairedSupportRecouplingSourceChoiceBlock
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId) :
    List (SlabObservablePairedSupportRecouplingSourceChoice
      D rootFaceId targetFaceId) :=
  (slabObservablePairedSupportRecouplingChoices
    D rootFaceId targetFaceId source).map fun choice =>
      ⟨source, choice⟩

def slabObservablePairedSupportRecouplingSourceChoices
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    List (SlabObservablePairedSupportRecouplingSourceChoice
      D rootFaceId targetFaceId) :=
  (slabObservablePairedSupportSeparatedSources
    D rootFaceId targetFaceId).flatMap fun source =>
      slabObservablePairedSupportRecouplingSourceChoiceBlock
        D rootFaceId targetFaceId source

/-! ## 2. Duplicate freedom -/

private theorem nodup_map_of_injective {A B : Type} (map : A → B)
    (hinjective : ∀ left right, map left = map right → left = right) :
    ∀ {items : List A}, items.Nodup → (items.map map).Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hitems => by
      have hparts := List.nodup_cons.mp hitems
      refine List.nodup_cons.mpr
        ⟨?_, nodup_map_of_injective map hinjective hparts.2⟩
      intro hmem
      obtain ⟨item, hitem, heq⟩ := List.mem_map.mp hmem
      exact hparts.1 ((hinjective head item heq.symm) ▸ hitem)

theorem slabObservablePairedSupportRecouplingChoices_nodup
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId) :
    (slabObservablePairedSupportRecouplingChoices
      D rootFaceId targetFaceId source).Nodup := by
  exact slabPhysicalPairRecouplingKernel_targets_nodup
    D.extent
    _ _

theorem slabObservablePairedSupportRecouplingSourceChoiceBlock_nodup
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedSupportSeparatedSource
      D rootFaceId targetFaceId) :
    (slabObservablePairedSupportRecouplingSourceChoiceBlock
      D rootFaceId targetFaceId source).Nodup := by
  unfold slabObservablePairedSupportRecouplingSourceChoiceBlock
  apply nodup_map_of_injective
  · intro left right heq
    apply eq_of_heq
    cases heq
    rfl
  · exact slabObservablePairedSupportRecouplingChoices_nodup
      D rootFaceId targetFaceId source

private theorem nodup_flatMap_of_disjoint_blocks {A B : Type}
    (block : A → List B) :
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
      have hvalueTail : value ∈ tail.flatMap block := heq ▸ htail
      obtain ⟨item, hitem, hvalueItem⟩ :=
        List.mem_flatMap.mp hvalueTail
      have hne : head ≠ item := by
        intro hsame
        subst item
        exact hparts.1 hitem
      exact (hdisjoint head List.mem_cons_self item
        (List.mem_cons_of_mem head hitem) hne value hhead) hvalueItem

theorem slabObservablePairedSupportRecouplingSourceChoices_nodup
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    (slabObservablePairedSupportRecouplingSourceChoices
      D rootFaceId targetFaceId).Nodup := by
  unfold slabObservablePairedSupportRecouplingSourceChoices
  apply nodup_flatMap_of_disjoint_blocks
  · exact slabObservablePairedSupportSeparatedSources_nodup
      D rootFaceId targetFaceId
  · intro source _
    exact slabObservablePairedSupportRecouplingSourceChoiceBlock_nodup
      D rootFaceId targetFaceId source
  · intro left _ right _ hne value hleft hright
    obtain ⟨leftChoice, _, rfl⟩ := List.mem_map.mp hleft
    obtain ⟨rightChoice, _, heq⟩ := List.mem_map.mp hright
    exact hne (congrArg
      (fun item : SlabObservablePairedSupportRecouplingSourceChoice
        D rootFaceId targetFaceId => item.1)
      heq.symm)

end YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalSourceChoice

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalSourceChoice.slabObservablePairedSupportRecouplingChoices_nodup
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalSourceChoice.slabObservablePairedSupportRecouplingSourceChoiceBlock_nodup
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalSourceChoice.slabObservablePairedSupportRecouplingSourceChoices_nodup
