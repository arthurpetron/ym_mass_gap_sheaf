/-
# Exact arbitrary-cutoff partition by excited support

Every bounded physical spin labelling has one literal excited-face support.
Filtering the duplicate-free physical enumeration by those supports therefore
partitions it into duplicate-free, pairwise-disjoint fibers.  This module
turns that statement into an exact rational reindexing: the full physical
spin-foam partition is the sum of the support activities used by the
cutoff-uniform polymer estimates.

This is the normalization bridge needed before the support-level cluster and
cylinder bounds can control the actual arbitrary-cutoff finite-volume model.
-/

import YMGap.Continuum.Z4SpinSummedFaceActivityBound
import YMGap.Continuum.Z4AllSpinLinkSeparatedFamilyFactorization
import YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure

namespace YMGap.Continuum.Z4SpinSummedSupportPartition

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4BoundedEdgeLabellingNodup
open YMGap.Continuum.Z4AllSpinLinkSeparatedFactorization
open YMGap.Continuum.Z4AllSpinLinkSeparatedFamilyFactorization
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The literal disjoint union of all support fibers -/

def parametricKSupportFibers (cutoff n : Nat) : List EdgeLabelling :=
  (cutoffOneFaceSupports n).flatMap
    (physicalLabellingsWithSupport cutoff n)

theorem excitedPlaquetteIds_mem_cutoffOneFaceSupports
    (n : Nat) (physical : EdgeLabelling) :
    excitedPlaquetteIds n physical ∈ cutoffOneFaceSupports n := by
  unfold excitedPlaquetteIds cutoffOneFaceSupports
  exact filter_mem_sublists _ _

theorem mem_parametricKSupportFibers_iff
    {cutoff n : Nat} {physical : EdgeLabelling} :
    physical ∈ parametricKSupportFibers cutoff n ↔
      physical ∈ boundedEdgeLabellings cutoff
        (List.range (plaquetteEdgeCount n)) := by
  constructor
  · intro hphysical
    obtain ⟨support, _, hfiber⟩ := List.mem_flatMap.mp hphysical
    exact (mem_physicalLabellingsWithSupport_iff.mp hfiber).1
  · intro hphysical
    apply List.mem_flatMap.mpr
    refine ⟨excitedPlaquetteIds n physical,
      excitedPlaquetteIds_mem_cutoffOneFaceSupports n physical, ?_⟩
    exact mem_physicalLabellingsWithSupport_iff.mpr
      ⟨hphysical, rfl⟩

private theorem nodup_flatMap_of_disjoint_blocks {A B : Type}
    (block : A → List B) :
    ∀ source : List A,
      source.Nodup →
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
        (List.mem_cons_of_mem head hitem) hne value hhead) hvalueItem

theorem parametricKSupportFibers_nodup (cutoff n : Nat) :
    (parametricKSupportFibers cutoff n).Nodup := by
  unfold parametricKSupportFibers
  apply nodup_flatMap_of_disjoint_blocks
  · exact cutoffOneFaceSupports_nodup n
  · intro support _
    exact physicalLabellingsWithSupport_nodup cutoff n support
  · intro left _ right _ hne physical hleft hright
    have hleftSupport :=
      (mem_physicalLabellingsWithSupport_iff.mp hleft).2
    have hrightSupport :=
      (mem_physicalLabellingsWithSupport_iff.mp hright).2
    exact hne (hleftSupport.symm.trans hrightSupport)

/-! ## 2. Constructive permutation of the physical enumeration -/

private theorem perm_of_nodup_mem_iff_local {A : Type} :
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
      have htailPerm := perm_of_nodup_mem_iff_local
        tail (before ++ after) hleftParts.2 hmiddleParts.2 htailMem
      exact (List.Perm.cons head htailPerm).trans hmiddle

theorem boundedEdgeLabellings_perm_supportFibers (cutoff n : Nat) :
    (boundedEdgeLabellings cutoff
        (List.range (plaquetteEdgeCount n))).Perm
      (parametricKSupportFibers cutoff n) := by
  apply perm_of_nodup_mem_iff_local
  · apply boundedEdgeLabellings_nodup
    simpa [physicalFaceEdges] using physicalFaceEdges_nodup n
  · exact parametricKSupportFibers_nodup cutoff n
  · intro physical
    exact mem_parametricKSupportFibers_iff.symm

/-! ## 3. Exact support-partition normalization -/

def parametricKSupportPartition (cutoff n : Nat) : Q' :=
  listQSum (parametricKSupportActivity cutoff n)
    (cutoffOneFaceSupports n)

/-- The arbitrary-cutoff physical spin-foam partition is exactly the sum of
its unique-support fibers at the derived strong-coupling anchor. -/
theorem parametricKPhysicalPartition_eqv_supportPartition
    (cutoff n : Nat) :
    parametricKPhysicalPartition anchorCoupling cutoff n ≈
      parametricKSupportPartition cutoff n := by
  unfold parametricKPhysicalPartition parametricKSupportPartition
  refine Q'.eqv_trans _ _ _
    (YMGap.Continuum.Z4CanonicalPolymerRange.listQSum_perm _
      (boundedEdgeLabellings_perm_supportFibers cutoff n)) ?_
  unfold parametricKSupportFibers parametricKSupportActivity
  exact listQSum_flatMap _ _ _

theorem parametricKSupportPartition_nonnegative (cutoff n : Nat) :
    (0 : Q') ≤ parametricKSupportPartition cutoff n := by
  unfold parametricKSupportPartition
  exact listQSum_nonnegative _
    (parametricKSupportActivity_nonnegative cutoff n)
    (cutoffOneFaceSupports n)

theorem parametricKPhysicalPartition_one_le (cutoff n : Nat) :
    (1 : Q') ≤
      parametricKPhysicalPartition anchorCoupling cutoff n := by
  unfold parametricKPhysicalPartition
  have hmember := listQSum_member_le
    (parametricKPhysicalTerm anchorCoupling cutoff n)
    (parametricKPhysicalTerm_nonnegative (by decide) cutoff n)
    (boundedEdgeLabellings cutoff
      (List.range (plaquetteEdgeCount n)))
    (zeroEdgeLabelling_mem_bounded cutoff n)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm
      (parametricKPhysicalTerm_zero_eqv_one
        anchorCoupling cutoff n))) hmember

theorem parametricKSupportPartition_one_le (cutoff n : Nat) :
    (1 : Q') ≤ parametricKSupportPartition cutoff n := by
  exact Q'.le_trans' _ _ _
    (parametricKPhysicalPartition_one_le cutoff n)
    (Q'.le_of_eqv
      (parametricKPhysicalPartition_eqv_supportPartition cutoff n))

theorem parametricKSupportPartition_pos (cutoff n : Nat) :
    (0 : Q') < parametricKSupportPartition cutoff n :=
  YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le
    (by decide) (parametricKSupportPartition_one_le cutoff n)

/-! ## 4. Exact normalized events of the full excited support -/

def parametricKSupportEventNumerator (cutoff n : Nat)
    (event : List Nat → Bool) : Q' :=
  listQSum (parametricKSupportActivity cutoff n)
    ((cutoffOneFaceSupports n).filter event)

theorem parametricKSupportEventNumerator_nonnegative
    (cutoff n : Nat) (event : List Nat → Bool) :
    (0 : Q') ≤
      parametricKSupportEventNumerator cutoff n event := by
  unfold parametricKSupportEventNumerator
  exact listQSum_nonnegative _
    (parametricKSupportActivity_nonnegative cutoff n) _

private theorem listQSum_filter_le_local {A : Type}
    (value : A → Q') (test : A → Bool)
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ xs : List A,
      listQSum value (xs.filter test) ≤ listQSum value xs
  | [] => Q'.le_refl' 0
  | head :: tail => by
      have ih := listQSum_filter_le_local value test hvalue tail
      cases htest : test head with
      | false =>
          simp only [List.filter_cons, htest, Bool.false_eq_true,
            ↓reduceIte, listQSum]
          have hmono : listQSum value tail ≤
              value head + listQSum value tail := by
            have hscaled := Q'.add_le_add_right
              (0 : Q') (value head) (listQSum value tail)
              (hvalue head)
            rwa [Q'.zero_add'] at hscaled
          exact Q'.le_trans' _ _ _ ih hmono
      | true =>
          simp only [List.filter_cons, htest, ↓reduceIte, listQSum]
          exact Q'.add_le_add_left (value head) _ _ ih

theorem parametricKSupportEventNumerator_le_partition
    (cutoff n : Nat) (event : List Nat → Bool) :
    parametricKSupportEventNumerator cutoff n event ≤
      parametricKSupportPartition cutoff n := by
  unfold parametricKSupportEventNumerator parametricKSupportPartition
  exact listQSum_filter_le_local
    (parametricKSupportActivity cutoff n) event
    (parametricKSupportActivity_nonnegative cutoff n)
    (cutoffOneFaceSupports n)

def parametricKSupportEventProbability (cutoff n : Nat)
    (event : List Nat → Bool) : Q' :=
  Q'.divPos (parametricKSupportEventNumerator cutoff n event)
    (parametricKSupportPartition cutoff n)
    (parametricKSupportPartition_pos cutoff n)

theorem parametricKSupportEventProbability_nonnegative
    (cutoff n : Nat) (event : List Nat → Bool) :
    (0 : Q') ≤
      parametricKSupportEventProbability cutoff n event := by
  unfold parametricKSupportEventProbability Q'.divPos
  exact Q'.mul_nonneg _ _
    (parametricKSupportEventNumerator_nonnegative cutoff n event)
    (Q'.le_of_lt
      (Q'.recipPos_pos (parametricKSupportPartition cutoff n)
        (parametricKSupportPartition_pos cutoff n)))

theorem parametricKSupportEventProbability_le_one
    (cutoff n : Nat) (event : List Nat → Bool) :
    parametricKSupportEventProbability cutoff n event ≤ (1 : Q') := by
  unfold parametricKSupportEventProbability
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _
    (parametricKSupportEventNumerator_le_partition cutoff n event)
    (Q'.ge_of_eqv
      (Q'.one_mul_eqv (parametricKSupportPartition cutoff n)))

end YMGap.Continuum.Z4SpinSummedSupportPartition

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4SpinSummedSupportPartition.excitedPlaquetteIds_mem_cutoffOneFaceSupports
#print axioms YMGap.Continuum.Z4SpinSummedSupportPartition.parametricKSupportFibers_nodup
#print axioms YMGap.Continuum.Z4SpinSummedSupportPartition.boundedEdgeLabellings_perm_supportFibers
#print axioms YMGap.Continuum.Z4SpinSummedSupportPartition.parametricKPhysicalPartition_eqv_supportPartition
#print axioms YMGap.Continuum.Z4SpinSummedSupportPartition.parametricKSupportPartition_nonnegative
#print axioms YMGap.Continuum.Z4SpinSummedSupportPartition.parametricKSupportPartition_pos
#print axioms YMGap.Continuum.Z4SpinSummedSupportPartition.parametricKSupportEventProbability_nonnegative
#print axioms YMGap.Continuum.Z4SpinSummedSupportPartition.parametricKSupportEventProbability_le_one
