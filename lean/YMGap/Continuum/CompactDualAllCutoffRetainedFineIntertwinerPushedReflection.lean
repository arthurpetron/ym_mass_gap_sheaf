/-
# Reflection invariance of the lossless all-cutoff pushed law

The preceding module proves covariance of each source-to-target row of the
enriched kernel.  This module performs the remaining finite change of
variables in the physical source.  Reflection is an explicit involution on
the proof-bearing attached source carrier, hence it permutes that carrier
without any decidable equality on function-valued labellings.  Exact
reflection invariance of the normalized physical mass and of the enriched
kernel then proves pointwise reflection invariance of the pushed law.

The same constructive permutation argument is recorded for the disjoint
enriched target carrier.  It is the finite reindexing input needed by later
observable and reflection-form identities.

This is an exact finite-volume symmetry theorem.  It does not by itself prove
reflection positivity, a strict form bound, a continuum limit, or the Clay
mass-gap theorem.

## Axiom gate

Finite list recursion, proof irrelevance, and exact rational identities only.
No classical choice, placeholder, trusted external computation,
computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerReflection

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPushedReflection

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerReflection
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalPolymerRange

local infix:50 " ≈ " => Q'.eqv

private theorem nodup_map_of_injective_on {A B : Type} (map : A → B) :
    ∀ (items : List A), items.Nodup →
      (∀ left, left ∈ items → ∀ right, right ∈ items →
        map left = map right → left = right) →
      (items.map map).Nodup
  | [], _, _ => List.nodup_nil
  | head :: tail, hnodup, hinjective => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨item, hitem, heq⟩ := List.mem_map.mp hmem
        have hheadItem := hinjective head List.mem_cons_self item
          (List.mem_cons_of_mem head hitem) heq.symm
        exact hparts.1 (hheadItem ▸ hitem)
      · exact nodup_map_of_injective_on map tail hparts.2
          (fun left hleft right hright =>
            hinjective left (List.mem_cons_of_mem head hleft)
              right (List.mem_cons_of_mem head hright))

private theorem perm_of_nodup_mem_iff {A : Type} :
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
      have hmiddle : (head :: before ++ after).Perm
          (before ++ head :: after) := List.perm_middle.symm
      have hmiddleNodup : (head :: before ++ after).Nodup :=
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
      have htailPerm := perm_of_nodup_mem_iff tail (before ++ after)
        hleftParts.2 hmiddleParts.2 htailMem
      exact (List.Perm.cons head htailPerm).trans hmiddle

/-! ## 1. The physical source change of variables -/

theorem reflectSlabPhysicalSourceEntry_involutive
    (D : SlabPhysicalData) (source : SlabPhysicalSourceEntry D) :
    reflectSlabPhysicalSourceEntry
        (reflectSlabPhysicalSourceEntry source) = source := by
  apply Subtype.ext
  exact slabPhysicalReflectLabelling_involutive_on D source.2

theorem slabPhysicalSourceEntries_reflection_perm
    (D : SlabPhysicalData) :
    ((slabPhysicalSourceEntries D).map
        reflectSlabPhysicalSourceEntry).Perm
      (slabPhysicalSourceEntries D) := by
  let entries := slabPhysicalSourceEntries D
  have hentries : entries.Nodup := slabPhysicalSourceEntries_nodup D
  apply perm_of_nodup_mem_iff
  · apply nodup_map_of_injective_on
      reflectSlabPhysicalSourceEntry entries hentries
    intro left _ right _ heq
    have hinvolutive := congrArg
      (reflectSlabPhysicalSourceEntry (D := D)) heq
    rw [reflectSlabPhysicalSourceEntry_involutive D left,
      reflectSlabPhysicalSourceEntry_involutive D right] at hinvolutive
    exact hinvolutive
  · exact hentries
  · intro source
    constructor
    · intro _
      exact List.mem_attach D.physicalLabellings source
    · intro _
      apply List.mem_map.mpr
      refine ⟨reflectSlabPhysicalSourceEntry source,
        List.mem_attach D.physicalLabellings _, ?_⟩
      exact reflectSlabPhysicalSourceEntry_involutive D source

/-! ## 2. Reflection of the pushed law -/

/-- The normalized physical source law pushed through the complete enriched
kernel is pointwise invariant under enriched target reflection. -/
theorem allCutoffRetainedFineIntertwinerBlockedMass_reflection
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (target : AllCutoffRetainedTarget)
    (htarget : target ∈ allCutoffRetainedTargets S) :
    allCutoffRetainedFineIntertwinerBlockedMass S
        (reflectAllCutoffRetainedTarget S target) ≈
      allCutoffRetainedFineIntertwinerBlockedMass S target := by
  let reflectedWeight : SlabPhysicalSourceEntry S.fine → Q' :=
    fun source =>
      S.fine.normalizedMass source.1 *
        allCutoffRetainedFineIntertwinerKernel S source
          (reflectAllCutoffRetainedTarget S target)
  let sourceWeight : SlabPhysicalSourceEntry S.fine → Q' :=
    fun source =>
      S.fine.normalizedMass source.1 *
        allCutoffRetainedFineIntertwinerKernel S source target
  unfold allCutoffRetainedFineIntertwinerBlockedMass
  change listQSum reflectedWeight (slabPhysicalSourceEntries S.fine) ≈
    listQSum sourceWeight (slabPhysicalSourceEntries S.fine)
  refine Q'.eqv_trans _
    (listQSum reflectedWeight
      ((slabPhysicalSourceEntries S.fine).map
        reflectSlabPhysicalSourceEntry)) _ ?_ ?_
  · exact listQSum_perm reflectedWeight
      (slabPhysicalSourceEntries_reflection_perm S.fine).symm
  · rw [listQSum_map]
    apply listQSum_congr_on _ _ (slabPhysicalSourceEntries S.fine)
    intro source _
    refine Q'.eqv_trans _
      (S.fine.normalizedMass source.1 *
        allCutoffRetainedFineIntertwinerKernel S
          (reflectSlabPhysicalSourceEntry source)
          (reflectAllCutoffRetainedTarget S target)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _
        (S.fine.normalizedMass_reflection source.2)
    · exact Q'.mul_eqv_congr_left _ _ _
        (allCutoffRetainedFineIntertwinerKernel_reflection
          S hfineCutoff source target htarget)

/-! ## 3. The target carrier change of variables -/

theorem allCutoffRetainedTargets_reflection_perm
    (S : SlabScalePair) :
    ((allCutoffRetainedTargets S).map
        (reflectAllCutoffRetainedTarget S)).Perm
      (allCutoffRetainedTargets S) := by
  let targets := allCutoffRetainedTargets S
  have htargets : targets.Nodup := allCutoffRetainedTargets_nodup S
  apply perm_of_nodup_mem_iff
  · apply nodup_map_of_injective_on
      (reflectAllCutoffRetainedTarget S) targets htargets
    intro left hleft right hright heq
    have hinvolutive := congrArg
      (reflectAllCutoffRetainedTarget S) heq
    rw [reflectAllCutoffRetainedTarget_involutive S hleft,
      reflectAllCutoffRetainedTarget_involutive S hright] at hinvolutive
    exact hinvolutive
  · exact htargets
  · intro target
    constructor
    · intro htarget
      obtain ⟨source, hsource, heq⟩ := List.mem_map.mp htarget
      rw [← heq]
      exact reflectAllCutoffRetainedTarget_mem S hsource
    · intro htarget
      apply List.mem_map.mpr
      refine ⟨reflectAllCutoffRetainedTarget S target,
        reflectAllCutoffRetainedTarget_mem S htarget, ?_⟩
      exact reflectAllCutoffRetainedTarget_involutive S htarget

/-! ## Axiom audit -/

#print axioms reflectSlabPhysicalSourceEntry_involutive
#print axioms slabPhysicalSourceEntries_reflection_perm
#print axioms allCutoffRetainedFineIntertwinerBlockedMass_reflection
#print axioms allCutoffRetainedTargets_reflection_perm

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPushedReflection
