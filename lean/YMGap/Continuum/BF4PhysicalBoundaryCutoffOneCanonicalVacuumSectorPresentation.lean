/-
# Multiplicity-preserving cutoff-one canonical-sector presentation

The cutoff-one canonical vacuum sector has already been identified by
membership with the displayed vacuum/cube block.  For normalized sums one
also needs multiplicity control.  This module proves constructively that the
state list obtained from the canonical finite index component is nodup and is
a permutation of `[vacuum, central cube]`.  Consequently every rational sum
over the canonical state presentation can be transported to the two-state
presentation without choosing representatives.

This is finite cutoff one only.  No cutoff-uniform or continuum assertion is
made.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorRefresh

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorPresentation

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSector
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem nodup_map_of_injective_on_local
    {A B : Type} (map : A → B) :
    ∀ (items : List A), items.Nodup →
      (∀ left, left ∈ items → ∀ right, right ∈ items →
        map left = map right → left = right) →
      (items.map map).Nodup
  | [], _, _ => List.nodup_nil
  | head :: tail, hnodup, hinjective => by
      have hparts := List.nodup_cons.mp hnodup
      refine List.nodup_cons.mpr ⟨?_,
        nodup_map_of_injective_on_local map tail hparts.2
          (fun left hleft right hright =>
            hinjective left (List.mem_cons_of_mem head hleft)
              right (List.mem_cons_of_mem head hright))⟩
      intro hmem
      rcases List.mem_map.mp hmem with ⟨other, hother, hmap⟩
      have heq := hinjective head List.mem_cons_self other
        (List.mem_cons_of_mem head hother) hmap.symm
      exact hparts.1 (heq ▸ hother)

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
      have htailPerm := perm_of_nodup_mem_iff_local
        tail (before ++ after) hleftParts.2 hmiddleParts.2 htailMem
      exact (List.Perm.cons head htailPerm).trans hmiddle

private theorem listQSum_perm_local {A : Type}
    (value : A → Q') {left right : List A}
    (hperm : left.Perm right) :
    listQSum value left ≈ listQSum value right := by
  induction hperm with
  | nil => exact Q'.eqv_refl 0
  | cons head _ ih =>
      exact Q'.add_eqv_congr' (Q'.eqv_refl (value head)) ih
  | swap left right tail =>
      exact Q'.eqv_trans _
        ((value right + value left) + listQSum value tail) _
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
        (Q'.eqv_trans _
          ((value left + value right) + listQSum value tail) _
          (Q'.add_eqv_congr_right _ _ _
            (Q'.add_comm_eqv _ _))
          (Q'.add_assoc_eqv _ _ _))
  | trans _ _ ihLeft ihRight =>
      exact Q'.eqv_trans _ _ _ ihLeft ihRight

private theorem centralPhysicalFiniteStateAt_injective_on_sector_local
    {w : Q'} {hw : (0 : Q') ≤ w} {K half left right : Nat}
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half)
    (hstate : centralPhysicalFiniteStateAt w hw K half left =
      centralPhysicalFiniteStateAt w hw K half right) :
    left = right := by
  have hleftLt := centralPhysicalFiniteVacuumSectorIndex_lt
    w hw K half hleft
  have hrightLt := centralPhysicalFiniteVacuumSectorIndex_lt
    w hw K half hright
  let states := centralPositiveHalfStates w hw K half
  have hoptions : states[left]? = states[right]? := by
    rw [List.getElem?_eq_getElem hleftLt,
      List.getElem?_eq_getElem hrightLt]
    apply congrArg some
    change states.getD left zeroEdgeLabelling =
      states.getD right zeroEdgeLabelling at hstate
    rw [← List.getElem_eq_getD
        (l := states) (i := left) (h := hleftLt) zeroEdgeLabelling,
      ← List.getElem_eq_getD
        (l := states) (i := right) (h := hrightLt) zeroEdgeLabelling]
      at hstate
    exact hstate
  exact List.getElem?_inj hleftLt
    (centralPositiveHalfStates_nodup w hw K half) hoptions

/-! ## 1. Multiplicity control -/

theorem centralPhysicalFiniteVacuumSectorStates_cutoffOne_nodup
    {w : Q'} (hw : (0 : Q') < w) :
    (centralPhysicalFiniteVacuumSectorStates
      w (Q'.le_of_lt hw) 1 0).Nodup := by
  unfold centralPhysicalFiniteVacuumSectorStates
  apply nodup_map_of_injective_on_local
  · exact centralPhysicalFiniteVacuumSectorIndices_nodup
      w (Q'.le_of_lt hw) 1 0
  · intro left hleft right hright hstate
    exact centralPhysicalFiniteStateAt_injective_on_sector_local
      hleft hright hstate

theorem cutoffOneVacuumCubePhysicalSources_nodup :
    cutoffOneVacuumCubePhysicalSources.Nodup := by
  simp only [cutoffOneVacuumCubePhysicalSources, List.nodup_cons,
    List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨
    Ne.symm
      YMGap.Continuum.BF4CentralLowerCubePositiveRow.centralLowerCubeState_ne_zero,
    (fun h => h), List.nodup_nil⟩

/-! ## 2. Exact permutation and sum transport -/

theorem centralPhysicalFiniteVacuumSectorStates_cutoffOne_perm
    {w : Q'} (hw : (0 : Q') < w) :
    (centralPhysicalFiniteVacuumSectorStates
        w (Q'.le_of_lt hw) 1 0).Perm
      cutoffOneVacuumCubePhysicalSources := by
  apply perm_of_nodup_mem_iff_local
  · exact centralPhysicalFiniteVacuumSectorStates_cutoffOne_nodup hw
  · exact cutoffOneVacuumCubePhysicalSources_nodup
  · exact centralPhysicalFiniteVacuumSectorStates_cutoffOne_iff hw

/-- Every rational sum over the mapped canonical index presentation is the
same sum over the explicit vacuum/cube presentation. -/
theorem centralPhysicalFiniteVacuumSectorStates_cutoffOne_sum_eqv
    {w : Q'} (hw : (0 : Q') < w)
    (value : EdgeLabelling → Q') :
    listQSum value
        (centralPhysicalFiniteVacuumSectorStates
          w (Q'.le_of_lt hw) 1 0) ≈
      listQSum value cutoffOneVacuumCubePhysicalSources := by
  exact listQSum_perm_local value
    (centralPhysicalFiniteVacuumSectorStates_cutoffOne_perm hw)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorPresentation

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorPresentation.centralPhysicalFiniteVacuumSectorStates_cutoffOne_nodup
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorPresentation.cutoffOneVacuumCubePhysicalSources_nodup
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorPresentation.centralPhysicalFiniteVacuumSectorStates_cutoffOne_perm
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorPresentation.centralPhysicalFiniteVacuumSectorStates_cutoffOne_sum_eqv
