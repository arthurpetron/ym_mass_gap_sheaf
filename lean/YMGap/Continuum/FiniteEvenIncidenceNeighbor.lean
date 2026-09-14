/-
# Even incidence has a distinct, computably selected companion

Vertices are occurrence identities, not their possibly repeated projections.
In a duplicate-free finite list, an even incidence count cannot have exactly
one contributing vertex. The output is the first distinct contributing
vertex, retained as Type-level data. No connectivity or counting bound for
the whole family is assumed or concluded.
-/

import YMGap.Continuum.CayleyPruferInjection

namespace YMGap.Continuum.FiniteEvenIncidenceNeighbor

set_option autoImplicit false

open YMGap.Continuum.CayleyPruferInjection

def neighbor {A : Type} [DecidableEq A] (vertices : List A) (hit : A → Bool)
    (hn : vertices.Nodup) (x : A) (hx : x ∈ vertices) (hh : hit x = true)
    (heven : (vertices.filter hit).length % 2 = 0) :
    Σ' y : A, y ∈ vertices ∧ y ≠ x ∧ hit y = true := by
  cases he : vertices.filter (fun y => decide (y ≠ x) && hit y) with
  | nil =>
    have hsub : ∀ y, y ∈ vertices.filter hit → y ∈ [x] := by
      intro y hy
      have hp := List.mem_filter.mp hy
      apply List.mem_singleton.mpr
      by_cases hyx : y = x
      · exact hyx
      · have hm : y ∈ vertices.filter (fun z => decide (z ≠ x) && hit z) :=
          List.mem_filter.mpr ⟨hp.1, by simp only [hyx, ne_eq, not_false_eq_true,
            decide_true, Bool.true_and, hp.2]⟩
        rw [he] at hm
        exact False.elim (List.not_mem_nil hm)
    have hle := nodup_subset_length_le (vertices.filter hit) [x] (hn.filter hit) hsub
    have hpos : 0 < (vertices.filter hit).length := by
      have hm := List.mem_filter.mpr ⟨hx, hh⟩
      cases hf : vertices.filter hit with
      | nil => rw [hf] at hm; exact False.elim (List.not_mem_nil hm)
      | cons a rest => simp only [List.length_cons]; omega
    simp only [List.length_cons, List.length_nil] at hle
    exact False.elim (by omega)
  | cons y rest =>
    have hm : y ∈ vertices.filter (fun z => decide (z ≠ x) && hit z) :=
      he ▸ List.mem_cons_self
    have hp := List.mem_filter.mp hm
    have hb := Bool.and_eq_true_iff.mp hp.2
    exact ⟨y, hp.1, of_decide_eq_true hb.1, hb.2⟩

end YMGap.Continuum.FiniteEvenIncidenceNeighbor

#print axioms YMGap.Continuum.FiniteEvenIncidenceNeighbor.neighbor
