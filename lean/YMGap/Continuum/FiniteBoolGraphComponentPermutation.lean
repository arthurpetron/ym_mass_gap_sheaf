/-
# The finite component forest preserves the entire input list up to permutation

Exact mass alone is not a license to discard duplicates. This permutation
theorem shows that the component algorithm moves each occurrence exactly
once. In particular, duplicate-free input gives duplicate-free flattened
components and duplicate-free individual components, without erasing data.
-/

import YMGap.Continuum.FiniteBoolGraphComponentMass

namespace YMGap.Continuum.FiniteBoolGraphComponentPermutation

set_option autoImplicit false

open YMGap.Continuum.FiniteBoolGraphComponents

theorem gather_keep_perm {A : Type} (adj : A → A → Bool) (x : A) : ∀ cs : List (List A),
    ((gatherTouched adj x cs)++(keepUntouched adj x cs).flatten).Perm (x::cs.flatten)
  | [] => List.Perm.refl _
  | c::cs => by
    have ih := gather_keep_perm adj x cs
    by_cases ht : touchesB adj x c=true
    · simp only [gatherTouched,keepUntouched,ht,↓reduceIte,List.flatten_cons,List.append_assoc]
      exact (ih.append_left c).trans List.perm_middle
    · simp only [gatherTouched,keepUntouched,ht,Bool.false_eq_true,↓reduceIte,List.flatten_cons]
      exact (List.perm_append_comm_assoc _ _ _).trans ((ih.append_left c).trans List.perm_middle)

theorem graph_flatten_perm {A : Type} (adj : A → A → Bool) : ∀ vertices : List A,
    (graphComponents adj vertices).flatten.Perm vertices
  | [] => List.Perm.refl _
  | x::xs => by
    change ((gatherTouched adj x (graphComponents adj xs))++
      (keepUntouched adj x (graphComponents adj xs)).flatten).Perm (x::xs)
    exact (gather_keep_perm adj x _).trans ((graph_flatten_perm adj xs).cons x)

theorem graph_flatten_nodup {A : Type} (adj : A → A → Bool) (vertices : List A)
    (hn : vertices.Nodup) : (graphComponents adj vertices).flatten.Nodup :=
  (graph_flatten_perm adj vertices).symm.nodup hn

theorem member_nodup_of_flatten {A : Type} : ∀ cs : List (List A), cs.flatten.Nodup →
    ∀ c, c ∈ cs → c.Nodup
  | [], _, _, hc => False.elim (List.not_mem_nil hc)
  | head::rest, hn, c, hc => by
    have hp := List.nodup_append.mp hn
    rcases List.mem_cons.mp hc with he | ht
    · exact he ▸ hp.1
    · exact member_nodup_of_flatten rest hp.2.1 c ht

theorem graph_component_nodup {A : Type} (adj : A → A → Bool) (vertices : List A)
    (hn : vertices.Nodup) (c : List A) (hc : c ∈ graphComponents adj vertices) : c.Nodup :=
  member_nodup_of_flatten _ (graph_flatten_nodup adj vertices hn) c hc

end YMGap.Continuum.FiniteBoolGraphComponentPermutation

#print axioms YMGap.Continuum.FiniteBoolGraphComponentPermutation.gather_keep_perm
#print axioms YMGap.Continuum.FiniteBoolGraphComponentPermutation.graph_flatten_perm
#print axioms YMGap.Continuum.FiniteBoolGraphComponentPermutation.graph_flatten_nodup
#print axioms YMGap.Continuum.FiniteBoolGraphComponentPermutation.member_nodup_of_flatten
#print axioms YMGap.Continuum.FiniteBoolGraphComponentPermutation.graph_component_nodup
