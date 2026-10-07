/-
# Torus RP (d9r): Classical-free permutation from Nodup + equal membership

`perm_ext'`: two nodup lists with the same members are permutations of each other (own erase lemmas; the core
`List.perm_cons_erase` / `Nodup.mem_erase_iff` use `Classical.choice`).

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

namespace YMGap.Continuum.SU2TorusRPPermExt

set_option autoImplicit false
variable {α : Type} [DecidableEq α]
theorem erase_eq_of_eq (a : α) (l : List α) : (a :: l).erase a = l := by
  rw [List.erase_cons, if_pos (beq_iff_eq.mpr rfl)]
theorem erase_ne {a b : α} (h : b ≠ a) (l : List α) : (b :: l).erase a = b :: l.erase a := by
  rw [List.erase_cons, if_neg (fun e => h (beq_iff_eq.mp e))]
theorem perm_cons_erase' (a : α) : ∀ l : List α, a ∈ l → l.Perm (a :: l.erase a)
  | [], h => absurd h List.not_mem_nil
  | b :: l, h => by
    rcases decEq b a with e | e
    · rw [erase_ne e]
      have ha : a ∈ l := by
        rcases List.mem_cons.mp h with h' | h'
        · exact absurd h'.symm e
        · exact h'
      exact ((perm_cons_erase' a l ha).cons b).trans (List.Perm.swap a b _)
    · subst e; rw [erase_eq_of_eq]
theorem mem_erase_ne' {a x : α} (hx : x ≠ a) : ∀ l : List α, x ∈ l → x ∈ l.erase a
  | [], h => absurd h List.not_mem_nil
  | b :: l, h => by
    rcases decEq b a with e | e
    · rw [erase_ne e]
      rcases List.mem_cons.mp h with h' | h'
      · subst h'; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (mem_erase_ne' hx l h')
    · subst e; rw [erase_eq_of_eq]
      rcases List.mem_cons.mp h with h' | h'
      · exact absurd h' hx
      · exact h'
theorem not_mem_erase' (a : α) : ∀ l : List α, l.Nodup → a ∉ l.erase a
  | [], _, h => by simp at h
  | b :: l, hn, h => by
    rcases decEq b a with e | e
    · rw [erase_ne e] at h
      rcases List.mem_cons.mp h with h' | h'
      · exact e h'.symm
      · exact not_mem_erase' a l (List.nodup_cons.mp hn).2 h'
    · subst e; rw [erase_eq_of_eq] at h; exact (List.nodup_cons.mp hn).1 h
theorem perm_ext' : ∀ (l1 l2 : List α), l1.Nodup → l2.Nodup →
    (∀ x, x ∈ l1 ↔ x ∈ l2) → l1.Perm l2
  | [], l2, _, _, h => by
    cases l2 with
    | nil => exact List.Perm.refl _
    | cons b l2 => exact absurd ((h b).mpr (List.mem_cons_self ..)) List.not_mem_nil
  | a :: l1, l2, h1, h2, h => by
    have ha : a ∈ l2 := (h a).mp (List.mem_cons_self ..)
    refine List.Perm.trans ?_ (perm_cons_erase' a l2 ha).symm
    refine List.Perm.cons a (perm_ext' l1 (l2.erase a) (List.nodup_cons.mp h1).2 (h2.erase a) fun x => ?_)
    constructor
    · intro hx
      exact mem_erase_ne' (fun (e : x = a) => (List.nodup_cons.mp h1).1 (e ▸ hx)) l2 ((h x).mp (List.mem_cons_of_mem _ hx))
    · intro hx
      have hx2 := List.mem_of_mem_erase hx
      rcases List.mem_cons.mp ((h x).mpr hx2) with e | hx'
      · subst e; exact absurd hx (not_mem_erase' _ l2 h2)
      · exact hx'
end YMGap.Continuum.SU2TorusRPPermExt

#print axioms YMGap.Continuum.SU2TorusRPPermExt.perm_ext'
