/-
# Torus RP (d8a): index facts for the split layout `P ++ C ++ P.map Θ`

With `a = |P| + |C|`:
* `lay_pos`: for `ℓ ∈ P`, `idx ℓ < a` and `idx (Θℓ) = idx ℓ + a`;
* `lay_cross`: for `c ∈ C`, `idx c < a`;
* `lay_mir`: for `ℓ ∈ P`, `a ≤ idx (Θℓ) < a + |P|`.
Only `Nodup` of the layout and injectivity of `Θ` on `P` are used (no `decide`, no classical `idxOf` lemmas).

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPSplitFactor

namespace YMGap.Continuum.SU2TorusRPLayout

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2TorusRPHalfOrder (idxOf_append_nmem)

theorem beq_false_of_ne {x y : Z4Link} (h : y ≠ x) : (y == x) = false := by
  cases hb : (y == x) with
  | false => rfl
  | true => exact absurd (beq_iff_eq.mp hb) h

theorem idxOf_lt (x : Z4Link) : ∀ L : List Z4Link, x ∈ L → L.idxOf x < L.length
  | [], h => absurd h List.not_mem_nil
  | y :: L, h => by
      rw [List.idxOf_cons]
      cases hb : (y == x) with
      | true => show 0 < _; exact Nat.succ_pos _
      | false =>
        show L.idxOf x + 1 < L.length + 1
        have hne : y ≠ x := fun e => by rw [e, beq_iff_eq.mpr rfl] at hb; exact Bool.noConfusion hb
        rcases List.mem_cons.mp h with e | hm
        · exact absurd e.symm hne
        · exact Nat.succ_lt_succ (idxOf_lt x L hm)

theorem idxOf_left (x : Z4Link) : ∀ L1 L2 : List Z4Link, x ∈ L1 → (L1 ++ L2).idxOf x = L1.idxOf x
  | [], _, h => absurd h List.not_mem_nil
  | y :: L1, L2, h => by
      show (y :: (L1 ++ L2)).idxOf x = (y :: L1).idxOf x
      rw [List.idxOf_cons, List.idxOf_cons]
      cases hb : (y == x) with
      | true => rfl
      | false =>
        have hne : y ≠ x := fun e => by rw [e, beq_iff_eq.mpr rfl] at hb; exact Bool.noConfusion hb
        rcases List.mem_cons.mp h with e | hm
        · exact absurd e.symm hne
        · show (L1 ++ L2).idxOf x + 1 = L1.idxOf x + 1
          rw [idxOf_left x L1 L2 hm]

theorem idxOf_map (f : Z4Link → Z4Link) (ℓ : Z4Link) :
    ∀ P : List Z4Link, ℓ ∈ P → (∀ x ∈ P, f x = f ℓ → x = ℓ) → (P.map f).idxOf (f ℓ) = P.idxOf ℓ
  | [], h, _ => absurd h List.not_mem_nil
  | y :: P, h, hinj => by
      show (f y :: P.map f).idxOf (f ℓ) = (y :: P).idxOf ℓ
      rw [List.idxOf_cons, List.idxOf_cons]
      by_cases e : y = ℓ
      · rw [e, beq_iff_eq.mpr rfl, beq_iff_eq.mpr rfl]; rfl
      · have e' : f y ≠ f ℓ := fun h' => e (hinj y (List.mem_cons_self ..) h')
        rw [beq_false_of_ne e, beq_false_of_ne e']
        rcases List.mem_cons.mp h with e2 | hm
        · exact absurd e2.symm e
        · show (P.map f).idxOf (f ℓ) + 1 = P.idxOf ℓ + 1
          rw [idxOf_map f ℓ P hm fun x hx => hinj x (List.mem_cons_of_mem _ hx)]

variable (P C : List Z4Link) (f : Z4Link → Z4Link) (hnd : (P ++ C ++ P.map f).Nodup)
include hnd

theorem lay_pos (ℓ : Z4Link) (hℓ : ℓ ∈ P) (hinj : ∀ x ∈ P, f x = f ℓ → x = ℓ) :
    (P ++ C ++ P.map f).idxOf ℓ < P.length + C.length ∧
      (P ++ C ++ P.map f).idxOf (f ℓ) = (P ++ C ++ P.map f).idxOf ℓ + (P.length + C.length) := by
  have hd := List.nodup_append.mp hnd
  have hfm : f ℓ ∈ P.map f := List.mem_map_of_mem hℓ
  have hnm : f ℓ ∉ P ++ C := fun h => hd.2.2 _ h _ hfm rfl
  rw [idxOf_left ℓ (P ++ C) _ (List.mem_append_left _ hℓ), idxOf_left ℓ P C hℓ,
    idxOf_append_nmem _ (P ++ C) _ hnm, idxOf_map f ℓ P hℓ hinj, List.length_append]
  exact ⟨Nat.lt_of_lt_of_le (idxOf_lt ℓ P hℓ) (Nat.le_add_right _ _), Nat.add_comm _ _⟩

theorem lay_cross (c : Z4Link) (hc : c ∈ C) : (P ++ C ++ P.map f).idxOf c < P.length + C.length := by
  have hd := List.nodup_append.mp hnd
  have hd2 := List.nodup_append.mp hd.1
  have hnP : c ∉ P := fun h => hd2.2.2 _ h _ hc rfl
  rw [idxOf_left c (P ++ C) _ (List.mem_append_right _ hc), idxOf_append_nmem c P C hnP]
  exact Nat.add_lt_add_left (idxOf_lt c C hc) _

end YMGap.Continuum.SU2TorusRPLayout

#print axioms YMGap.Continuum.SU2TorusRPLayout.lay_pos
#print axioms YMGap.Continuum.SU2TorusRPLayout.lay_cross
