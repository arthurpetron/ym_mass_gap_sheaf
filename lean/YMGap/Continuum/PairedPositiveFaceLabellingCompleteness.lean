/-
# Every bounded pair with exactly the selected support is enumerated

The witness is the given pair itself. At each selected head, its two
labels choose the existing positive-pair branch; resetting the head to
zero constructs the tail. No search oracle or equality test on functions
is used, and the original enumeration is unchanged.
-/

import YMGap.Continuum.PairedPositiveFaceLabellings

namespace YMGap.Continuum.PairedPositiveFaceLabellingCompleteness

set_option autoImplicit false

open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.PairedPositiveFaceLabellings

theorem positivePairs_complete {K : Nat} (spins : Nat × Nat)
    (hb : spins.1 ≤ K ∧ spins.2 ≤ K) (hp : 0 < spins.1 ∨ 0 < spins.2) :
    spins ∈ positivePairs K := by
  rcases spins with ⟨a,b⟩
  cases a with
  | zero =>
    cases b with
    | zero => rcases hp with h | h <;> exact False.elim (Nat.lt_irrefl 0 h)
    | succ b =>
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
        (List.mem_map.mpr ⟨b,List.mem_range.mpr (by omega),rfl⟩))))
  | succ a =>
    cases b with
    | zero =>
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
        (List.mem_map.mpr ⟨a,List.mem_range.mpr (by omega),rfl⟩))))
    | succ b =>
      exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
        ⟨a,List.mem_range.mpr (by omega),List.mem_map.mpr
          ⟨b,List.mem_range.mpr (by omega),rfl⟩⟩))

theorem setPair_restore (pair : EdgeLabelling × EdgeLabelling) (id : Nat) :
    setPair (setPair pair id (0,0)) id (pair.1 id,pair.2 id) = pair := by
  apply Prod.ext
  all_goals
    funext i
    by_cases hi : i = id
    · subst i
      simp only [setPair,setEdgeLabel,↓reduceIte]
    · simp only [setPair,setEdgeLabel,if_neg hi]

theorem labels_complete (K : Nat) : ∀ (ids : List Nat) (pair : EdgeLabelling × EdgeLabelling),
    ids.Nodup →
    (∀ id, id ∈ ids → pair.1 id ≤ K ∧ pair.2 id ≤ K) →
    (∀ id, id ∈ ids → 0 < pair.1 id ∨ 0 < pair.2 id) →
    (∀ id, id ∉ ids → pair.1 id = 0 ∧ pair.2 id = 0) → pair ∈ labels K ids
  | [], pair, _, _, _, hz => by
      apply List.mem_singleton.mpr
      exact Prod.ext (funext (fun id => (hz id List.not_mem_nil).1))
        (funext (fun id => (hz id List.not_mem_nil).2))
  | id::ids, pair, hn, hb, hp, hz => by
      have ht := List.nodup_cons.mp hn
      have hne (i : Nat) (hi : i ∈ ids) : i ≠ id := by
        intro he
        exact ht.1 (he ▸ hi)
      have htail : setPair pair id (0,0) ∈ labels K ids :=
        labels_complete K ids (setPair pair id (0,0)) ht.2
          (fun i hi => by
            simpa only [setPair,setEdgeLabel,if_neg (hne i hi)] using hb i (List.mem_cons_of_mem id hi))
          (fun i hi => by
            simpa only [setPair,setEdgeLabel,if_neg (hne i hi)] using hp i (List.mem_cons_of_mem id hi))
          (fun i hi => by
            by_cases he : i = id
            · subst i
              exact ⟨by simp [setPair,setEdgeLabel],by simp [setPair,setEdgeLabel]⟩
            · simpa only [setPair,setEdgeLabel,if_neg he] using
                hz i (fun hm => (List.mem_cons.mp hm).elim he hi))
      exact List.mem_flatMap.mpr ⟨(pair.1 id,pair.2 id),
        positivePairs_complete _ (hb id List.mem_cons_self) (hp id List.mem_cons_self),
        List.mem_map.mpr ⟨setPair pair id (0,0),htail,setPair_restore pair id⟩⟩

end YMGap.Continuum.PairedPositiveFaceLabellingCompleteness

#print axioms YMGap.Continuum.PairedPositiveFaceLabellingCompleteness.positivePairs_complete
#print axioms YMGap.Continuum.PairedPositiveFaceLabellingCompleteness.setPair_restore
#print axioms YMGap.Continuum.PairedPositiveFaceLabellingCompleteness.labels_complete
