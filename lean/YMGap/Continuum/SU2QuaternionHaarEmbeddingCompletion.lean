/-
# Complete an injective coordinate placement without losing spectators

Keep the prescribed source coordinates first, then append every unused
target coordinate. The result is a full carrier permutation preserving
Haar, and its initial block map is exactly the original embedding.
-/

import YMGap.Continuum.SU2QuaternionHaarBlockEmbeddingAlgebra

namespace YMGap.Continuum.SU2QuaternionHaarEmbeddingCompletion

set_option autoImplicit false

open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection

variable {source target : Nat} (E : BlockEmbedding source target)

def completeOrder : List Nat :=
  E.image ++ (quaternionBlockOrder target).filter (fun b => decide (b ∉ E.image))

theorem completeOrder_nodup : (completeOrder E).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨E.nodup, List.filter_sublist.nodup (quaternionBlockOrder_nodup target), ?_⟩
  intro a ha b hb he
  exact (of_decide_eq_true (List.mem_filter.mp hb).2) (he ▸ ha)

theorem completeOrder_mem (b : Nat) : b ∈ completeOrder E ↔ b < target := by
  constructor
  · intro hb
    rcases List.mem_append.mp hb with hb | hb
    · exact E.physical b hb
    · exact (mem_quaternionBlockOrder_iff _ _).mp (List.mem_filter.mp hb).1
  · intro hb
    by_cases hi : b ∈ E.image
    · exact List.mem_append.mpr (Or.inl hi)
    · exact List.mem_append.mpr (Or.inr (List.mem_filter.mpr
        ⟨(mem_quaternionBlockOrder_iff _ _).mpr hb, decide_eq_true hi⟩))

theorem completeOrder_perm : (completeOrder E).Perm (quaternionBlockOrder target) :=
  perm_of_nodup_mem_iff _ _ (completeOrder_nodup E) (quaternionBlockOrder_nodup target)
    (fun b => (completeOrder_mem E b).trans (mem_quaternionBlockOrder_iff b target).symm)

private theorem order_length : ∀ n, (quaternionBlockOrder n).length = n
  | 0 => rfl
  | n+1 => by simp only [quaternionBlockOrder, List.length_cons, List.length_map, order_length n]

theorem completeOrder_length : (completeOrder E).length = target :=
  (completeOrder_perm E).length_eq.trans (order_length target)

def complete : BlockEmbedding target target where
  image := completeOrder E
  length := completeOrder_length E
  nodup := completeOrder_nodup E
  physical := fun b hb => (completeOrder_mem E b).mp hb

private theorem getD_append_left {A : Type} (xs ys : List A) (fallback : A) :
    ∀ i, i < xs.length → (xs++ys).getD i fallback = xs.getD i fallback := by
  induction xs with
  | nil => intro i hi; simp at hi
  | cons a xs ih =>
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact ih i (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi)

theorem complete_block {i : Nat} (hi : i < source) : (complete E).block i = E.block i :=
  getD_append_left E.image _ 0 i (by rw [E.length]; exact hi)

include E in
theorem source_le_target : source ≤ target := by
  have h := completeOrder_length E
  unfold completeOrder at h
  rw [List.length_append, E.length] at h
  omega

end YMGap.Continuum.SU2QuaternionHaarEmbeddingCompletion

#print axioms YMGap.Continuum.SU2QuaternionHaarEmbeddingCompletion.completeOrder
#print axioms YMGap.Continuum.SU2QuaternionHaarEmbeddingCompletion.completeOrder_nodup
#print axioms YMGap.Continuum.SU2QuaternionHaarEmbeddingCompletion.completeOrder_mem
#print axioms YMGap.Continuum.SU2QuaternionHaarEmbeddingCompletion.completeOrder_perm
#print axioms YMGap.Continuum.SU2QuaternionHaarEmbeddingCompletion.completeOrder_length
#print axioms YMGap.Continuum.SU2QuaternionHaarEmbeddingCompletion.complete
#print axioms YMGap.Continuum.SU2QuaternionHaarEmbeddingCompletion.complete_block
#print axioms YMGap.Continuum.SU2QuaternionHaarEmbeddingCompletion.source_le_target
