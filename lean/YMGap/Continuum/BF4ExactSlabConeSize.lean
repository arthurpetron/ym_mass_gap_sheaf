/-
# Uniform cardinality budget for literal Ward-star cones

Each literal star has at most 25 links. Consequently an r-step deduplicated
cone has at most 25^r times the initial support size, independently of the
ambient slab extent. This is a finite combinatorial budget only; it is not a
decay estimate.
-/

import YMGap.Continuum.BF4ExactSlabEightLayerCone

namespace YMGap.Continuum.BF4ExactSlabConeSize

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabWardStarGeometry

private theorem eraseDups_length_le_local {A : Type} [BEq A]
    (xs : List A) : xs.eraseDups.length ≤ xs.length := by
  cases xs with
  | nil => simp
  | cons head tail =>
      rw [List.eraseDups_cons]
      simp only [List.length_cons]
      have hfilter := List.length_filter_le
        (fun item : A => !item == head) tail
      have ih := eraseDups_length_le_local
        (tail.filter fun item => !item == head)
      omega
termination_by xs.length
decreasing_by
  simp_wf
  omega

private theorem flatMap_length_le {A B : Type} (f : A → List B) (C : Nat) :
    ∀ xs : List A, (∀ x, x ∈ xs → (f x).length ≤ C) →
      (xs.flatMap f).length ≤ xs.length * C
  | [], _ => by simp
  | x :: xs, h => by
      have hx := h x List.mem_cons_self
      have ht := flatMap_length_le f C xs
        (fun y hy => h y (List.mem_cons_of_mem x hy))
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        Nat.add_mul, Nat.one_mul]
      omega

/-- One deduplicated expansion multiplies literal support size by at most 25.
The bound is uniform in the slab extent. -/
theorem expand_length_le (extent : Nat) (support : List Z4Link) :
    (expand extent support).length ≤ 25 * support.length := by
  unfold expand
  apply Nat.le_trans (eraseDups_length_le_local _)
  simpa only [Nat.mul_comm] using
    flatMap_length_le (starLinks extent) 25 support
      (fun link _ => starLinks_length_le_25 extent link)

/-- An r-step literal Ward-star cone has size at most 25^r times its initial
support size, uniformly in the slab extent. -/
theorem grow_length_le (extent r : Nat) (support : List Z4Link) :
    (grow extent r support).length ≤ 25^r * support.length := by
  induction r generalizing support with
  | zero => simp [grow]
  | succ r ih =>
      rw [grow]
      calc
        (grow extent r (expand extent support)).length ≤
            25^r * (expand extent support).length :=
          ih (expand extent support)
        _ ≤ 25^r * (25 * support.length) :=
          Nat.mul_le_mul_left _ (expand_length_le extent support)
        _ = 25^(r+1) * support.length := by
          simp [Nat.pow_succ, Nat.mul_assoc]

#print axioms expand_length_le
#print axioms grow_length_le

end YMGap.Continuum.BF4ExactSlabConeSize
