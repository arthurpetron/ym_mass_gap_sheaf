/-
# Exact multiplicity of the parallel residual allocator

An occurrence mask with `k` available bits has exactly `2^k` submasks.  This
module derives that count using a recursive, duplicate-free enumeration and
identifies it with the filtered enumeration used by the residual allocator.
Consequently the emitted target-code block has exactly the same cardinality.
-/

import YMGap.Continuum.XiExceptionalParallelResidualBlock

namespace YMGap.Continuum.XiExceptionalParallelSubmaskCount

open YMGap.Continuum.PolymerModel
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalParallelExternalFamily
open YMGap.Continuum.XiExceptionalParallelSubmaskBlock
open YMGap.Continuum.XiExceptionalParallelResidualBlock

variable {L : Lattice} [DecidableEq L.Plaquette]

def occurrenceBitCount : OccBitVec n → Nat
  | .nil => 0
  | .cons false tail => occurrenceBitCount tail
  | .cons true tail => occurrenceBitCount tail + 1

/-- Canonical recursive enumeration of all occurrence submasks. -/
def occurrenceSubmasks : OccBitVec n → List (OccBitVec n)
  | .nil => [.nil]
  | .cons false tail =>
      (occurrenceSubmasks tail).map
        (XiExceptionalOccurrenceCodes.BitVec.cons false)
  | .cons true tail =>
      (occurrenceSubmasks tail).map
          (XiExceptionalOccurrenceCodes.BitVec.cons false) ++
        (occurrenceSubmasks tail).map
          (XiExceptionalOccurrenceCodes.BitVec.cons true)

theorem mem_occurrenceSubmasks_iff : ∀ {n : Nat}
    (big small : OccBitVec n),
    small ∈ occurrenceSubmasks big ↔ occurrenceSubmaskB small big = true
  | 0, .nil, .nil => by simp [occurrenceSubmasks, occurrenceSubmaskB]
  | _ + 1, .cons false bigTail, .cons false smallTail => by
      simp [occurrenceSubmasks, occurrenceSubmaskB,
        mem_occurrenceSubmasks_iff bigTail smallTail]
  | _ + 1, .cons false bigTail, .cons true smallTail => by
      simp [occurrenceSubmasks, occurrenceSubmaskB]
  | _ + 1, .cons true bigTail, .cons false smallTail => by
      simp [occurrenceSubmasks, occurrenceSubmaskB,
        mem_occurrenceSubmasks_iff bigTail smallTail]
  | _ + 1, .cons true bigTail, .cons true smallTail => by
      simp [occurrenceSubmasks, occurrenceSubmaskB,
        mem_occurrenceSubmasks_iff bigTail smallTail]

theorem occurrenceSubmasks_nodup : ∀ {n : Nat} (big : OccBitVec n),
    (occurrenceSubmasks big).Nodup
  | 0, .nil => List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | _ + 1, .cons false tail =>
      nodup_map_of_injOn (XiExceptionalOccurrenceCodes.BitVec.cons false)
        (occurrenceSubmasks tail)
        (occurrenceSubmasks_nodup tail)
        (fun _ _ _ _ h => by injection h)
  | _ + 1, .cons true tail => by
      have ih := occurrenceSubmasks_nodup tail
      have hfalse :
          ((occurrenceSubmasks tail).map
            (XiExceptionalOccurrenceCodes.BitVec.cons false)).Nodup :=
        nodup_map_of_injOn
          (XiExceptionalOccurrenceCodes.BitVec.cons false)
          (occurrenceSubmasks tail) ih
          (fun _ _ _ _ h => by injection h)
      have htrue :
          ((occurrenceSubmasks tail).map
            (XiExceptionalOccurrenceCodes.BitVec.cons true)).Nodup :=
        nodup_map_of_injOn
          (XiExceptionalOccurrenceCodes.BitVec.cons true)
          (occurrenceSubmasks tail) ih
          (fun _ _ _ _ h => by injection h)
      apply List.nodup_append.mpr
      refine ⟨hfalse, htrue, ?_⟩
      intro x hx y hy hxy
      obtain ⟨u, _, hux⟩ := List.mem_map.mp hx
      obtain ⟨v, _, hvy⟩ := List.mem_map.mp hy
      rw [← hux, ← hvy] at hxy
      injection hxy with _ hhead _
      exact Bool.false_ne_true hhead

theorem occurrenceSubmasks_length : ∀ {n : Nat} (big : OccBitVec n),
    (occurrenceSubmasks big).length = 2 ^ occurrenceBitCount big
  | 0, .nil => rfl
  | _ + 1, .cons false tail => by
      simp [occurrenceSubmasks, occurrenceBitCount,
        occurrenceSubmasks_length tail]
  | _ + 1, .cons true tail => by
      simp [occurrenceSubmasks, occurrenceBitCount,
        occurrenceSubmasks_length tail, Nat.pow_succ]
      omega

private theorem filter_false_map_big_false (big : OccBitVec n) :
    ∀ xs : List (OccBitVec n),
    (xs.map (XiExceptionalOccurrenceCodes.BitVec.cons false)).filter
        (fun small => occurrenceSubmaskB small
          (XiExceptionalOccurrenceCodes.BitVec.cons false big)) =
      (xs.filter (fun small => occurrenceSubmaskB small big)).map
        (XiExceptionalOccurrenceCodes.BitVec.cons false)
  | [] => rfl
  | x :: xs => by
      cases hx : occurrenceSubmaskB x big <;>
        simp [occurrenceSubmaskB, hx, filter_false_map_big_false big xs]

private theorem filter_true_map_big_false (big : OccBitVec n) :
    ∀ xs : List (OccBitVec n),
    (xs.map (XiExceptionalOccurrenceCodes.BitVec.cons true)).filter
        (fun small => occurrenceSubmaskB small
          (XiExceptionalOccurrenceCodes.BitVec.cons false big)) = []
  | [] => rfl
  | _ :: xs => by
      simp [occurrenceSubmaskB, filter_true_map_big_false big xs]

private theorem filter_false_map_big_true (big : OccBitVec n) :
    ∀ xs : List (OccBitVec n),
    (xs.map (XiExceptionalOccurrenceCodes.BitVec.cons false)).filter
        (fun small => occurrenceSubmaskB small
          (XiExceptionalOccurrenceCodes.BitVec.cons true big)) =
      (xs.filter (fun small => occurrenceSubmaskB small big)).map
        (XiExceptionalOccurrenceCodes.BitVec.cons false)
  | [] => rfl
  | x :: xs => by
      cases hx : occurrenceSubmaskB x big <;>
        simp [occurrenceSubmaskB, hx, filter_false_map_big_true big xs]

private theorem filter_true_map_big_true (big : OccBitVec n) :
    ∀ xs : List (OccBitVec n),
    (xs.map (XiExceptionalOccurrenceCodes.BitVec.cons true)).filter
        (fun small => occurrenceSubmaskB small
          (XiExceptionalOccurrenceCodes.BitVec.cons true big)) =
      (xs.filter (fun small => occurrenceSubmaskB small big)).map
        (XiExceptionalOccurrenceCodes.BitVec.cons true)
  | [] => rfl
  | x :: xs => by
      cases hx : occurrenceSubmaskB x big <;>
        simp [occurrenceSubmaskB, hx, filter_true_map_big_true big xs]

/-- The recursive enumeration agrees exactly, including order, with filtering
the complete bit-vector enumeration by the Boolean submask test. -/
theorem occurrenceSubmasks_eq_filter : ∀ {n : Nat} (big : OccBitVec n),
    occurrenceSubmasks big =
      (bitVectors n).filter (fun small => occurrenceSubmaskB small big)
  | 0, .nil => rfl
  | _ + 1, .cons false tail => by
      rw [occurrenceSubmasks, bitVectors, List.filter_append]
      rw [filter_false_map_big_false, filter_true_map_big_false]
      simp only [List.append_nil]
      rw [occurrenceSubmasks_eq_filter tail]
  | _ + 1, .cons true tail => by
      rw [occurrenceSubmasks, bitVectors, List.filter_append]
      rw [filter_false_map_big_true, filter_true_map_big_true]
      rw [occurrenceSubmasks_eq_filter tail]

theorem rightResidualExternalMasks_length
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (rightResidualExternalMasks Gamma qP b1 b2 entry).length =
      2 ^ occurrenceBitCount (rightPathResidual Gamma qP b1 b2 entry) := by
  unfold rightResidualExternalMasks
  rw [← occurrenceSubmasks_eq_filter]
  exact occurrenceSubmasks_length _

/-- Exact emitted-code multiplicity: injection loses no residual submask. -/
theorem rightResidualParallelCodes_length
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (rightResidualParallelCodes Gamma qP b1 b2 entry).length =
      2 ^ occurrenceBitCount (rightPathResidual Gamma qP b1 b2 entry) := by
  unfold rightResidualParallelCodes parallelExternalBlock
  rw [List.length_map]
  exact rightResidualExternalMasks_length Gamma qP b1 b2 entry

#print axioms mem_occurrenceSubmasks_iff
#print axioms occurrenceSubmasks_nodup
#print axioms occurrenceSubmasks_length
#print axioms occurrenceSubmasks_eq_filter
#print axioms rightResidualExternalMasks_length
#print axioms rightResidualParallelCodes_length

end YMGap.Continuum.XiExceptionalParallelSubmaskCount
