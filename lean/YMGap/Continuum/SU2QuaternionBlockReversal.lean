/-
# Exact reversal recodings for a fresh-head heat update

Two explicit involutions reverse either every carried quaternion block or
only the tail after block zero.  Their prefix identities place a fresh block
at the opposite end without identifying it with an existing spectator.
-/

import YMGap.Continuum.SU2QuaternionSpareHeadCopy

namespace YMGap.Continuum.SU2QuaternionBlockReversal

set_option autoImplicit false

open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionSpareHeadCopy
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages

/-- Reverse all blocks of an `n`-block carrier. -/
def reverseBlocks (n : Nat) : QuaternionBlockInvolution n where
  map i := n - 1 - i
  map_lt := by intro i hi; omega
  involutive := by intro i hi; omega

/-- Fix block zero and reverse the remaining tail blocks. -/
def reverseTailBlocks (n : Nat) : QuaternionBlockInvolution n where
  map i := if i = 0 then 0 else n - i
  map_lt := by
    intro i hi
    by_cases h : i = 0
    · simp [h]
      omega
    · simp [h]
      omega
  involutive := by
    intro i hi
    by_cases h : i = 0
    · simp [h]
    · have hn : n - i ≠ 0 := by omega
      simp [h, hn]
      omega

@[simp] theorem reverseBlocks_map_zero (n : Nat) :
    (reverseBlocks n).map 0 = n - 1 := by
  simp [reverseBlocks]

@[simp] theorem reverseBlocks_map_last (n : Nat) :
    (reverseBlocks n).map (n-1) = 0 := by
  simp [reverseBlocks]

@[simp] theorem reverseTailBlocks_map_zero (n : Nat) :
    (reverseTailBlocks n).map 0 = 0 := by
  simp [reverseTailBlocks]

@[simp] theorem reverseTailBlocks_map_one (n : Nat) :
    (reverseTailBlocks (n+1)).map 1 = n := by
  simp [reverseTailBlocks]

@[simp] theorem reverseTailBlocks_map_last (n : Nat) (hn : 0 < n) :
    (reverseTailBlocks (n+1)).map n = 1 := by
  simp [reverseTailBlocks]
  omega

private theorem exponentAt_zero_of_length_le (m : List Nat) (i : Nat)
    (hm : m.length ≤ i) : exponentAt m i = 0 := by
  induction m generalizing i with
  | nil => rfl
  | cons a m ih =>
      cases i with
      | zero => simp at hm
      | succ i =>
          change exponentAt m i = 0
          exact ih i (by simpa using hm)

private theorem exponentAt_four_zeros (m : List Nat) (k : Nat) :
    exponentAt (0::0::0::0::m) (4+k) = exponentAt m k := by
  rw [Nat.add_comm 4 k]
  rfl

private theorem exponentAt_copyMonomial_tail (m : List Nat) (k : Nat) :
    exponentAt (copyMonomial m) (8+k) = exponentAt m (4+k) := by
  unfold copyMonomial
  have h8 := exponentAt_drop
    ([exponentAt m 0, exponentAt m 1, exponentAt m 2, exponentAt m 3,
      0, 0, 0, 0] ++ m.drop 4) 8 k
  have h4 := exponentAt_drop m 4 k
  simpa using h8.symm.trans h4

/-- Reversing the tail after adjoining a head is the lift of full reversal
on the original carrier. -/
theorem reverseTail_lift_prefix (n : Nat) (q : RatPoly) :
    QuaternionPrefixPolynomialEqv (n+1)
      (reindexQuaternionPolynomial (reverseTailBlocks (n+1)) (liftHead q))
      (liftHead (reindexQuaternionPolynomial (reverseBlocks n) q)) := by
  induction q with
  | nil => exact .nil
  | cons t ts ih =>
      apply QuaternionPrefixPolynomialEqv.cons
      · refine ⟨Q'.eqv_refl _, ?_⟩
        intro j hj
        change exponentAt
            (reindexQuaternionExponents (reverseTailBlocks (n+1))
              (0::0::0::0::t.1)) j =
          exponentAt (0::0::0::0::
            reindexQuaternionExponents (reverseBlocks n) t.1) j
        rw [exponentAt_reindexQuaternionExponents _ _ hj]
        by_cases hj0 : j < 4
        · have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
          rcases h with rfl | rfl | rfl | rfl <;> rfl
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hj0)
          have hk : k < 4*n := by omega
          have hb : (4+k)/4 = k/4+1 := by omega
          have hr : (4+k)%4 = k%4 := by omega
          rw [hb, hr]
          have hne : k/4+1 ≠ 0 := by omega
          simp only [reverseTailBlocks, hne, if_false]
          rw [show n+1-(k/4+1)=n-k/4 by omega]
          rw [show 4*(n-k/4)+k%4 = 4+(4*(n-1-k/4)+k%4) by omega]
          simp only [exponentAt_four_zeros]
          rw [exponentAt_reindexQuaternionExponents (reverseBlocks n) t.1 hk]
          rfl
      · exact ih

/-- On an `n`-supported source, tail reversal in the enlarged carrier inserts
the unused block one exactly as `copy` does. -/
theorem reverseTail_source_copy_prefix (n : Nat) (hn : 0 < n)
    (p : RatPoly) (hp : SupportedQuaternionBlocks n p) :
    QuaternionPrefixPolynomialEqv (n+1)
      (reindexQuaternionPolynomial (reverseTailBlocks (n+1)) p)
      (copy (reindexQuaternionPolynomial (reverseTailBlocks n) p)) := by
  induction p with
  | nil => exact .nil
  | cons t ts ih =>
      have ht := hp t List.mem_cons_self
      apply QuaternionPrefixPolynomialEqv.cons
      · refine ⟨Q'.eqv_refl _, ?_⟩
        intro j hj
        change exponentAt
            (reindexQuaternionExponents (reverseTailBlocks (n+1)) t.1) j =
          exponentAt (copyMonomial
            (reindexQuaternionExponents (reverseTailBlocks n) t.1)) j
        rw [exponentAt_reindexQuaternionExponents _ _ hj]
        by_cases hj4 : j < 4
        · rw [copyMonomial_head _ hj4,
            exponentAt_reindexQuaternionExponents _ _ (by omega : j < 4*n)]
          have hd : j / 4 = 0 := by omega
          simp only [hd, reverseTailBlocks_map_zero]
        · by_cases hj8 : j < 8
          · have h : j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
            rcases h with rfl | rfl | rfl | rfl <;>
              simp [reverseTailBlocks, copyMonomial] <;>
              exact exponentAt_zero_of_length_le t.1 _ (by omega)
          · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hj8)
            have hk : 4+k < 4*n := by omega
            rw [show (8+k)/4=k/4+2 by omega, show (8+k)%4=k%4 by omega]
            have hne : k/4+2 ≠ 0 := by omega
            rw [exponentAt_copyMonomial_tail]
            rw [exponentAt_reindexQuaternionExponents (reverseTailBlocks n) t.1 hk]
            rw [show (4+k)/4=k/4+1 by omega, show (4+k)%4=k%4 by omega]
            have hk0 : k/4+1 ≠ 0 := by omega
            simp only [reverseTailBlocks, hne, hk0, if_false]
            congr 1
            omega
      · exact ih (fun s hs => hp s (List.mem_cons_of_mem t hs))

end YMGap.Continuum.SU2QuaternionBlockReversal

#print axioms YMGap.Continuum.SU2QuaternionBlockReversal.reverseBlocks
#print axioms YMGap.Continuum.SU2QuaternionBlockReversal.reverseTailBlocks
#print axioms YMGap.Continuum.SU2QuaternionBlockReversal.reverseTail_lift_prefix
#print axioms YMGap.Continuum.SU2QuaternionBlockReversal.reverseTail_source_copy_prefix
