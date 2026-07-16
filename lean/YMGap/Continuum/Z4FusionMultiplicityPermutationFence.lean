/-
# A finite-cutoff fence for fusion-path permutation invariance

Left-associated SU(2) fusion is permutation invariant only after the
auxiliary channel window contains every channel that can occur.  This file
banks a small obstruction to an incorrectly stated theorem at an arbitrary
cutoff.  At cutoff two, the paired order has two paths while the interleaved
order loses the spin-three intermediate channel and has only one.  All four
external spins are nevertheless bounded by the cutoff.

The production finite-box formula uses the larger auxiliary cutoff `6*K`.
Consequently this fence does not obstruct the physical theorem; it records
why that theorem must retain its external-spin bound and fusion-complete
auxiliary window.
-/

import YMGap.Continuum.Z4FusionPathZeroInsertion

namespace YMGap.Continuum.Z4FusionMultiplicityPermutationFence

open YMGap.Continuum.Z4FusionPathZeroInsertion

theorem paired_order_cutoff_two :
    fusionPathMultiplicity 2 [1, 1, 2, 2] = 2 := by
  decide

theorem interleaved_order_cutoff_two :
    fusionPathMultiplicity 2 [1, 2, 1, 2] = 1 := by
  decide

theorem paired_interleaved_perm :
    [1, 1, 2, 2].Perm [1, 2, 1, 2] := by
  apply List.Perm.cons 1
  exact List.Perm.swap 2 1 [2]

theorem paired_order_bounded :
    SpinsBounded 2 [1, 1, 2, 2] := by
  intro spin hspin
  simp only [List.mem_cons] at hspin
  rcases hspin with rfl | rfl | rfl | rfl | hfalse
  · omega
  · omega
  · omega
  · omega
  · simp only [List.not_mem_nil] at hfalse

theorem interleaved_order_bounded :
    SpinsBounded 2 [1, 2, 1, 2] := by
  intro spin hspin
  simp only [List.mem_cons] at hspin
  rcases hspin with rfl | rfl | rfl | rfl | hfalse
  · omega
  · omega
  · omega
  · omega
  · simp only [List.not_mem_nil] at hfalse

/-- **Machine-checked truncation fence.** There is no theorem asserting
permutation invariance of `fusionPathMultiplicity` for every auxiliary
cutoff, even for four external spins. -/
theorem arbitrary_cutoff_permutation_invariance_false :
    ∃ cutoff : Nat, ∃ left right : List Nat,
      SpinsBounded cutoff left ∧ SpinsBounded cutoff right ∧
        left.Perm right ∧
        fusionPathMultiplicity cutoff left ≠
          fusionPathMultiplicity cutoff right := by
  exact ⟨2, [1, 1, 2, 2], [1, 2, 1, 2],
    paired_order_bounded, interleaved_order_bounded,
    paired_interleaved_perm, by
      rw [paired_order_cutoff_two, interleaved_order_cutoff_two]
      decide⟩

end YMGap.Continuum.Z4FusionMultiplicityPermutationFence

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4FusionMultiplicityPermutationFence.paired_order_cutoff_two
#print axioms YMGap.Continuum.Z4FusionMultiplicityPermutationFence.interleaved_order_cutoff_two
#print axioms YMGap.Continuum.Z4FusionMultiplicityPermutationFence.paired_interleaved_perm
#print axioms YMGap.Continuum.Z4FusionMultiplicityPermutationFence.paired_order_bounded
#print axioms YMGap.Continuum.Z4FusionMultiplicityPermutationFence.interleaved_order_bounded
#print axioms YMGap.Continuum.Z4FusionMultiplicityPermutationFence.arbitrary_cutoff_permutation_invariance_false
