/-
# All positive ORIGINAL discrete times have the same kernel

Symmetry identifies <T_n x,T_n x> with <x,T_(2n) x>. Positive definiteness
therefore makes the kernels of T_(2n) and T_n equal. The semigroup law
then propagates a later zero backward, proving ker T_n = ker T_1 for every
n>=1. No spectral theorem, inverse, classical choice or positivity premise
for T_1 is needed. The operator is the existing completed geometric time.

This does NOT prove that this common kernel is zero on the whole completion.
It does prove no further annihilation on any positive-time range, a useful
distinction for subsequent positive-time reconstruction.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime

namespace YMGap.Continuum.BF4ExactSlabThermodynamicTimeKernel

set_option autoImplicit false

open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPosdef
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime

theorem time_double_zero_iff (n : Nat) (x : Completion) :
    completedTime (n+n) x=completedZero ↔ completedTime n x=completedZero := by
  constructor
  · intro h
    apply (completedInner_posdef _).mp
    rw [completedTime_moments,h,completedInner_zero_right]
  · intro h
    rw [← completedTime_comp,h,completedTime_zeroState]

theorem time_zero_predecessor (n : Nat) (hn : 1 ≤ n) (x : Completion)
    (h : completedTime (n+1) x=completedZero) : completedTime n x=completedZero := by
  have hlater := congrArg (completedTime (n-1)) h
  rw [completedTime_comp,completedTime_zeroState] at hlater
  have he : n+1+(n-1)=n+n := by omega
  rw [he] at hlater
  exact (time_double_zero_iff n x).mp hlater

theorem time_succ_zero_iff_one : ∀ n : Nat, ∀ x : Completion,
    completedTime (n+1) x=completedZero ↔ completedTime 1 x=completedZero
  | 0, _ => Iff.rfl
  | n+1, x => by
    constructor
    · intro h
      exact (time_succ_zero_iff_one n x).mp (time_zero_predecessor (n+1) (by omega) x h)
    · intro h
      have hlater := congrArg (completedTime (n+1)) h
      rw [completedTime_comp,completedTime_zeroState] at hlater
      simpa only [Nat.add_comm 1 (n+1)] using hlater

theorem time_positive_zero_iff_one (n : Nat) (hn : 0<n) (x : Completion) :
    completedTime n x=completedZero ↔ completedTime 1 x=completedZero := by
  cases n with
  | zero => exact False.elim ((Nat.lt_irrefl 0) hn)
  | succ n => exact time_succ_zero_iff_one n x

theorem time_positive_kernel_equal (s t : Nat) (hs : 0<s) (ht : 0<t) (x : Completion) :
    completedTime s x=completedZero ↔ completedTime t x=completedZero :=
  (time_positive_zero_iff_one s hs x).trans (time_positive_zero_iff_one t ht x).symm

theorem even_form_zero_iff_one (n : Nat) (hn : 0<n) (x : Completion) :
    completedInner x (completedTime (n+n) x)=RCzero ↔ completedTime 1 x=completedZero := by
  rw [← completedTime_moments]
  exact (completedInner_posdef _).trans (time_positive_zero_iff_one n hn x)

theorem positive_range_no_further_kernel (s t : Nat) (hs : 0<s) (x : Completion) :
    completedTime t (completedTime s x)=completedZero ↔ completedTime s x=completedZero := by
  rw [completedTime_comp]
  exact time_positive_kernel_equal (s+t) s (by omega) hs x

end YMGap.Continuum.BF4ExactSlabThermodynamicTimeKernel

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeKernel.time_double_zero_iff
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeKernel.time_zero_predecessor
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeKernel.time_succ_zero_iff_one
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeKernel.time_positive_zero_iff_one
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeKernel.time_positive_kernel_equal
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeKernel.even_form_zero_iff_one
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeKernel.positive_range_no_further_kernel
