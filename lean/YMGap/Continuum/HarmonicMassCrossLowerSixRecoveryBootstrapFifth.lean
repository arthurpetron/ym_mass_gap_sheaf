/-
# Fifth exact cumulative lower-six recovery tranche

This is the next independently replayable exact-rational bridge block between
the finite recovery anchor and the uniform symbolic production tail.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapFourth

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapFifth

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapFourth
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixActual
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixReserveDeficit
open YMGap.Continuum.HarmonicMassCrossLowerSixTerminalPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixTwoSidedWindow
open YMGap.Continuum.HarmonicMassCrossResidualSandwich

/-- First replay-sized quarter of the exact fifth bootstrap tranche. -/
theorem lowerSixRecoveryPayment_bootstrap_448_472 : ∀ i : Fin 25,
    -lowerSixWindowPrefix (i.val + 448) ≤
      lowerSixRecoveryReserve (i.val + 448) := by
  decide

/-- Second replay-sized quarter of the exact fifth bootstrap tranche. -/
theorem lowerSixRecoveryPayment_bootstrap_473_497 : ∀ i : Fin 25,
    -lowerSixWindowPrefix (i.val + 473) ≤
      lowerSixRecoveryReserve (i.val + 473) := by
  decide

/-- First half of the exact fifth bootstrap tranche, assembled from two
25-case certificates so neither kernel reduction reaches the memory cap. -/
theorem lowerSixRecoveryPayment_bootstrap_448_497 : ∀ i : Fin 50,
    -lowerSixWindowPrefix (i.val + 448) ≤
      lowerSixRecoveryReserve (i.val + 448) := by
  intro i
  by_cases hi : i.val < 25
  · let j : Fin 25 := ⟨i.val, hi⟩
    exact lowerSixRecoveryPayment_bootstrap_448_472 j
  · let j : Fin 25 := ⟨i.val - 25, by omega⟩
    have h := lowerSixRecoveryPayment_bootstrap_473_497 j
    have hidx : i.val - 25 + 473 = i.val + 448 := by omega
    simpa [j, hidx] using h

/-- Second replay-sized half of the exact fifth bootstrap tranche. -/
theorem lowerSixRecoveryPayment_bootstrap_498_547 : ∀ i : Fin 50,
    -lowerSixWindowPrefix (i.val + 498) ≤
      lowerSixRecoveryReserve (i.val + 498) := by
  decide

/-- Exact fifth bootstrap tranche, assembled without re-running one
monolithic 100-case kernel reduction. -/
theorem lowerSixRecoveryPayment_bootstrap_448_547 : ∀ i : Fin 100,
    -lowerSixWindowPrefix (i.val + 448) ≤
      lowerSixRecoveryReserve (i.val + 448) := by
  intro i
  by_cases hi : i.val < 50
  · let j : Fin 50 := ⟨i.val, hi⟩
    exact lowerSixRecoveryPayment_bootstrap_448_497 j
  · let j : Fin 50 := ⟨i.val - 50, by omega⟩
    have h := lowerSixRecoveryPayment_bootstrap_498_547 j
    have hidx : i.val - 50 + 498 = i.val + 448 := by omega
    simpa [j, hidx] using h

theorem lowerSixRecoveryPayment_448_547
    {k : Nat} (hk0 : 448 ≤ k) (hk1 : k < 548) :
    -lowerSixWindowPrefix k ≤ lowerSixRecoveryReserve k := by
  let i : Fin 100 := ⟨k - 448, by omega⟩
  have h := lowerSixRecoveryPayment_bootstrap_448_547 i
  have hkidx : k - 448 + 448 = k := by omega
  simpa [i, hkidx] using h

theorem growingResidualLowerSix_448_547
    {k : Nat} (hk0 : 448 ≤ k) (hk1 : k < 548) :
    GrowingResidualLowerSix k := by
  apply growingResidualLowerSix_of_interior_nonnegative (by omega)
  exact lowerSixInterior_nonnegative_of_recovery_payment_actual (by omega)
    (lowerSixRecoveryPayment_448_547 hk0 hk1)

theorem growingResidualLowerSix_below_fiveFortyEight
    {k : Nat} (hk0 : 10 ≤ k) (hk1 : k < 548) :
    GrowingResidualLowerSix k := by
  by_cases hk448 : 448 ≤ k
  · exact growingResidualLowerSix_448_547 hk448 hk1
  · exact growingResidualLowerSix_below_fourFortyEight hk0 (by omega)

#print axioms lowerSixRecoveryPayment_bootstrap_448_472
#print axioms lowerSixRecoveryPayment_bootstrap_473_497
#print axioms lowerSixRecoveryPayment_bootstrap_448_497
#print axioms lowerSixRecoveryPayment_bootstrap_498_547
#print axioms lowerSixRecoveryPayment_bootstrap_448_547
#print axioms lowerSixRecoveryPayment_448_547
#print axioms growingResidualLowerSix_448_547
#print axioms growingResidualLowerSix_below_fiveFortyEight

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapFifth
