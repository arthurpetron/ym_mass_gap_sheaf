/-
# Fourth exact cumulative lower-six recovery tranche

This is the next independently replayable exact-rational bridge block between
the finite recovery anchor and the uniform symbolic production tail.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapThird

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapFourth

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapThird
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixActual
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixReserveDeficit
open YMGap.Continuum.HarmonicMassCrossLowerSixTerminalPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixTwoSidedWindow
open YMGap.Continuum.HarmonicMassCrossResidualSandwich

/-- First replay-sized half of the exact fourth bootstrap tranche. -/
theorem lowerSixRecoveryPayment_bootstrap_348_397 : ∀ i : Fin 50,
    -lowerSixWindowPrefix (i.val + 348) ≤
      lowerSixRecoveryReserve (i.val + 348) := by
  decide

/-- Second replay-sized half of the exact fourth bootstrap tranche. -/
theorem lowerSixRecoveryPayment_bootstrap_398_447 : ∀ i : Fin 50,
    -lowerSixWindowPrefix (i.val + 398) ≤
      lowerSixRecoveryReserve (i.val + 398) := by
  decide

/-- Exact fourth bootstrap tranche, assembled without re-running one
monolithic 100-case kernel reduction. -/
theorem lowerSixRecoveryPayment_bootstrap_348_447 : ∀ i : Fin 100,
    -lowerSixWindowPrefix (i.val + 348) ≤
      lowerSixRecoveryReserve (i.val + 348) := by
  intro i
  by_cases hi : i.val < 50
  · let j : Fin 50 := ⟨i.val, hi⟩
    exact lowerSixRecoveryPayment_bootstrap_348_397 j
  · let j : Fin 50 := ⟨i.val - 50, by omega⟩
    have h := lowerSixRecoveryPayment_bootstrap_398_447 j
    have hidx : i.val - 50 + 398 = i.val + 348 := by omega
    simpa [j, hidx] using h

theorem lowerSixRecoveryPayment_348_447
    {k : Nat} (hk0 : 348 ≤ k) (hk1 : k < 448) :
    -lowerSixWindowPrefix k ≤ lowerSixRecoveryReserve k := by
  let i : Fin 100 := ⟨k - 348, by omega⟩
  have h := lowerSixRecoveryPayment_bootstrap_348_447 i
  have hkidx : k - 348 + 348 = k := by omega
  simpa [i, hkidx] using h

theorem growingResidualLowerSix_348_447
    {k : Nat} (hk0 : 348 ≤ k) (hk1 : k < 448) :
    GrowingResidualLowerSix k := by
  apply growingResidualLowerSix_of_interior_nonnegative (by omega)
  exact lowerSixInterior_nonnegative_of_recovery_payment_actual (by omega)
    (lowerSixRecoveryPayment_348_447 hk0 hk1)

theorem growingResidualLowerSix_below_fourFortyEight
    {k : Nat} (hk0 : 10 ≤ k) (hk1 : k < 448) :
    GrowingResidualLowerSix k := by
  by_cases hk348 : 348 ≤ k
  · exact growingResidualLowerSix_348_447 hk348 hk1
  · exact growingResidualLowerSix_below_threeFortyEight hk0 (by omega)

#print axioms lowerSixRecoveryPayment_bootstrap_348_397
#print axioms lowerSixRecoveryPayment_bootstrap_398_447
#print axioms lowerSixRecoveryPayment_bootstrap_348_447
#print axioms lowerSixRecoveryPayment_348_447
#print axioms growingResidualLowerSix_348_447
#print axioms growingResidualLowerSix_below_fourFortyEight

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapFourth
