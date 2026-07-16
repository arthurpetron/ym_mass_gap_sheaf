/-
# Third exact cumulative lower-six recovery tranche

This extends the committed finite anchor by one independently kernel-checked
block.  It is an exact rational certificate and introduces no measured
constant; the symbolic production tail remains a separate theorem.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapSecond

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapThird

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapSecond
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixActual
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixReserveDeficit
open YMGap.Continuum.HarmonicMassCrossLowerSixTerminalPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixTwoSidedWindow
open YMGap.Continuum.HarmonicMassCrossResidualSandwich

/-- Exact third bootstrap tranche for the cumulative recovery payment. -/
theorem lowerSixRecoveryPayment_bootstrap_248_347 : ∀ i : Fin 100,
    -lowerSixWindowPrefix (i.val + 248) ≤
      lowerSixRecoveryReserve (i.val + 248) := by
  decide

theorem lowerSixRecoveryPayment_248_347
    {k : Nat} (hk0 : 248 ≤ k) (hk1 : k < 348) :
    -lowerSixWindowPrefix k ≤ lowerSixRecoveryReserve k := by
  let i : Fin 100 := ⟨k - 248, by omega⟩
  have h := lowerSixRecoveryPayment_bootstrap_248_347 i
  have hkidx : k - 248 + 248 = k := by omega
  simpa [i, hkidx] using h

theorem growingResidualLowerSix_248_347
    {k : Nat} (hk0 : 248 ≤ k) (hk1 : k < 348) :
    GrowingResidualLowerSix k := by
  apply growingResidualLowerSix_of_interior_nonnegative (by omega)
  exact lowerSixInterior_nonnegative_of_recovery_payment_actual (by omega)
    (lowerSixRecoveryPayment_248_347 hk0 hk1)

theorem growingResidualLowerSix_below_threeFortyEight
    {k : Nat} (hk0 : 10 ≤ k) (hk1 : k < 348) :
    GrowingResidualLowerSix k := by
  by_cases hk248 : 248 ≤ k
  · exact growingResidualLowerSix_248_347 hk248 hk1
  · exact growingResidualLowerSix_below_twoFortyEight hk0 (by omega)

#print axioms lowerSixRecoveryPayment_bootstrap_248_347
#print axioms lowerSixRecoveryPayment_248_347
#print axioms growingResidualLowerSix_248_347
#print axioms growingResidualLowerSix_below_threeFortyEight

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapThird
