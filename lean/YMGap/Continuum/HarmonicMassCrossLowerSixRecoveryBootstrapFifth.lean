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

/-- Exact fifth bootstrap tranche for the cumulative recovery payment. -/
theorem lowerSixRecoveryPayment_bootstrap_448_547 : ∀ i : Fin 100,
    -lowerSixWindowPrefix (i.val + 448) ≤
      lowerSixRecoveryReserve (i.val + 448) := by
  decide

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

#print axioms lowerSixRecoveryPayment_bootstrap_448_547
#print axioms lowerSixRecoveryPayment_448_547
#print axioms growingResidualLowerSix_448_547
#print axioms growingResidualLowerSix_below_fiveFortyEight

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapFifth
