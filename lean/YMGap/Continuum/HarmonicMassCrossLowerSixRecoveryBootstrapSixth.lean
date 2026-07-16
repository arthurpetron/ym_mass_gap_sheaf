/-
# Sixth exact cumulative lower-six recovery tranche

This is a replayable fallback block while the symbolic fixed-center
finite-difference proof is developed.  Its constants are exact closed
rationals; no sampled value enters a theorem.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapFifth

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapSixth

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapFifth
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixActual
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixReserveDeficit
open YMGap.Continuum.HarmonicMassCrossLowerSixTerminalPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixTwoSidedWindow
open YMGap.Continuum.HarmonicMassCrossResidualSandwich

/-- First replay-sized half of the exact sixth fallback tranche. -/
theorem lowerSixRecoveryPayment_bootstrap_548_597 : ∀ i : Fin 50,
    -lowerSixWindowPrefix (i.val + 548) ≤
      lowerSixRecoveryReserve (i.val + 548) := by
  decide

/-- Second replay-sized half of the exact sixth fallback tranche. -/
theorem lowerSixRecoveryPayment_bootstrap_598_647 : ∀ i : Fin 50,
    -lowerSixWindowPrefix (i.val + 598) ≤
      lowerSixRecoveryReserve (i.val + 598) := by
  decide

/-- Exact sixth fallback tranche, assembled without re-running one monolithic
100-case kernel reduction. -/
theorem lowerSixRecoveryPayment_bootstrap_548_647 : ∀ i : Fin 100,
    -lowerSixWindowPrefix (i.val + 548) ≤
      lowerSixRecoveryReserve (i.val + 548) := by
  intro i
  by_cases hi : i.val < 50
  · let j : Fin 50 := ⟨i.val, hi⟩
    exact lowerSixRecoveryPayment_bootstrap_548_597 j
  · let j : Fin 50 := ⟨i.val - 50, by omega⟩
    have h := lowerSixRecoveryPayment_bootstrap_598_647 j
    have hidx : i.val - 50 + 598 = i.val + 548 := by omega
    simpa [j, hidx] using h

theorem lowerSixRecoveryPayment_548_647
    {k : Nat} (hk0 : 548 ≤ k) (hk1 : k < 648) :
    -lowerSixWindowPrefix k ≤ lowerSixRecoveryReserve k := by
  let i : Fin 100 := ⟨k - 548, by omega⟩
  have h := lowerSixRecoveryPayment_bootstrap_548_647 i
  have hkidx : k - 548 + 548 = k := by omega
  simpa [i, hkidx] using h

theorem growingResidualLowerSix_548_647
    {k : Nat} (hk0 : 548 ≤ k) (hk1 : k < 648) :
    GrowingResidualLowerSix k := by
  apply growingResidualLowerSix_of_interior_nonnegative (by omega)
  exact lowerSixInterior_nonnegative_of_recovery_payment_actual (by omega)
    (lowerSixRecoveryPayment_548_647 hk0 hk1)

theorem growingResidualLowerSix_below_sixFortyEight
    {k : Nat} (hk0 : 10 ≤ k) (hk1 : k < 648) :
    GrowingResidualLowerSix k := by
  by_cases hk548 : 548 ≤ k
  · exact growingResidualLowerSix_548_647 hk548 hk1
  · exact growingResidualLowerSix_below_fiveFortyEight hk0 (by omega)

#print axioms lowerSixRecoveryPayment_bootstrap_548_597
#print axioms lowerSixRecoveryPayment_bootstrap_598_647
#print axioms lowerSixRecoveryPayment_bootstrap_548_647
#print axioms lowerSixRecoveryPayment_548_647
#print axioms growingResidualLowerSix_548_647
#print axioms growingResidualLowerSix_below_sixFortyEight

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapSixth
