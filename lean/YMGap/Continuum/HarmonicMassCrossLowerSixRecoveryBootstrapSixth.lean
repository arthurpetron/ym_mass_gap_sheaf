/-
# Sixth exact cumulative lower-six recovery tranche

This is a replayable fallback block while the symbolic fixed-center
finite-difference proof is developed.  Its constants are exact closed
rationals; no sampled value enters a theorem.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapSixthBlock0
import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapSixthBlock1
import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapSixthBlock2
import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapSixthBlock3
import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapSixthBlock4
import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapSixthBlock5
import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapSixthBlock6
import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapSixthBlock7
import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapSixthBlock8
import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapSixthBlock9

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

/-- First replay-sized half, assembled from five independently compiled
ten-case decisions. -/
theorem lowerSixRecoveryPayment_bootstrap_548_597 : ∀ i : Fin 50,
    -lowerSixWindowPrefix (i.val + 548) ≤
      lowerSixRecoveryReserve (i.val + 548) := by
  intro i
  by_cases hi10 : i.val < 10
  · let j : Fin 10 := ⟨i.val, hi10⟩
    exact lowerSixRecoveryPayment_bootstrap_548_557 j
  · by_cases hi20 : i.val < 20
    · let j : Fin 10 := ⟨i.val - 10, by omega⟩
      have h := lowerSixRecoveryPayment_bootstrap_558_567 j
      have hidx : i.val - 10 + 558 = i.val + 548 := by omega
      simpa only [j, hidx] using h
    · by_cases hi30 : i.val < 30
      · let j : Fin 10 := ⟨i.val - 20, by omega⟩
        have h := lowerSixRecoveryPayment_bootstrap_568_577 j
        have hidx : i.val - 20 + 568 = i.val + 548 := by omega
        simpa only [j, hidx] using h
      · by_cases hi40 : i.val < 40
        · let j : Fin 10 := ⟨i.val - 30, by omega⟩
          have h := lowerSixRecoveryPayment_bootstrap_578_587 j
          have hidx : i.val - 30 + 578 = i.val + 548 := by omega
          simpa only [j, hidx] using h
        · let j : Fin 10 := ⟨i.val - 40, by omega⟩
          have h := lowerSixRecoveryPayment_bootstrap_588_597 j
          have hidx : i.val - 40 + 588 = i.val + 548 := by omega
          simpa only [j, hidx] using h

/-- Second replay-sized half, assembled from five independently compiled
ten-case decisions. -/
theorem lowerSixRecoveryPayment_bootstrap_598_647 : ∀ i : Fin 50,
    -lowerSixWindowPrefix (i.val + 598) ≤
      lowerSixRecoveryReserve (i.val + 598) := by
  intro i
  by_cases hi10 : i.val < 10
  · let j : Fin 10 := ⟨i.val, hi10⟩
    exact lowerSixRecoveryPayment_bootstrap_598_607 j
  · by_cases hi20 : i.val < 20
    · let j : Fin 10 := ⟨i.val - 10, by omega⟩
      have h := lowerSixRecoveryPayment_bootstrap_608_617 j
      have hidx : i.val - 10 + 608 = i.val + 598 := by omega
      simpa only [j, hidx] using h
    · by_cases hi30 : i.val < 30
      · let j : Fin 10 := ⟨i.val - 20, by omega⟩
        have h := lowerSixRecoveryPayment_bootstrap_618_627 j
        have hidx : i.val - 20 + 618 = i.val + 598 := by omega
        simpa only [j, hidx] using h
      · by_cases hi40 : i.val < 40
        · let j : Fin 10 := ⟨i.val - 30, by omega⟩
          have h := lowerSixRecoveryPayment_bootstrap_628_637 j
          have hidx : i.val - 30 + 628 = i.val + 598 := by omega
          simpa only [j, hidx] using h
        · let j : Fin 10 := ⟨i.val - 40, by omega⟩
          have h := lowerSixRecoveryPayment_bootstrap_638_647 j
          have hidx : i.val - 40 + 638 = i.val + 598 := by omega
          simpa only [j, hidx] using h

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
    simpa only [j, hidx] using h

theorem lowerSixRecoveryPayment_548_647
    {k : Nat} (hk0 : 548 ≤ k) (hk1 : k < 648) :
    -lowerSixWindowPrefix k ≤ lowerSixRecoveryReserve k := by
  let i : Fin 100 := ⟨k - 548, by omega⟩
  have h := lowerSixRecoveryPayment_bootstrap_548_647 i
  have hkidx : k - 548 + 548 = k := by omega
  simpa only [i, hkidx] using h

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
