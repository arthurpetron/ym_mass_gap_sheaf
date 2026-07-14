/-
Second exact cumulative-payment bootstrap, split into bounded kernel-decision
tranches so each certificate remains independently checkable.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapClosure

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapSecond

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapClosure
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixActual
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixReserveDeficit
open YMGap.Continuum.HarmonicMassCrossLowerSixTerminalPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixTwoSidedWindow
open YMGap.Continuum.HarmonicMassCrossResidualSandwich

theorem lowerSixRecoveryPayment_bootstrap_148_247 : ∀ i : Fin 100,
    -lowerSixWindowPrefix (i.val + 148) ≤
      lowerSixRecoveryReserve (i.val + 148) := by
  decide

theorem lowerSixRecoveryPayment_148_247 {k : Nat}
    (hk0 : 148 ≤ k) (hk1 : k < 248) :
    -lowerSixWindowPrefix k ≤ lowerSixRecoveryReserve k := by
  let i : Fin 100 := ⟨k - 148, by omega⟩
  have h := lowerSixRecoveryPayment_bootstrap_148_247 i
  have hkidx : k - 148 + 148 = k := by omega
  simpa [i, hkidx] using h

theorem growingResidualLowerSix_148_247 {k : Nat}
    (hk0 : 148 ≤ k) (hk1 : k < 248) :
    GrowingResidualLowerSix k := by
  apply growingResidualLowerSix_of_interior_nonnegative (by omega)
  exact lowerSixInterior_nonnegative_of_recovery_payment_actual (by omega)
    (lowerSixRecoveryPayment_148_247 hk0 hk1)

theorem growingResidualLowerSix_below_twoFortyEight {k : Nat}
    (hk0 : 10 ≤ k) (hk1 : k < 248) :
    GrowingResidualLowerSix k := by
  by_cases hk148 : 148 ≤ k
  · exact growingResidualLowerSix_148_247 hk148 hk1
  · exact growingResidualLowerSix_below_oneFortyEight hk0 (by omega)

#print axioms lowerSixRecoveryPayment_bootstrap_148_247
#print axioms lowerSixRecoveryPayment_148_247
#print axioms growingResidualLowerSix_148_247
#print axioms growingResidualLowerSix_below_twoFortyEight

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapSecond
