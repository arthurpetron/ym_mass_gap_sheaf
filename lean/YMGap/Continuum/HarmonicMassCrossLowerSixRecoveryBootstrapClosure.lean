/-
Close the exact lower-six scale band reached by the cumulative recovery
bootstrap.  This is a finite constructive anchor, not a substitute for the
remaining uniform full-suffix argument.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixSuffixActual
import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrap

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapClosure

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrap
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixActual
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixReserveDeficit
open YMGap.Continuum.HarmonicMassCrossLowerSixTerminalPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixTwoSidedWindow
open YMGap.Continuum.HarmonicMassCrossResidualSandwich

theorem lowerSixRecoveryPayment_48_147 {k : Nat}
    (hk0 : 48 ≤ k) (hk1 : k < 148) :
    -lowerSixWindowPrefix k ≤ lowerSixRecoveryReserve k := by
  let i : Fin 100 := ⟨k - 48, by omega⟩
  have h := lowerSixRecoveryPayment_bootstrap_48_147 i
  have hkidx : k - 48 + 48 = k := by omega
  simpa [i, hkidx] using h

theorem growingResidualLowerSix_48_147 {k : Nat}
    (hk0 : 48 ≤ k) (hk1 : k < 148) :
    GrowingResidualLowerSix k := by
  apply growingResidualLowerSix_of_interior_nonnegative hk0
  exact lowerSixInterior_nonnegative_of_recovery_payment_actual hk0
    (lowerSixRecoveryPayment_48_147 hk0 hk1)

/-- Exact closure of every lower-six scale from the original base `k=10`
through `k=147`. -/
theorem growingResidualLowerSix_below_oneFortyEight {k : Nat}
    (hk0 : 10 ≤ k) (hk1 : k < 148) :
    GrowingResidualLowerSix k := by
  by_cases hk48 : 48 ≤ k
  · exact growingResidualLowerSix_48_147 hk48 hk1
  · exact growingResidualLowerSix_below_forty_eight hk0 (by omega)

#print axioms lowerSixRecoveryPayment_48_147
#print axioms growingResidualLowerSix_48_147
#print axioms growingResidualLowerSix_below_oneFortyEight

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapClosure
