/- Exact bounded leaf for the sixth lower-six recovery bootstrap. -/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapFifth

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapSixth

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixActual
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixReserveDeficit
open YMGap.Continuum.HarmonicMassCrossLowerSixTwoSidedWindow

theorem lowerSixRecoveryPayment_bootstrap_608_617 : ∀ i : Fin 10,
    -lowerSixWindowPrefix (i.val + 608) ≤
      lowerSixRecoveryReserve (i.val + 608) := by
  decide

#print axioms lowerSixRecoveryPayment_bootstrap_608_617

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapSixth
