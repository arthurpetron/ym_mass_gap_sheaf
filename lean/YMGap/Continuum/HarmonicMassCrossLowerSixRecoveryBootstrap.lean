/-
Exact finite bootstrap for the genuinely cumulative lower-six recovery
payment.  The computation is kernel reduction over closed rationals; no
measured constant enters the proof.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryPairingFence

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrap

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixReserveDeficit
open YMGap.Continuum.HarmonicMassCrossLowerSixTwoSidedWindow

/-- Exact first bootstrap tranche for the cumulative payment. -/
theorem lowerSixRecoveryPayment_bootstrap_48_147 : ∀ i : Fin 100,
    -lowerSixWindowPrefix (i.val + 48) ≤
      lowerSixRecoveryReserve (i.val + 48) := by
  decide

#print axioms lowerSixRecoveryPayment_bootstrap_48_147

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrap
