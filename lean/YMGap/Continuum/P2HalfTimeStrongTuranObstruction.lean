/-
Track 11.7-fusion / R4k -- obstruction to the fixed-w strong-Turan
compression.

The two heat-matched parity transitions are true on the physical schedule,
but the stronger proposal which asks for one adjacent `w`-row at every
centre is not.  Its first arithmetic row already fails at the first scale of
the proposed all-scale family (`k = 4`, `t = 1`).  This module records that
failure by kernel computation and proves that the schedule-wide arithmetic
carrier is uninhabited.

This is a frontier correction, not a Yang--Mills closure.  The live route is
the exact odd/even transition family, equivalently the full low-debt /
high-reserve balance from `P2HalfTimeShiftTail`.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2HalfTimeStrongTuranCompiler

namespace YMGap.Continuum.P2HalfTimeStrongTuranObstruction

open YMGap.Continuum.P2HalfTimeStrongTuranCompiler

set_option maxHeartbeats 12000000
set_option maxRecDepth 1000000
set_option exponentiation.threshold 900000

/-- The proposed fixed-`w` compression fails at its first physical scale and
first supported centre.  The proposition is the exact cleared natural-number
cross-product, so `decide` is kernel computation rather than a floating-point
or native certificate. -/
theorem physicalHalfTimeBoxTuranAt_four_one_false :
    ¬ physicalHalfTimeBoxTuranAt 4 1 := by
  decide

/-- Consequently the schedule-wide pure-natural strong-Turan carrier is
constructively empty. -/
theorem integralStrongTuranFromFour_uninhabited
    (T : BlockCompatibleP2HalfTimeIntegralStrongTuranFromFour) : False :=
  physicalHalfTimeBoxTuranAt_four_one_false
    (T.turan 4 1 (by decide) (by decide) (by decide))

end YMGap.Continuum.P2HalfTimeStrongTuranObstruction

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeStrongTuranObstruction.physicalHalfTimeBoxTuranAt_four_one_false
#print axioms YMGap.Continuum.P2HalfTimeStrongTuranObstruction.integralStrongTuranFromFour_uninhabited
