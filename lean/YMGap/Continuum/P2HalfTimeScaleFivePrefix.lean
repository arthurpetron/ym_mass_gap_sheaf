/-
Track 11.7-fusion / R4ar -- joined scale-five half-time prefix.

This module splices the process-isolated direct and sharp-strand certificate
blocks into one physical theorem.  The current honest scope is the contiguous
prefix `2 <= s < 42` at `N_5 = 159`; it does not claim the remaining interior
or the complete scale-five row.

No `Classical`, `native_decide`, explicit proof hole, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.P2HalfTimeScaleFiveCertificate
import YMGap.Continuum.P2HalfTimeScaleFiveStrandCertificate
import YMGap.Continuum.P2HalfTimeScaleFiveStrandCertificate26
import YMGap.Continuum.P2HalfTimeScaleFiveStrandCertificate34

namespace YMGap.Continuum.P2HalfTimeScaleFivePrefix

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2HalfTimeScaleFiveCertificate
open YMGap.Continuum.P2HalfTimeScaleFiveStrandCertificate
open YMGap.Continuum.P2HalfTimeScaleFiveStrandCertificate26
open YMGap.Continuum.P2HalfTimeScaleFiveStrandCertificate34
open YMGap.Continuum.RGTransport

/-- Joined physical scale-five half-time prefix. -/
theorem physical_halfTime_scaleFive_prefix_2_41
    (s : Nat) (hs : 2 <= s) (hs' : s < 42) :
    dimQ s * bondMovedCoeff (blockNcut 5) (blockWeight 5) 2 (s + 1) <=
      qpow (blockWeight 5) (s + 2) *
        (dimQ (s + 1) * bondMovedCoeff
          (blockNcut 5) (blockWeight 5) 2 s) := by
  by_cases h10 : s < 10
  · exact physical_halfTime_scaleFive_2_9 s hs h10
  · by_cases h26 : s < 26
    · exact physical_halfTime_scaleFive_strand_10_25 s (by omega) h26
    · by_cases h34 : s < 34
      · exact physical_halfTime_scaleFive_strand_26_33 s (by omega) h34
      · exact physical_halfTime_scaleFive_strand_34_41 s (by omega) hs'

end YMGap.Continuum.P2HalfTimeScaleFivePrefix

/-! ## Axiom-dependency gate -/

#print axioms YMGap.Continuum.P2HalfTimeScaleFivePrefix.physical_halfTime_scaleFive_prefix_2_41
