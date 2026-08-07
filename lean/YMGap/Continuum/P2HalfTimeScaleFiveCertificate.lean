/-
Track 11.7-fusion / R4an -- bounded direct half-time certificates at physical
scale five.

The generic reflected checker and its soundness theorem were proved once in
the scale-four campaign.  Here they are reused at the next physical cutoff,
`N_5 = 159` and `w_5 = 12287/12288`.  Small independent blocks keep kernel
normalization bounded and give a restartable path toward the complete
scale-five row.

No `Classical`, `native_decide`, explicit proof hole, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.P2HalfTimeScaleFourCertificate

namespace YMGap.Continuum.P2HalfTimeScaleFiveCertificate

set_option maxHeartbeats 12000000
set_option maxRecDepth 300000
set_option exponentiation.threshold 300000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleScheduleClosed
open YMGap.Continuum.P2HalfTimeParityStrandCompiler
open YMGap.Continuum.P2HalfTimeScaleFourCertificate
open YMGap.Continuum.RGTransport

private theorem scaleFive_coordinates :
    physicalWeightNum 5 = 12287 ∧
      physicalWeightDen 5 = 12288 ∧ blockNcut 5 = 159 := by
  decide

/-- Feasibility block for the first eight non-head scale-five cells. -/
theorem physicalHalfTimeScaleFiveCheck_2_9 :
    halfTimeIntegralTailBlockCheck 12287 12288 159 2 8 = true := by
  decide

/-- Rational soundness of the first reflected scale-five block. -/
theorem physical_halfTime_scaleFive_2_9
    (s : Nat) (hs : 2 <= s) (hs' : s < 10) :
    dimQ s * bondMovedCoeff (blockNcut 5) (blockWeight 5) 2 (s + 1) <=
      qpow (blockWeight 5) (s + 2) *
        (dimQ (s + 1) * bondMovedCoeff
          (blockNcut 5) (blockWeight 5) 2 s) := by
  have hcell : halfTimeIntegralTailAt 12287 12288 159 s :=
    halfTimeIntegralTailBlockCheck_sound
      physicalHalfTimeScaleFiveCheck_2_9 hs (by omega)
  have hcoords := scaleFive_coordinates
  rw [hcoords.2.2]
  exact halfTimeIntegralTailAt_sound 12287 12288 159 s (by decide)
    (blockWeight 5) (by simpa only [hcoords.1, hcoords.2.1] using
      blockWeight_eqv_closed 5) hcell

end YMGap.Continuum.P2HalfTimeScaleFiveCertificate

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeScaleFiveCertificate.physicalHalfTimeScaleFiveCheck_2_9
#print axioms YMGap.Continuum.P2HalfTimeScaleFiveCertificate.physical_halfTime_scaleFive_2_9
