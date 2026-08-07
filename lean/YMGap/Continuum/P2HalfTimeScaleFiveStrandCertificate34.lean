/-
Track 11.7-fusion / R4au -- third scale-five strand-linear block.

The block remains process-isolated and eight cells wide.  This retains the
sharp-strand proof-about-computation interface while keeping the monitored
kernel normalization below the host reserve.

No `Classical`, `native_decide`, explicit proof hole, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.P2HalfTimeStrandIntegralCertificate

namespace YMGap.Continuum.P2HalfTimeScaleFiveStrandCertificate34

set_option maxHeartbeats 12000000
set_option maxRecDepth 300000
set_option exponentiation.threshold 300000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleScheduleClosed
open YMGap.Continuum.P2HalfTimeStrandIntegralCertificate
open YMGap.Continuum.RGTransport

private theorem scaleFive_coordinates :
    physicalWeightNum 5 = 12287 ∧
      physicalWeightDen 5 = 12288 ∧ blockNcut 5 = 159 := by
  decide

/-- Eight further sharp-strand scale-five cells. -/
theorem physicalHalfTimeScaleFiveStrandCheck_34_41 :
    halfTimeStrandIntegralBlockCheck 12287 12288 159 34 8 = true := by
  decide

/-- Rational physical soundness of the third checked strand block. -/
theorem physical_halfTime_scaleFive_strand_34_41
    (s : Nat) (hs : 34 <= s) (hs' : s < 42) :
    dimQ s * bondMovedCoeff (blockNcut 5) (blockWeight 5) 2 (s + 1) <=
      qpow (blockWeight 5) (s + 2) *
        (dimQ (s + 1) * bondMovedCoeff
          (blockNcut 5) (blockWeight 5) 2 s) := by
  have hcell : halfTimeStrandIntegralAt 12287 12288 159 s :=
    halfTimeStrandIntegralBlockCheck_sound
      physicalHalfTimeScaleFiveStrandCheck_34_41 hs (by omega)
  have hcoords := scaleFive_coordinates
  rw [hcoords.2.2]
  exact halfTimeStrandIntegralAt_sound 12287 12288 159 s (by decide)
    (blockWeight 5) (by simpa only [hcoords.1, hcoords.2.1] using
      blockWeight_eqv_closed 5) hcell

end YMGap.Continuum.P2HalfTimeScaleFiveStrandCertificate34

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeScaleFiveStrandCertificate34.physicalHalfTimeScaleFiveStrandCheck_34_41
#print axioms YMGap.Continuum.P2HalfTimeScaleFiveStrandCertificate34.physical_halfTime_scaleFive_strand_34_41
