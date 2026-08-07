/-
Track 11.7-fusion / R4ap -- scale-five strand-linear certificate blocks.

This is the first concrete consumer of the exact strand evaluator.  It checks
sixteen consecutive physical `k = 5` half-time cells in one bounded Boolean
scan and transports them to the original `bondMovedCoeff` statement through
the generic computation theorem.

No `Classical`, `native_decide`, explicit proof hole, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.P2HalfTimeStrandIntegralCertificate

namespace YMGap.Continuum.P2HalfTimeScaleFiveStrandCertificate

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

/-- Sixteen consecutive scale-five cells evaluated on their sharp A1
strands, rather than on the full cutoff square. -/
theorem physicalHalfTimeScaleFiveStrandCheck_10_25 :
    halfTimeStrandIntegralBlockCheck 12287 12288 159 10 16 = true := by
  decide

/-- Rational physical soundness of the checked scale-five strand block. -/
theorem physical_halfTime_scaleFive_strand_10_25
    (s : Nat) (hs : 10 <= s) (hs' : s < 26) :
    dimQ s * bondMovedCoeff (blockNcut 5) (blockWeight 5) 2 (s + 1) <=
      qpow (blockWeight 5) (s + 2) *
        (dimQ (s + 1) * bondMovedCoeff
          (blockNcut 5) (blockWeight 5) 2 s) := by
  have hcell : halfTimeStrandIntegralAt 12287 12288 159 s :=
    halfTimeStrandIntegralBlockCheck_sound
      physicalHalfTimeScaleFiveStrandCheck_10_25 hs (by omega)
  have hcoords := scaleFive_coordinates
  rw [hcoords.2.2]
  exact halfTimeStrandIntegralAt_sound 12287 12288 159 s (by decide)
    (blockWeight 5) (by simpa only [hcoords.1, hcoords.2.1] using
      blockWeight_eqv_closed 5) hcell

end YMGap.Continuum.P2HalfTimeScaleFiveStrandCertificate

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeScaleFiveStrandCertificate.physicalHalfTimeScaleFiveStrandCheck_10_25
#print axioms YMGap.Continuum.P2HalfTimeScaleFiveStrandCertificate.physical_halfTime_scaleFive_strand_10_25
