/-
Track 11.7-fusion / R4ae -- bounded direct half-time certificates at the
first unresolved physical cutoff.

The endpoint-spliced parity compiler leaves an all-scale transition family.
At the first unresolved scale `k=4` the cutoff is the concrete value `79`.
This module reflects a bounded list of the direct half-time cells, rather
than asking the kernel to normalize a single enormous conjunction or
rechecking transition cross-products with four box coefficients per cell.

The generic soundness theorem is a proof about computation: successful
Boolean evaluation on `[start,start+length)` yields the original rational
half-time inequality at every member of that interval.  The concrete row is
split into small blocks so each certificate remains independently reviewable
and the monitored Lean launcher retains a useful progress boundary.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2HalfTimeEndpointSplicedParityCompiler

namespace YMGap.Continuum.P2HalfTimeScaleFourCertificate

set_option maxHeartbeats 12000000
set_option maxRecDepth 300000
set_option exponentiation.threshold 300000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleScheduleClosed
open YMGap.Continuum.P2HalfTimeParityStrandCompiler
open YMGap.Continuum.RGTransport

/-! ## 1. Generic bounded reflection -/

/-- Boolean scan of direct half-time cells on a consecutive interval. -/
def halfTimeIntegralTailBlockCheck
    (num den N start length : Nat) : Bool :=
  (List.range length).all fun i =>
    decide (halfTimeIntegralTailAt num den N (start + i))

/-- A successful bounded scan supplies every direct cell in its interval. -/
theorem halfTimeIntegralTailBlockCheck_sound
    {num den N start length s : Nat}
    (hcheck : halfTimeIntegralTailBlockCheck
      num den N start length = true)
    (hstart : start <= s) (hstop : s < start + length) :
    halfTimeIntegralTailAt num den N s := by
  unfold halfTimeIntegralTailBlockCheck at hcheck
  have hmem : s - start ∈ List.range length := by
    rw [List.mem_range]
    omega
  have hrow := List.all_eq_true.mp hcheck (s - start) hmem
  have hindex : start + (s - start) = s := by omega
  rw [hindex] at hrow
  exact of_decide_eq_true hrow

/-! ## 2. Physical scale four -/

private theorem scaleFour_coordinates :
    physicalWeightNum 4 = 3071 ∧
      physicalWeightDen 4 = 3072 ∧ blockNcut 4 = 79 := by
  decide

/-- First small block of the scale-four direct row.  Subsequent blocks use
the same checker; keeping this initial certificate separate gives the
monitored build a cheap feasibility gate before the full row is attempted. -/
theorem physicalHalfTimeScaleFourCheck_2_17 :
    halfTimeIntegralTailBlockCheck 3071 3072 79 2 16 = true := by
  decide

/-- Rational soundness of the first checked scale-four block. -/
theorem physical_halfTime_scaleFour_2_17
    (s : Nat) (hs : 2 <= s) (hs' : s < 18) :
    dimQ s * bondMovedCoeff (blockNcut 4) (blockWeight 4) 2 (s + 1) <=
      qpow (blockWeight 4) (s + 2) *
        (dimQ (s + 1) * bondMovedCoeff
          (blockNcut 4) (blockWeight 4) 2 s) := by
  have hcell : halfTimeIntegralTailAt 3071 3072 79 s :=
    halfTimeIntegralTailBlockCheck_sound
      physicalHalfTimeScaleFourCheck_2_17 hs (by omega)
  have hcoords := scaleFour_coordinates
  rw [hcoords.2.2]
  exact halfTimeIntegralTailAt_sound 3071 3072 79 s (by decide)
    (blockWeight 4) (by simpa only [hcoords.1, hcoords.2.1] using
      blockWeight_eqv_closed 4) hcell


end YMGap.Continuum.P2HalfTimeScaleFourCertificate

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeScaleFourCertificate.halfTimeIntegralTailBlockCheck_sound
#print axioms YMGap.Continuum.P2HalfTimeScaleFourCertificate.physicalHalfTimeScaleFourCheck_2_17
#print axioms YMGap.Continuum.P2HalfTimeScaleFourCertificate.physical_halfTime_scaleFour_2_17
