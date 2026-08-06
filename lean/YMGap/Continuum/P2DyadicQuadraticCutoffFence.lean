/-
Track 11.7-fusion / R2z -- exact fence for the quadratic cutoff schedule.

The proposed trajectory

    N_k = (k+2)^2,  w_k = 1 - (1/12)2^-k

passes its first cells, but its cutoff ratio tends to one while the physical
block map squares the fine eigenvalue.  This file locates the first exact
failure at `k=5` (`N=49 -> 64`).  It uses the common-denominator `Nat`
certificate from `P2VacNormIntegralCertificate`; no large normalized rational
fusion sum is evaluated.

This is a schedule fence, not a failure of the fusion-spectrum/Phi dictionary:
the latter remains available for a cutoff schedule compatible with the block
power.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2VacNormIntegralCertificate

namespace YMGap.Continuum.P2DyadicQuadraticCutoffFence

set_option maxRecDepth 30000
set_option exponentiation.threshold 10000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.P2DyadicFusionEndpointCriterion
open YMGap.Continuum.P2DyadicFusionGapEnvelope
open YMGap.Continuum.P2DyadicFusionMonotonicityAudit
open YMGap.Continuum.P2VacNormIntegralCertificate
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

/-- Exact reduced rational presentation of the coarse heat weight. -/
theorem dyadicWeight_five_eqv :
    dyadicWeight 5 ≈ Q'.mkPos 383 384 (by decide) := by
  decide

/-- Exact reduced rational presentation of the fine heat weight. -/
theorem dyadicWeight_six_eqv :
    dyadicWeight 6 ≈ Q'.mkPos 767 768 (by decide) := by
  decide

/-- Integral reconstruction of the `k=5` physical mode-one quotient. -/
def coarseScaledModeOne : Q' :=
  scaledModeOne 383 384 (Ncut 5) (by decide)

/-- Integral reconstruction of the `k=6` physical mode-one quotient. -/
def fineScaledModeOne : Q' :=
  scaledModeOne 767 768 (Ncut 6) (by decide)

theorem rawDyadicModeOne_five_eqv :
    rawDyadicModeOne 5 ≈ coarseScaledModeOne := by
  exact p2VacNorm_one_eqv_scaled 383 384 (by decide)
    (dyadicWeight 5) dyadicWeight_five_eqv
    (dyadicWeight_nonneg 5) (dyadicWeight_le_one 5) (Ncut 5) (by decide)

theorem rawDyadicModeOne_six_eqv :
    rawDyadicModeOne 6 ≈ fineScaledModeOne := by
  exact p2VacNorm_one_eqv_scaled 767 768 (by decide)
    (dyadicWeight 6) dyadicWeight_six_eqv
    (dyadicWeight_nonneg 6) (dyadicWeight_le_one 6) (Ncut 6) (by decide)

/-- The sole large arithmetic fact is an integer comparison between four
cleared finite sums. -/
theorem scaled_step_five_refuted :
    ¬ (coarseScaledModeOne <= qpow fineScaledModeOne 2) := by
  decide

/-- **First exact quadratic-schedule obstruction.**  The physical mode-one
square inequality reverses at `k=5`. -/
theorem p2VacNorm_step_five_refuted :
    ¬ (rawDyadicModeOne 5 <= qpow (rawDyadicModeOne 6) 2) := by
  intro h
  have hfine := BondMovingRelResidual.qpow_eqv_congr_base
    rawDyadicModeOne_six_eqv 2
  have hscaled : coarseScaledModeOne <= qpow fineScaledModeOne 2 :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv rawDyadicModeOne_five_eqv)
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hfine))
  exact scaled_step_five_refuted hscaled

/-- Hence the all-tail carrier previously isolated for the quadratic schedule
is constructively uninhabited. -/
theorem no_quadratic_cutoff_modeOne_tail
    (M : DyadicP2ModeOneTailMonotonicity) : False :=
  p2VacNorm_step_five_refuted (M.tail 5 (by decide))

/-- The endpoint-budget carrier is also fenced, since it compiles to that raw
mode-one tail. -/
theorem no_quadratic_cutoff_endpoint_tail
    (E : DyadicP2EndpointMonotonicityTail) : False :=
  no_quadratic_cutoff_modeOne_tail E.toModeOneTailMonotonicity

end YMGap.Continuum.P2DyadicQuadraticCutoffFence

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2DyadicQuadraticCutoffFence.scaled_step_five_refuted
#print axioms YMGap.Continuum.P2DyadicQuadraticCutoffFence.p2VacNorm_step_five_refuted
#print axioms YMGap.Continuum.P2DyadicQuadraticCutoffFence.no_quadratic_cutoff_modeOne_tail
#print axioms YMGap.Continuum.P2DyadicQuadraticCutoffFence.no_quadratic_cutoff_endpoint_tail
