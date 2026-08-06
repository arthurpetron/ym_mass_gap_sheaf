/-
Track 11.7-fusion / R2v -- finite-head audit for dyadic spectral monotonicity.

The physical quotient route has been reduced to

    modeOne(k) <= modeOne(k+1)^2.

This file kernel-checks the two expensive small-cutoff cells once, at
`N=4 -> 9` and `N=9 -> 16`.  A generic equivalence bridge then transfers a
raw `p2VacNorm` tail theorem to every compiled dyadic control family.  Thus
the remaining arithmetic wall begins at `k=2`; no growing family of closed
rational certificates is stored.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2DyadicFusionHalfFloor

namespace YMGap.Continuum.P2DyadicFusionMonotonicityAudit

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BlockingStepFrontier
open YMGap.Continuum.P2DyadicFusionGapBudget
open YMGap.Continuum.P2DyadicFusionGapEnvelope
open YMGap.Continuum.P2DyadicFusionHalfFloor
open YMGap.Continuum.P2RetunedBlockingDictionary
open YMGap.Continuum.P2RetunedFusionReferenceGap
open YMGap.Continuum.P2RetunedFusionPhysicalMode
open YMGap.Continuum.P2RetunedFusionPowerCertificate
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.RGTransport

set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

/-- Exact first dyadic cell, `N=4,w=11/12 -> N=9,w=23/24`. -/
theorem p2VacNorm_step_zero :
    p2VacNorm (Ncut 0) (dyadicWeight_nonneg 0) (dyadicWeight_le_one 0) 1 <=
      qpow
        (p2VacNorm (Ncut 1) (dyadicWeight_nonneg 1)
          (dyadicWeight_le_one 1) 1) 2 := by
  decide

/-- Exact second dyadic cell, `N=9,w=23/24 -> N=16,w=47/48`. -/
theorem p2VacNorm_step_one :
    p2VacNorm (Ncut 1) (dyadicWeight_nonneg 1) (dyadicWeight_le_one 1) 1 <=
      qpow
        (p2VacNorm (Ncut 2) (dyadicWeight_nonneg 2)
          (dyadicWeight_le_one 2) 1) 2 := by
  decide

/-- Equivalence transport from the raw vacuum-normalized spectrum to the
mode selected by an arbitrary compiled dyadic control family. -/
theorem fusionModeOne_coarse_le_fineSquare_of_raw
    (D : DyadicP2CoeffTailData) (k : Nat)
    (hraw :
      p2VacNorm (Ncut k) (dyadicWeight_nonneg k)
          (dyadicWeight_le_one k) 1 <=
        qpow
          (p2VacNorm (Ncut (k + 1)) (dyadicWeight_nonneg (k + 1))
            (dyadicWeight_le_one (k + 1)) 1) 2) :
    fusionModeQ D.toControlFamily modeOne k <=
      qpow (fusionModeQ D.toControlFamily modeOne (k + 1)) 2 := by
  have hcoarse := fusionModeOne_eqv_p2VacNorm D.toControlFamily k
  have hfine := fusionModeOne_eqv_p2VacNorm D.toControlFamily (k + 1)
  have hfinePower :=
    BondMovingRelResidual.qpow_eqv_congr_base hfine 2
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hcoarse)
    (Q'.le_trans' _ _ _ hraw (Q'.ge_of_eqv hfinePower))

/-- The two kernel-checked head cells hold for every compiled dyadic control
family; proof fields in the family play no computational role. -/
theorem fusionModeOne_step_zero (D : DyadicP2CoeffTailData) :
    fusionModeQ D.toControlFamily modeOne 0 <=
      qpow (fusionModeQ D.toControlFamily modeOne 1) 2 :=
  fusionModeOne_coarse_le_fineSquare_of_raw D 0 p2VacNorm_step_zero

theorem fusionModeOne_step_one (D : DyadicP2CoeffTailData) :
    fusionModeQ D.toControlFamily modeOne 1 <=
      qpow (fusionModeQ D.toControlFamily modeOne 2) 2 :=
  fusionModeOne_coarse_le_fineSquare_of_raw D 1 p2VacNorm_step_one

/-- Proof-about-computation tail carrier.  The finite exceptional prefix has
already been discharged, so a structural argument need only cover `k >= 2`.
The statement is independent of any proof fields in `CanonicalBulkControl`. -/
structure DyadicP2ModeOneTailMonotonicity : Type where
  tail : forall k, 2 <= k ->
    p2VacNorm (Ncut k) (dyadicWeight_nonneg k)
        (dyadicWeight_le_one k) 1 <=
      qpow
        (p2VacNorm (Ncut (k + 1)) (dyadicWeight_nonneg (k + 1))
          (dyadicWeight_le_one (k + 1)) 1) 2

/-- Combine the two exact head cells with one uniform tail theorem. -/
theorem DyadicP2ModeOneTailMonotonicity.coarseLeFineSquare
    (M : DyadicP2ModeOneTailMonotonicity)
    (D : DyadicP2CoeffTailData) (k : Nat) :
    fusionModeQ D.toControlFamily modeOne k <=
      qpow (fusionModeQ D.toControlFamily modeOne (k + 1)) 2 := by
  cases k with
  | zero => exact fusionModeOne_step_zero D
  | succ k =>
      cases k with
      | zero => exact fusionModeOne_step_one D
      | succ k =>
          exact fusionModeOne_coarse_le_fineSquare_of_raw D (k + 2)
            (M.tail (k + 2) (by omega))

/-- The head/tail compiler constructs the complete one-inequality physical
spectral carrier used by the genuine `BlockingStep.Phi` route. -/
def DyadicP2ModeOneTailMonotonicity.toPhysicalMonotoneInput
    (M : DyadicP2ModeOneTailMonotonicity)
    {D : DyadicP2CoeffTailData} {R : DyadicP2RefinedCutoffData D}
    {B : BlockingStep (fusionSeparator D.toControlFamily modeOne)}
    (hCq : R.Cq <= cutoffCoeffCap) :
    DyadicP2PhysicalMonotoneInput D R B where
  cutoffCoeff_le := hCq
  coarseLeFineSquare := M.coarseLeFineSquare D

end YMGap.Continuum.P2DyadicFusionMonotonicityAudit

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2DyadicFusionMonotonicityAudit.p2VacNorm_step_zero
#print axioms YMGap.Continuum.P2DyadicFusionMonotonicityAudit.p2VacNorm_step_one
#print axioms YMGap.Continuum.P2DyadicFusionMonotonicityAudit.fusionModeOne_coarse_le_fineSquare_of_raw
#print axioms YMGap.Continuum.P2DyadicFusionMonotonicityAudit.DyadicP2ModeOneTailMonotonicity.coarseLeFineSquare
#print axioms YMGap.Continuum.P2DyadicFusionMonotonicityAudit.DyadicP2ModeOneTailMonotonicity.toPhysicalMonotoneInput
