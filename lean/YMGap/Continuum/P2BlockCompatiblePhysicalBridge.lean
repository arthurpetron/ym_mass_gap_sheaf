/-
Track 11.7-fusion / R3b -- the block-compatible p=2 physical bridge.

This module installs the replacement cutoff/weight schedule in the reviewed
`CanonicalBulkControl` and fusion-spectrum dictionaries.  It leaves exactly
two honest analytic carriers:

* the division-free coefficient tail that constructs `CanonicalBulkControl`;
* the normalized mode-one square comparison from scale `k = 2` onward.

The first two square cells are already kernel-checked.  Once the tail is
supplied, the same square comparison propagates a one-half mode-one floor, so
there is no independent all-scale floor hypothesis.  The quotient compiler
then reaches the actual `BlockingStep.Phi` defect identity on the
spectrum-defined trajectory.  Summability of the resulting defects remains
the later physical-margin problem.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatibleHeatPower
import YMGap.Continuum.P2BlockCompatibleScheduleCells
import YMGap.Continuum.P2RetunedFusionPhysicalMode
import YMGap.Continuum.P2RetunedFusionReferenceGap

namespace YMGap.Continuum.P2BlockCompatiblePhysicalBridge

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.BlockingStepFrontier
open YMGap.Continuum.FusionKernelStatement
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleScheduleCells
open YMGap.Continuum.P2RetunedBlockingDictionary
open YMGap.Continuum.P2RetunedFusionDefectPower
open YMGap.Continuum.P2RetunedFusionPhysicalMode
open YMGap.Continuum.P2RetunedFusionPowerCertificate
open YMGap.Continuum.P2RetunedFusionReferenceGap
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SpectralLocalizationCrux

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact replacement control family -/

theorem blockWeight_near_continuum (k : Nat) :
    (1 : Q') - blockWeight k <= q112 :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv (one_sub_blockWeight_eqv_margin k))
    (blockMargin_le_q112 k)

/-- The sole all-scale residual needed to build the reviewed p=2
`CanonicalBulkControl` family on the block-compatible schedule. -/
structure BlockCompatibleP2CoeffTailData : Type where
  coeffTailRatio : forall k,
    P2RetunedCoeffTailRatio (blockNcut k) (blockWeight k)
      (blockWeight_nonneg k) (blockWeight_le_one k)

def BlockCompatibleP2CoeffTailData.toCoeffControlFamily
    (D : BlockCompatibleP2CoeffTailData) : P2RetunedCoeffControlFamily where
  N := blockNcut
  w := blockWeight
  hN := fun k => by
    have := blockNcut_pos k
    omega
  hw0 := blockWeight_nonneg
  hw1 := blockWeight_le_one
  hnc := blockWeight_near_continuum
  coeffTailRatio := D.coeffTailRatio

/-- The genuine reviewed control family after compiling the raw coefficient
tail. -/
def BlockCompatibleP2CoeffTailData.toControlFamily
    (D : BlockCompatibleP2CoeffTailData) : P2RetunedControlFamily :=
  D.toCoeffControlFamily.toTailFamily

/-! ## 2. Two checked head cells plus one structural tail -/

/-- Transport a raw mode-one square inequality into any compiled replacement
control family.  Proof fields in `CanonicalBulkControl` do not enter. -/
theorem fusionModeOne_coarse_le_fineSquare_of_raw
    (D : BlockCompatibleP2CoeffTailData) (k : Nat)
    (hraw : blockRawModeOne k <= qpow (blockRawModeOne (k + 1)) 2) :
    fusionModeQ D.toControlFamily modeOne k <=
      qpow (fusionModeQ D.toControlFamily modeOne (k + 1)) 2 := by
  have hcoarse := fusionModeOne_eqv_p2VacNorm D.toControlFamily k
  have hfine := fusionModeOne_eqv_p2VacNorm D.toControlFamily (k + 1)
  have hfinePower := BondMovingRelResidual.qpow_eqv_congr_base hfine 2
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hcoarse)
    (Q'.le_trans' _ _ _ hraw (Q'.ge_of_eqv hfinePower))

theorem fusionModeOne_step_zero (D : BlockCompatibleP2CoeffTailData) :
    fusionModeQ D.toControlFamily modeOne 0 <=
      qpow (fusionModeQ D.toControlFamily modeOne 1) 2 :=
  fusionModeOne_coarse_le_fineSquare_of_raw D 0 blockRaw_step_zero

theorem fusionModeOne_step_one (D : BlockCompatibleP2CoeffTailData) :
    fusionModeQ D.toControlFamily modeOne 1 <=
      qpow (fusionModeQ D.toControlFamily modeOne 2) 2 :=
  fusionModeOne_coarse_le_fineSquare_of_raw D 1 blockRaw_step_one

/-- The only remaining normalized-amplitude comparison.  Its finite prefix is
not repeated: the structural proof starts at `k = 2`. -/
structure BlockCompatibleP2ModeOneTailMonotonicity : Type where
  tail : forall k, 2 <= k ->
    blockRawModeOne k <= qpow (blockRawModeOne (k + 1)) 2

/-- Combine the two exact head cells with the one all-scale tail theorem. -/
theorem BlockCompatibleP2ModeOneTailMonotonicity.coarseLeFineSquare
    (M : BlockCompatibleP2ModeOneTailMonotonicity)
    (D : BlockCompatibleP2CoeffTailData) (k : Nat) :
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

/-! ## 3. Derive the all-scale half floor -/

private theorem blockScaledModeZero_half :
    half <= blockScaledModeZero := by
  decide

theorem blockRawModeZero_half : half <= blockRawModeOne 0 :=
  Q'.le_trans' _ _ _ blockScaledModeZero_half
    (Q'.ge_of_eqv blockRawModeZero_eqv)

theorem fusionModeOne_zero_half (D : BlockCompatibleP2CoeffTailData) :
    half <= fusionModeQ D.toControlFamily modeOne 0 := by
  have hzero := fusionModeOne_eqv_p2VacNorm D.toControlFamily 0
  exact Q'.le_trans' _ _ _ blockRawModeZero_half (Q'.ge_of_eqv hzero)

/-- The square comparison propagates the base half-floor automatically:
`half <= coarse <= fine^2 <= fine`. -/
theorem BlockCompatibleP2ModeOneTailMonotonicity.modeOneHalf
    (M : BlockCompatibleP2ModeOneTailMonotonicity)
    (D : BlockCompatibleP2CoeffTailData) (k : Nat) :
    half <= fusionModeQ D.toControlFamily modeOne k := by
  induction k with
  | zero => exact fusionModeOne_zero_half D
  | succ k ih =>
      have hstep := M.coarseLeFineSquare D k
      have hfine := fusionModeOne_range D.toControlFamily (k + 1)
      have hsq : qpow (fusionModeQ D.toControlFamily modeOne (k + 1)) 2 <=
          fusionModeQ D.toControlFamily modeOne (k + 1) := by
        simpa using
          (qpow_succ_le_self hfine.1 hfine.2 1)
      exact Q'.le_trans' _ _ _ ih (Q'.le_trans' _ _ _ hstep hsq)

/-! ## 4. Compile to the genuine physical map -/

/-- All quotient data are derived from the two honest residual carriers. -/
def BlockCompatibleP2ModeOneTailMonotonicity.toQuotientData
    (M : BlockCompatibleP2ModeOneTailMonotonicity)
    (D : BlockCompatibleP2CoeffTailData)
    {B : BlockingStep (fusionSeparator D.toControlFamily modeOne)} :
    SpectrumPinnedP2QuotientDefectPowerData
      1 D.toControlFamily modeOne B where
  physicalMode :=
    P2RetunedFusionPhysicalMode.P2RetunedControlFamily.modeOnePhysical
      D.toControlFamily
  coarseNonneg := fun k => (fusionModeOne_range D.toControlFamily k).1
  finePowerPos := fun k => by
    have hhalf := M.modeOneHalf D (k + 1)
    have hpos : (0 : Q') <
        fusionModeQ D.toControlFamily modeOne (k + 1) :=
      BondMovingRelResidual.q_lt_of_lt_of_le
        (by decide : (0 : Q') < half) hhalf
    exact BondMovingScaledNorm.qpow_pos hpos 2
  coarseLeFinePower := M.coarseLeFineSquare D
  halfFinePowerLeCoarse := fun k => by
    have hfine := fusionModeOne_range D.toControlFamily (k + 1)
    have hpow : qpow (fusionModeQ D.toControlFamily modeOne (k + 1)) 2 <=
        (1 : Q') := qpow_le_one hfine.1 hfine.2 2
    have hscale := Q'.mul_le_mul_of_nonneg_left _ _ half hpow half_nonneg
    exact Q'.le_trans' _ _ _ hscale
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.mul_one_eqv half))
        (M.modeOneHalf D k))

/-- The replacement schedule reaches the actual `BlockingStep.Phi` defect
identity.  `finePin` is definitional and `imagePin` is `BlockingStep.step`;
neither is an added hypothesis here. -/
theorem BlockCompatibleP2ModeOneTailMonotonicity.blockDefectPowerOnTrajectory
    (M : BlockCompatibleP2ModeOneTailMonotonicity)
    (D : BlockCompatibleP2CoeffTailData)
    {B : BlockingStep (fusionSeparator D.toControlFamily modeOne)} :
    IsBlockDefectPowerOnTrajectory 1
      (fusionSeparator D.toControlFamily modeOne) B.Φ
      (M.toQuotientData D (B := B)).toCrossMul.factor :=
  (M.toQuotientData D (B := B)).toCrossMul.blockDefectPowerOnTrajectory

/-- Every canonical quotient factor lies in the certified half-loss window.
Summability of these losses is deliberately not claimed here. -/
theorem BlockCompatibleP2ModeOneTailMonotonicity.factorLossLeHalf
    (M : BlockCompatibleP2ModeOneTailMonotonicity)
    (D : BlockCompatibleP2CoeffTailData)
    {B : BlockingStep (fusionSeparator D.toControlFamily modeOne)}
    (k : Nat) :
    (1 : Q') - (M.toQuotientData D (B := B)).toCrossMul.factor k <= half :=
  (M.toQuotientData D (B := B)).factorLossLeHalf k

#print axioms blockWeight_near_continuum
#print axioms fusionModeOne_coarse_le_fineSquare_of_raw
#print axioms BlockCompatibleP2ModeOneTailMonotonicity.coarseLeFineSquare
#print axioms BlockCompatibleP2ModeOneTailMonotonicity.modeOneHalf
#print axioms BlockCompatibleP2ModeOneTailMonotonicity.toQuotientData
#print axioms BlockCompatibleP2ModeOneTailMonotonicity.blockDefectPowerOnTrajectory
#print axioms BlockCompatibleP2ModeOneTailMonotonicity.factorLossLeHalf

end YMGap.Continuum.P2BlockCompatiblePhysicalBridge
