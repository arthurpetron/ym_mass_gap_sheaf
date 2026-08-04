/- Generated proof-carrying checkpoints for BF4 mask 0x008938.
   Regenerate with computations/generate_bf4_forest_gauge_staged.py. -/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeMask008938

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge
open YMGap.Continuum.SU2QuaternionBivalentHaarContraction
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

def stage0 := surfaceForestGaugeFactors 35128

def stage1 : List RatPoly :=
  [[([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], { num := 4, denPred := 3 })],
    [([1], { num := 2, denPred := 0 })],
    [([0, 0, 0, 0, 1], { num := 2, denPred := 0 })],
    [([0, 0, 0, 0, 0, 0, 0, 0, 1], { num := 2, denPred := 0 })],
    [([1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1], { num := -2, denPred := 0 }),
      ([0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], { num := -2, denPred := 0 }),
      ([0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], { num := -2, denPred := 0 }),
      ([1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], { num := -2, denPred := 0 }),
      ([1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1], { num := 2, denPred := 0 }),
      ([0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], { num := -2, denPred := 0 }),
      ([1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1], { num := 2, denPred := 0 }),
      ([0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1], { num := -2, denPred := 0 }),
      ([1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1], { num := -2, denPred := 0 }),
      ([0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1], { num := -2, denPred := 0 }),
      ([1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1], { num := -2, denPred := 0 }),
      ([0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1], { num := -2, denPred := 0 }),
      ([0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1], { num := -2, denPred := 0 }),
      ([0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1], { num := 2, denPred := 0 }),
      ([0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1], { num := -2, denPred := 0 }),
      ([1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1], { num := -2, denPred := 0 }),
      ([0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1], { num := -2, denPred := 0 }),
      ([1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1], { num := -2, denPred := 0 }),
      ([0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1], { num := -2, denPred := 0 }),
      ([0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1], { num := -2, denPred := 0 }),
      ([0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1], { num := 2, denPred := 0 }),
      ([0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1], { num := 2, denPred := 0 }),
      ([0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1], { num := -2, denPred := 0 }),
      ([1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1], { num := -2, denPred := 0 }),
      ([0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1], { num := 2, denPred := 0 }),
      ([0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1], { num := -2, denPred := 0 }),
      ([1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1], { num := -2, denPred := 0 }),
      ([0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1], { num := -2, denPred := 0 }),
      ([0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1], { num := -2, denPred := 0 }),
      ([0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1], { num := 2, denPred := 0 }),
      ([0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1], { num := -2, denPred := 0 })]]

theorem stage1_exact :
    compactBivalentFactorizedHeadStep stage0 = stage1 := by
  decide

def stage2 : List RatPoly :=
  [[([0, 0, 0, 1, 0, 0, 0, 1, 1], { num := -4, denPred := 3 }),
      ([0, 0, 0, 1, 0, 0, 1, 0, 0, 1], { num := -4, denPred := 3 }),
      ([0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1], { num := 4, denPred := 3 }),
      ([0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1], { num := 4, denPred := 3 }),
      ([0, 0, 1, 0, 0, 0, 0, 1, 0, 1], { num := 4, denPred := 3 }),
      ([0, 0, 1, 0, 0, 0, 1, 0, 1], { num := -4, denPred := 3 }),
      ([0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1], { num := -4, denPred := 3 }),
      ([0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1], { num := 4, denPred := 3 }),
      ([0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1], { num := -4, denPred := 3 }),
      ([0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], { num := 4, denPred := 3 }),
      ([0, 1, 0, 0, 0, 1, 0, 0, 1], { num := -4, denPred := 3 }),
      ([0, 1, 0, 0, 1, 0, 0, 0, 0, 1], { num := 4, denPred := 3 }),
      ([1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1], { num := 4, denPred := 3 }),
      ([1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1], { num := 4, denPred := 3 }),
      ([1, 0, 0, 0, 0, 1, 0, 0, 0, 1], { num := 4, denPred := 3 }),
      ([1, 0, 0, 0, 1, 0, 0, 0, 1], { num := 4, denPred := 3 })],
    [([0, 0, 0, 0, 0, 0, 0, 0, 1], { num := 4, denPred := 3 })],
    [([1], { num := 2, denPred := 0 })],
    [([0, 0, 0, 0, 1], { num := 2, denPred := 0 })]]

theorem stage2_exact :
    compactBivalentFactorizedHeadStep stage1 = stage2 := by
  decide

def stage3 : List RatPoly :=
  [[([0, 0, 0, 1, 0, 0, 0, 1], { num := 8, denPred := 15 }),
      ([0, 0, 1, 0, 0, 0, 1], { num := 8, denPred := 15 }),
      ([0, 1, 0, 0, 0, 1], { num := 8, denPred := 15 }),
      ([1, 0, 0, 0, 1], { num := 8, denPred := 15 })],
    [([0, 0, 0, 0, 1], { num := 4, denPred := 3 })],
    [([1], { num := 2, denPred := 0 })]]

theorem stage3_exact :
    compactBivalentFactorizedHeadStep stage2 = stage3 := by
  decide

def stage4 : List RatPoly :=
  [[([1], { num := 16, denPred := 63 })],
    [([1], { num := 4, denPred := 3 })]]

theorem stage4_exact :
    compactBivalentFactorizedHeadStep stage3 = stage4 := by
  decide

def stage5 : List RatPoly :=
  [[([], { num := 64, denPred := 1023 })]]

theorem stage5_exact :
    compactBivalentFactorizedHeadStep stage4 = stage5 := by
  decide

theorem contraction5_exact :
    compactBivalentFactorizedHaarContract 5 stage0 =
      factorProduct (nonUnitFactors stage5) := by
  change compactBivalentFactorizedHaarContract 4
      (compactBivalentFactorizedHeadStep stage0) = _
  rw [stage1_exact]
  change compactBivalentFactorizedHaarContract 3
      (compactBivalentFactorizedHeadStep stage1) = _
  rw [stage2_exact]
  change compactBivalentFactorizedHaarContract 2
      (compactBivalentFactorizedHeadStep stage2) = _
  rw [stage3_exact]
  change compactBivalentFactorizedHaarContract 1
      (compactBivalentFactorizedHeadStep stage3) = _
  rw [stage4_exact]
  change compactBivalentFactorizedHaarContract 0
      (compactBivalentFactorizedHeadStep stage4) = _
  rw [stage5_exact]
  rfl

theorem forestGaugeHaar_exact :
    surfaceForestGaugeHaar 35128 ≈
      surfaceTopologicalHaarAmplitude 35128 := by
  unfold surfaceForestGaugeHaar compactBivalentFactorizedHaar
  change quaternionHaar 0
      (compactBivalentFactorizedHaarContract 5 stage0) ≈ _
  rw [contraction5_exact]
  decide

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeMask008938

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeMask008938.forestGaugeHaar_exact
