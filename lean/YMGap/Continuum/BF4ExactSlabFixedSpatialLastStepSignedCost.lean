/-
# Last-step paired score meets the COMPLETE original signed cost

The actual finite ratio, projected action and original energy are retained.
Only the angular first-order term is bounded by the last-step paired budget.
The negative diagonal Taylor remainder and signed boundary drift remain in
the computed ceiling; neither is replaced by an independent absolute cap.
The complete signed reconstruction error has its existing explicit modulus.
No useful changing-family relative ceiling or continuum survival is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepConditionalEnergy
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalEnergy

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepSignedCost

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalGradient
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalEnergy
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepConditionalEnergy
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceTaylor (energy_taylor_angular)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor (pairRemainder)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound (relativeCutoff headCutoff_le_relativeCutoff)
open YMGap.Continuum.QuaternionHaarSquareCertificate (Certificate)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage weightedMass

/-- Literal combined signed ceiling. Its negative diagonal remainder and
drift are not discarded; all dependence remains explicit in its arguments. -/
def originalBlockLastStepSignedBudget {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : relativeCutoff w 32 ≤ K)
    (n r : Nat) (psi : RatPoly) (k : Nat) : Q' :=
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := terminalMessage w K width (n+(r+1))
  let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi k
  let q := projectedEndpointSource w K width A
  weightedMass w K width (polyMul A A) *
    ((1-w)*originalBlockLastStepAngularBudget hw0 hw1 K width hK n r psi k +
      (pairRemainder (N width-1) w K q (polyMul q (polyMul phi phi)) +
        -(pairRemainder (N width-1) w K (polyMul q phi) (polyMul q phi)))) +
    boundaryDrift w K width A phi

private theorem energy_drift_le_budget {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hN : 0 < N width)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let A := terminalMessage w K width (n+(r+1))
    let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi k
    weightedMass w K width (polyMul A A)*energy w K width A phi +
      boundaryDrift w K width A phi ≤
      originalBlockLastStepSignedBudget hw0 hw1 K width hK n r psi k := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := terminalMessage w K width (n+(r+1))
  let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi k
  have hA := terminalMessage_supported w K width (n+(r+1))
  have ht := energy_taylor_angular w K width A phi hA
    (blockConditionalRatio_supported hw0 hw1 K width hhead n (r+1) hp k) hN
    (fun i hi => blockConditionalRatio_fringe_independent hw0 hw1 K width hhead
      n (r+1) (by omega) hp k i hi)
  have ha := original_block_lastStep_weightedAngularEnergy_le hw0 hw1 K width hK
    n r hN psi hp k
  have he := Q'.le_trans' _ _ _ (Q'.le_of_eqv ht)
    (Q'.add_le_add_right _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ ha
      (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))))
  exact Q'.add_le_add_right _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ he
    (weightedMass_nonnegative hw0 hw1 K width hhead (Certificate.square A hA)))

/-- The COMPLETE original cost is bounded by the combined signed expression
and only the complete reconstruction error. No SAME-norm bound is assumed. -/
theorem original_block_lastStep_signedCost_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hN : 0 < N width)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    let A := terminalMessage w K width (n+(r+1))
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    clearedRayleighCost w K width A b ≤
      originalBlockLastStepSignedBudget hw0 hw1 K width hK n r psi k +
        (mixRate hw0 hw1 width)^k*blockEnergyErrorCoefficient w K width n (r+1) psi := by
  dsimp only
  have hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  exact Q'.le_trans' _ _ _
    (ExpNeg.le_add_of_abs_sub_le (blockConditionalRatio_energy_error_abs_le hw0 hw1
      K width hhead n (r+1) (by omega) hp k))
    (Q'.add_le_add_right _ _ _ (energy_drift_le_budget hw0 hw1 K width hK n r hN hp k))

/-- Computed absolute tolerance for the SAME combined signed-cost ceiling.
All source, width, nome and cutoff dependence of the onset stays explicit. -/
theorem original_block_lastStep_signedCost_tolerance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hN : 0 < N width)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (k : Nat)
    (hk : blockEnergyErrorCutoff hw0 hw1 K width n (r+1) psi epsilon ≤ k) :
    let A := terminalMessage w K width (n+(r+1))
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    clearedRayleighCost w K width A b ≤
      originalBlockLastStepSignedBudget hw0 hw1 K width hK n r psi k + epsilon := by
  dsimp only
  have hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  exact Q'.le_trans' _ _ _
    (ExpNeg.le_add_of_abs_sub_le (blockConditionalRatio_energy_error_tolerance hw0 hw1
      K width hhead n (r+1) (by omega) hp epsilon hepsilon k hk))
    (Q'.add_le_add_right _ _ _ (energy_drift_le_budget hw0 hw1 K width hK n r hN hp k))

#print axioms originalBlockLastStepSignedBudget
#print axioms original_block_lastStep_signedCost_le
#print axioms original_block_lastStep_signedCost_tolerance

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepSignedCost
