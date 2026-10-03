/-
# Actual terminal-depth payment in the COMPLETE original signed cost

The existing signed ceiling remains available with its favorable drift.
This alternative pays only the boundary drift by the SAME surviving norm;
the exact Rmixed-Rdiagonal Taylor difference is retained. Terminal depth
and reciprocal degree have separate computed tolerance onsets. No useful
bulk/norm comparison or changing-family uniformity is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepSignedCost
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalDrift
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRelativeEnergy

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepDriftPaidCost

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison (comparisonEta)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalEnergy
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalDrift
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRelativeEnergy
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepConditionalEnergy
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepSignedCost
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor (pairRemainder)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
  (relativeCutoff headCutoff_le_relativeCutoff)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage weightedMass

/-- The literal bulk part of the previous signed ceiling. BOTH Taylor
remainders remain signed; this is computed data, not a supplied estimate. -/
def originalBlockLastStepBulkBudget {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : relativeCutoff w 32 ≤ K)
    (n r : Nat) (psi : RatPoly) (k : Nat) : Q' :=
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := terminalMessage w K width (n+(r+1))
  let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi k
  let q := projectedEndpointSource w K width A
  weightedMass w K width (polyMul A A) *
    ((1-w)*originalBlockLastStepAngularBudget hw0 hw1 K width hK n r psi k +
      (pairRemainder (N width-1) w K q (polyMul q (polyMul phi phi)) +
        -(pairRemainder (N width-1) w K (polyMul q phi) (polyMul q phi))))

private theorem signedBudget_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (psi : RatPoly) (k : Nat)
    (bound : Q')
    (hd : boundaryDrift w K width (terminalMessage w K width (n+(r+1)))
      (blockConditionalRatio hw0 hw1 K width
        (Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK) n (r+1) psi k) ≤ bound) :
    originalBlockLastStepSignedBudget hw0 hw1 K width hK n r psi k ≤
      originalBlockLastStepBulkBudget hw0 hw1 K width hK n r psi k + bound := by
  dsimp only [originalBlockLastStepSignedBudget, originalBlockLastStepBulkBudget]
  exact Q'.add_le_add_left _ _ _ hd

/-- Actual original cleared cost: the drift is paid by the surviving norm,
without a source cap or inverse. The signed bulk estimate is still OPEN. -/
theorem original_block_lastStep_driftPaid_cost_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hN : 0 < N width)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi) (k : Nat) :
    let A := terminalMessage w K width (n+(r+1))
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    clearedRayleighCost w K width A b ≤
      (originalBlockLastStepBulkBudget hw0 hw1 K width hK n r psi k +
        comparisonEta hw0 hw1 width (n+(r+1)-1) *
          weightedMass w K width (polyMul A (transferStep w K width A)) *
          weightedMass w K width (polyMul b b)) +
        (mixRate hw0 hw1 width)^k*blockEnergyErrorCoefficient w K width n (r+1) psi := by
  dsimp only
  have hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  have hd := blockConditionalRatio_boundaryDrift_abs_le hw0 hw1 K width hhead
    n (r+1) (by omega) hp k
  exact Q'.le_trans' _ _ _
    (original_block_lastStep_signedCost_le hw0 hw1 K width hK n r hN hp k)
    (Q'.add_le_add_right _ _ _ (signedBudget_le hw0 hw1 K width hK n r psi k _
      (Q'.le_trans' _ _ _ (Q'.le_abs_self _) hd)))

/-- Two computed onsets for the SAME cost: terminal depth pays relative
drift and reciprocal degree pays complete reconstruction. Their dependence
is explicit; no uniform modulus along changing nome/width is inferred. -/
theorem original_block_lastStep_driftPaid_cost_tolerance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hN : 0 < N width)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi)
    (delta epsilon : Q') (hdelta : (0 : Q') < delta) (hepsilon : (0 : Q') < epsilon)
    (hdepth : blockConditionalDriftDepthCutoff hw0 hw1 width delta ≤ n+(r+1)-1)
    (k : Nat)
    (hk : blockEnergyErrorCutoff hw0 hw1 K width n (r+1) psi epsilon ≤ k) :
    let A := terminalMessage w K width (n+(r+1))
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    clearedRayleighCost w K width A b ≤
      (originalBlockLastStepBulkBudget hw0 hw1 K width hK n r psi k +
        delta * weightedMass w K width (polyMul A (transferStep w K width A)) *
          weightedMass w K width (polyMul b b)) + epsilon := by
  dsimp only
  have hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  have hd := blockConditionalRatio_boundaryDrift_tolerance hw0 hw1 K width hhead
    n (r+1) (by omega) hp delta hdelta k hdepth
  exact Q'.le_trans' _ _ _
    (original_block_lastStep_signedCost_tolerance hw0 hw1 K width hK n r hN
      hp epsilon hepsilon k hk)
    (Q'.add_le_add_right _ _ _ (signedBudget_le hw0 hw1 K width hK n r psi k _
      (Q'.le_trans' _ _ _ (Q'.le_abs_self _) hd)))

/-- Both errors are paid in SAME-norm currency. The TWO computed onsets
depend only on fixed nome/width and their tolerances, not source, depth or
heat cutoff. The actual signed bulk still needs a useful family estimate. -/
theorem original_block_lastStep_driftPaid_cost_relative_tolerance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hN : 0 < N width)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi)
    (delta epsilon : Q') (hdelta : (0 : Q') < delta) (hepsilon : (0 : Q') < epsilon)
    (hdepth : blockConditionalDriftDepthCutoff hw0 hw1 width delta ≤ n+(r+1)-1)
    (k : Nat) (hk : blockEnergyRelativeErrorCutoff hw0 hw1 width epsilon ≤ k) :
    let A := terminalMessage w K width (n+(r+1))
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    clearedRayleighCost w K width A b ≤
      (originalBlockLastStepBulkBudget hw0 hw1 K width hK n r psi k +
        delta * weightedMass w K width (polyMul A (transferStep w K width A)) *
          weightedMass w K width (polyMul b b)) +
        epsilon * (weightedMass w K width (polyMul A (transferStep w K width A)) *
          weightedMass w K width (polyMul b b)) := by
  dsimp only
  have hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  have hd := blockConditionalRatio_boundaryDrift_tolerance hw0 hw1 K width hhead
    n (r+1) (by omega) hp delta hdelta k hdepth
  have he := blockEnergyError_relative_budget_tolerance hw0 hw1 K width hhead
    n (r+1) (by omega) hp epsilon hepsilon k hk
  exact Q'.le_trans' _ _ _
    (original_block_lastStep_signedCost_le hw0 hw1 K width hK n r hN hp k)
    (Q'.add_le_add (signedBudget_le hw0 hw1 K width hK n r psi k _
      (Q'.le_trans' _ _ _ (Q'.le_abs_self _) hd)) he)

#print axioms originalBlockLastStepBulkBudget
#print axioms original_block_lastStep_driftPaid_cost_le
#print axioms original_block_lastStep_driftPaid_cost_tolerance
#print axioms original_block_lastStep_driftPaid_cost_relative_tolerance

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepDriftPaidCost
