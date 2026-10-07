/-
# Three paired directions give the SAME original direct-score budget

The paired score-square identity is used on the actual terminal A and
transmitted b, not on a replacement action or unweighted heat operator.
The original Vbar^2*G^2 multiplier, active blocks, reciprocal degree and
sigma remain literal. This is an equality of finite rational budgets,
not a new curvature bound, completed OS estimate or physical mass gap.

Consumer: the existing exactScoreAngularBudget and its signed-cost route.
This removes an energy-conversion obligation for a future three-direction
one-sided producer; no geodesic or heat-equation hypothesis is assumed.
-/

import YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepExactScoreBudget

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPairedScoreBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail (finSum finSum_eqv_congr)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepExactScoreBudget (exactScoreAngularBudget)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient (conditionalScore)
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
  (relativeCutoff headCutoff_le_relativeCutoff)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
  (haar_six sixValue_mul_left)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks terminalMessage

/-- The literal original budget, expressed as three paired score squares.
No source factorization, positivity or hemisphere premise is introduced. -/
def pairedScoreAngularBudget (sigma : Q') {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (psi : RatPoly) (k : Nat) : Q' :=
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := terminalMessage w K width (n+(r+1))
  let b := originalBlockTransfer w K width (r+1)
    (polyMul (terminalMessage w K width n) psi)
  let G := blockReciprocal hw0 hw1 K width hhead n (r+1) k
  let Vbar := spatialFringeMass w K width
  finSum (fun s => if s ∈ activeBlocks width then
    (1+sigma)*quaternionHaar (N width)
      (polyMul (polyMul (polyMul Vbar Vbar) (polyMul G G))
        (threeSquare (pairedScorePlus s A b)))
    else 0) (N width)

/-- Exact equality on the SAME terminal window and arbitrary original source.
The equality is coefficient-exact before Haar integration and does not need
positivity of the output multiplier or an inverse of A. -/
theorem pairedScoreAngularBudget_eq_exact (sigma : Q') {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (psi : RatPoly) (k : Nat) :
    pairedScoreAngularBudget sigma hw0 hw1 K width hK n r psi k ≈
      exactScoreAngularBudget sigma hw0 hw1 K width hK n r psi k := by
  unfold pairedScoreAngularBudget exactScoreAngularBudget
  apply finSum_eqv_congr
  intro s
  split
  · exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (1+sigma) _ _
        (Q'.eqv_trans _ _ _
          (haar_of_coeff ((plusSquare_eq_sixScoreSquare s _ _).mul_left _))
          (haar_six (N width) _ _)))
      (sixValue_mul_left (1+sigma) _)
  · exact Q'.eqv_refl _

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPairedScoreBudget

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPairedScoreBudget.pairedScoreAngularBudget_eq_exact
