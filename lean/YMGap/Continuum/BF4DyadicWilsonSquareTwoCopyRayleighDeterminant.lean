/-
# The chronological OWN-centered square in the signed two-copy determinant

The actual padded-square source, depth-n OWN mean and half-smoothed block
message are retained literally. The two output copies have the original V
once each; first/second differences use the same original one-step transfer.
Their signed pairing is twice the existing cleared block Rayleigh cost.

This supplies an alternative exact form for the missing signed relative
estimate, not that estimate or a new survival reserve. All physical,
canonical OS, scaling, continuum and Clay endpoints remain open.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTwoCopyRayleighDeterminant
import YMGap.Continuum.BF4DyadicWilsonSquareExactBlockHeatDefect

namespace YMGap.Continuum.BF4DyadicWilsonSquareTwoCopyRayleighDeterminant

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit (clearedRayleighCost)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4DyadicWilsonSquare (side paddedSquare)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoCopyRayleighDeterminant

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks terminalMessage middleRatio originalBlockTransfer clearedRayleighCost

/-- SAME square, chronological OWN center and filtered block norm as the
current determinant frontier. No later mean is substituted into b. -/
theorem paddedSquare_own_twoCopy_determinant {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (n t scale : Nat) (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let c := middleRatio hw0 hw1 K width hK (n+1) n f
    let A := terminalMessage w K width (n+t)
    let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) (shifted f c))
    twoCopyPair w K width (symmetricProduct width A b)
      (polyAdd (firstDifference w K width A b) (polyNeg (secondDifference w K width A b))) ≈
      clearedRayleighCost w K width A b + clearedRayleighCost w K width A b := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let c := middleRatio hw0 hw1 K width hK (n+1) n f
  have hf : SupportedQuaternionBlocks (N width) f :=
    sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hg := terminalMessage_supported w K width n
  have hp := shifted_supported hf c
  have hb : SupportedQuaternionBlocks (N width)
      (originalBlockTransfer w K width t (polyMul (terminalMessage w K width n)
        (shifted f c))) := by
    unfold originalBlockTransfer
    exact iterateStep_supported (kineticWeight_supported w K width)
      (spatialWeight_supported w K width) t (supported_polyMul hg hp)
  exact antisymmetric_pairing_determinant w K width
    (terminalMessage_supported w K width (n+t)) hb

#print axioms paddedSquare_own_twoCopy_determinant

end YMGap.Continuum.BF4DyadicWilsonSquareTwoCopyRayleighDeterminant
