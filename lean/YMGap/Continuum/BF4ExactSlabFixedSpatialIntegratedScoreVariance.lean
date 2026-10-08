/-
# Centered integrated-link score bound for the ORIGINAL odd marginal

The selected active link is moved to the Haar head. The full weight is still
V*g_n*g_(n+1), with both terminal messages and all shared tail variables.
The two positive score tilts produce a bound by its literal conditional
variance determinant, without an extra squared conditional mass or inverse.

The constant is explicit and nome-dependent. This local conditional estimate
does not produce a changing-family innovation reserve or a physical gap.
-/

import YMGap.Continuum.SU2QuaternionIntegratedScoreVariance
import YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalRelativeBound
import YMGap.Continuum.BF4ExactSlabFixedSpatialRelativeWardBound
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
import YMGap.Continuum.BF4DyadicWilsonSquare

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialIntegratedScoreVariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex (reindex_supported)
open YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica (determinant)
open YMGap.Continuum.SU2QuaternionIntegratedScoreVariance
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound (headCutoff_le_relativeCutoff)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredWard (frameWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalRelativeBound (frameRelativeBound)
open YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointRelativeBound (endpointRelativeCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialRelativeWardBound (marginalScoreCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4DyadicWilsonSquare (paddedSquare)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight terminalMessage activeBlocks

/-- The score acts in the integrated selected link, not an output-tail
direction. Every remaining coordinate survives as a polynomial variable.
The negative first-moment square is kept in the conditional determinant. -/
def original_marginal_integratedScore_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width n : Nat) (hK : endpointRelativeCutoff w ≤ K)
    (selected : Z4Link) (hl : selected ∈ baseLinks width)
    (hs : (baseLinks width).idxOf selected ∈ activeBlocks width)
    {i j : Nat} (hi : i < 4) (hj : j < 4)
    (p : RatPoly) (_hp : SupportedQuaternionBlocks (N width) p) :
    let swap := headSwapBlockInvolution (N width) ((baseLinks width).idxOf selected)
      (List.idxOf_lt_length_of_mem hl)
    let W := frameWeight w K width n swap
    let f := reindexQuaternionPolynomial swap p
    let score := partialHaarHeads 1 (polyMul (angularDerivative i j W) f)
    Certificate (N width-1) (polyAdd
      (polyMul (cap (marginalScoreCap w*marginalScoreCap w)) (determinant 1 W f))
      (polyNeg (polyMul score score))) := by
  dsimp only
  let swap := headSwapBlockInvolution (N width) ((baseLinks width).idxOf selected)
    (List.idxOf_lt_length_of_mem hl)
  let W := frameWeight w K width n swap
  let f := reindexQuaternionPolynomial swap p
  have hN : N width-1+1 = N width := by
    have := List.idxOf_lt_length_of_mem hl
    omega
  let P := frameRelativeBound hw0 hw1 K width n hK selected hl hs hi hj
  have hf : SupportedQuaternionBlocks (N width) f := reindex_supported swap p
  have hW : SupportedQuaternionBlocks (N width) W := by
    exact reindex_supported swap _
  have P' : QuaternionHaarRelativeAngularBound.RelativeBound (N width-1+1) i j W
      (marginalScoreCap w) := by
    rw [hN]
    exact P
  have hW' : SupportedQuaternionBlocks (N width-1+1) W := by rw [hN]; exact hW
  have hf' : SupportedQuaternionBlocks (N width-1+1) f := by rw [hN]; exact hf
  simpa only [Nat.mul_zero, Nat.zero_add] using
    integratedAngularScore_certificate (N width-1) 1 0 i j
      (by decide) hi hj W f (marginalScoreCap w) hW' hf'
      (by simpa only [Nat.mul_zero, Nat.zero_add] using P')

/-- Concrete original square source, with the SAME chronological OWN center.
No source mean or conditional normalizer is replaced by bare Haar data. -/
def paddedSquare_own_integratedScore_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width n scale : Nat) (hK : endpointRelativeCutoff w ≤ K)
    (hwidth : 2^scale < width)
    (selected : Z4Link) (hl : selected ∈ baseLinks width)
    (hs : (baseLinks width).idxOf selected ∈ activeBlocks width)
    {i j : Nat} (hi : i < 4) (hj : j < 4) :
    let hhead := Nat.le_trans
      (BF4ExactSlabFixedSpatialRelativeWardBound.headCutoff_le_endpointRelativeCutoff w) hK
    let p := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let c := middleRatio hw0 hw1 K width hhead (n+1) n p
    let swap := headSwapBlockInvolution (N width) ((baseLinks width).idxOf selected)
      (List.idxOf_lt_length_of_mem hl)
    let W := frameWeight w K width n swap
    let f := reindexQuaternionPolynomial swap (shifted p c)
    let score := partialHaarHeads 1 (polyMul (angularDerivative i j W) f)
    Certificate (N width-1) (polyAdd
      (polyMul (cap (marginalScoreCap w*marginalScoreCap w)) (determinant 1 W f))
      (polyNeg (polyMul score score))) :=
  original_marginal_integratedScore_certificate hw0 hw1 K width n hK selected hl hs hi hj
    _ (shifted_supported (sourceCharacter_supported width
      (paddedSquare scale width hwidth).edges 1) _)

end YMGap.Continuum.BF4ExactSlabFixedSpatialIntegratedScoreVariance

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntegratedScoreVariance.original_marginal_integratedScore_certificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntegratedScoreVariance.paddedSquare_own_integratedScore_certificate
