/-
# ORIGINAL last-step reciprocal gradient paid by incoming prediction energy

The actual projected conditional noise in the existing gradient estimate is
bounded by the ORIGINAL incoming Dirichlet energy, through the terminal
upper bracket and spatialCeiling. The projected action square is NOT
identified with the original spatial weight. Both finite reciprocal errors
remain literally unchanged; the incoming and outgoing degrees are independent.

This is one per-plane finite estimate, not a small-energy assertion, a bound
on the signed Taylor remainders, or a changing-family survival claim.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPredictionEnergyNormalized
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioRefinement

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPredictionGradient

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredVarianceComparison
  (filteredTerminalBracket)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensity (spatialCeiling)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
  (spatialFringeMass spatialFringeMass_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepRatioRefinement
  (incomingNumerator incomingScoreErrorCoefficient original_lastStep_incomingRatio_gradient_le)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPredictionEnergyNormalized
  (lastStepNoise_projected_prediction_energy_le)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionAngularDerivative (angularDerivative)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
  (relativeCutoff relativeCap headCutoff_le_relativeCutoff)
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient (reciprocalScoreCorrection)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage

/-- The actual outgoing reciprocal gradient is controlled by incoming
prediction energy, with both original finite corrections retained. No norm
or source is inverted, and zero or signed incoming sources are allowed. -/
theorem original_lastStep_prediction_energy_gradient_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hdepth : 1 ≤ n+r)
    (s : Nat) (hs : s ∈ activeBlocks width) {i j : Nat} (hi : i < 4) (hj : j < 4)
    {psi : RatPoly} (hpsi : SupportedQuaternionBlocks (N width) psi)
    (etaYoung sigma : Q') (heta : (0 : Q') < etaYoung) (hsigma : (0 : Q') < sigma)
    (k l : Nat) :
    let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
    let a := terminalMessage w K width (n+r)
    let A := transferStep w K width a
    let b := transferStep w K width (incomingNumerator w K width n r psi)
    let phi := blockConditionalRatio hw0 hw1 K width hhead n r psi k
    let G := blockReciprocal hw0 hw1 K width hhead n (r+1) l
    let U := (filteredTerminalBracket hw0 hw1 K width hhead (n+r) 0 1 hdepth).upper
    let Vbar := spatialFringeMass w K width
    let d := polyMul A (angularDerivative (4*s+i) (4*s+j) (polyMul G b))
    let e := reciprocalScoreCorrection (4*s+i) (4*s+j) A b
      (blockWindowUpper w K width n (r+1))
      (blockWindowUpper_positive hw0 hw1 K width hhead n (r+1)) l
    quaternionHaar (N width) (polyMul (polyMul Vbar Vbar) (polyMul d d)) ≤
      (1+sigma)*((1+etaYoung)*((relativeCap w 32*relativeCap w 32)*
        (spatialCeiling w width*((2*U)*energy w K width a phi))) +
        (mixRate hw0 hw1 width)^(2*k)*incomingScoreErrorCoefficient w K width n r psi
          (polyMul (polyMul Vbar Vbar) (polyMul G G)) etaYoung heta) +
      (1+Q'.recipPos sigma hsigma)*quaternionHaar (N width)
        (polyMul (polyMul Vbar Vbar) (polyMul e e)) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let Vbar := spatialFringeMass w K width
  have MW : Certificate (N width) (polyMul Vbar Vbar) :=
    Certificate.square Vbar (spatialFringeMass_supported w K width)
  have hgrad := original_lastStep_incomingRatio_gradient_le
    hw0 hw1 K width hK n r hdepth s hs hi hj hpsi MW etaYoung sigma heta hsigma k l
  have hnoise := lastStepNoise_projected_prediction_energy_le
    hw0 hw1 K width hhead (n+r) hdepth
    (blockConditionalRatio_supported hw0 hw1 K width hhead n r hpsi k)
  dsimp only at hgrad hnoise
  have hlead := Q'.mul_le_mul_of_nonneg_left _ _
    (relativeCap w 32*relativeCap w 32) hnoise
    (SumOfSquares.q_mul_self_nonneg (relativeCap w 32))
  have hleading := Q'.mul_le_mul_of_nonneg_left _ _ (1+etaYoung) hlead
    (Q'.zero_le_add 1 etaYoung Q'.zero_le_one (Q'.le_of_lt heta))
  exact Q'.le_trans' _ _ _ hgrad
    (Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_left _ _ (1+sigma)
        (Q'.add_le_add hleading (Q'.le_of_eqv (Q'.eqv_refl _)))
        (Q'.zero_le_add 1 sigma Q'.zero_le_one (Q'.le_of_lt hsigma)))
      (Q'.le_of_eqv (Q'.eqv_refl _)))

#print axioms original_lastStep_prediction_energy_gradient_le

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPredictionGradient
