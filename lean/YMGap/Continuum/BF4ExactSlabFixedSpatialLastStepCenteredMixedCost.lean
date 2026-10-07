/-
# The actual conditional observable reaches the centered mixed remainder bound

Reuse the direct exact score, without conditional Jensen or a repeated global
score cap. Shift ONLY the remainder evaluation. The finite reciprocal ratio
of psi-c is NOT assumed to be phi-c. All original terminal messages, spatial
weights, partitions and already-paid errors remain unchanged.

The favorable negative diagonal remainder is retained. The resulting mixed
budget still depends on the actual q, phi, nome, width,
depth and reciprocal degree. No useful AF-relative bound, all-vector RG
comparison, physical scaling or continuum mass gap is supplied.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepExactScoreCost
import YMGap.Continuum.SU2QuaternionCenteredSignedRemainder

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepCenteredMixedCost

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass weightedMass_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy (endpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRelativeEnergy
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalDrift
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit (clearedRayleighCost)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepAsymmetricEnergy (asymmetricCorrectionCostCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepExactScoreBudget (exactScoreAngularBudget)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepExactScoreCost
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor (pairBudget pairRemainder)
open YMGap.Continuum.SU2QuaternionCenteredSignedRemainder
open YMGap.Continuum.SU2HeatCutoffCasimirBound (sufficientCutoff)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound (relativeCutoff headCutoff_le_relativeCutoff)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage projectedEndpointSource

/-- The ORIGINAL direct score and a single centered mixed remainder budget,
with the actual favorable negative diagonal remainder RETAINED.
The center is explicit data, not an assumed new source or vacuum law. -/
def centeredMixedBulk (sigma : Q') {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (psi : RatPoly) (k : Nat) (c : Q') : Q' :=
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := terminalMessage w K width (n+(r+1))
  let q := projectedEndpointSource w K width A
  let phi := shifted (blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi k) c
  weightedMass w K width (polyMul A A)*
    ((1-w)*exactScoreAngularBudget sigma hw0 hw1 K width hK n r psi k +
      (((1-w)*(1-w))*pairBudget (N width-1) q (polyMul q (polyMul phi phi)) +
        -(pairRemainder (N width-1) w K (polyMul q phi) (polyMul q phi))))

/-- A genuine inequality on the actual q/conditional-ratio pair. The
additional quadratic cutoff guard is explicit, not inferred from hK. -/
theorem exactScoreSignedBulk_le_centeredMixed (sigma : Q') {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (hquad : sufficientCutoff w ≤ K)
    (n r : Nat) (hN : 0 < N width) {psi : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) psi) (k : Nat) (c : Q') :
    exactScoreSignedBulk sigma hw0 hw1 K width hK n r psi k ≤
      centeredMixedBulk sigma hw0 hw1 K width hK n r psi k c := by
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := terminalMessage w K width (n+(r+1))
  let q := projectedEndpointSource w K width A
  let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi k
  have hA := terminalMessage_supported w K width (n+(r+1))
  have hq : SupportedQuaternionBlocks (N width) q := by
    unfold q projectedEndpointSource endpointSource
    exact familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width) hA)
  have hf := blockConditionalRatio_supported hw0 hw1 K width hhead n (r+1) hp k
  have hsize : N width-1+1 = N width := Nat.sub_add_cancel hN
  have hr := signedRemainder_le_centered_mixed_minus_diagonal (N width-1)
    (Q'.le_of_lt hw0) hw1 K hquad q phi
    (by simpa only [hsize] using hq) (by simpa only [hsize] using hf) c
  have hZ := weightedMass_nonnegative hw0 hw1 K width hhead (Certificate.square A hA)
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.add_le_add_left _ _ _ hr) hZ

/-- COMPLETE original cleared Rayleigh cost with the actual direct score,
centered mixed budget, and unchanged source-relative error payments. This
is still a ONE-step pairing cost, not a two-step squared-norm comparison. -/
theorem original_block_centered_mixed_cost_relative_tolerance (sigma : Q')
    (hsigma : (0 : Q') < sigma) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (hquad : sufficientCutoff w ≤ K)
    (n r : Nat) (hN : 0 < N width) {psi : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) psi) (c delta epsilon zeta : Q')
    (hd : (0 : Q') < delta) (he : (0 : Q') < epsilon) (hz : (0 : Q') < zeta)
    (hdepth : blockConditionalDriftDepthCutoff hw0 hw1 width delta ≤ n+(r+1)-1)
    (k : Nat) (hk : blockEnergyRelativeErrorCutoff hw0 hw1 width epsilon ≤ k+1)
    (hc : asymmetricCorrectionCostCutoff sigma hsigma hw0 hw1 width zeta ≤ k) :
    let A := terminalMessage w K width (n+(r+1))
    let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
    clearedRayleighCost w K width A b ≤
      centeredMixedBulk sigma hw0 hw1 K width hK n r psi (k+1) c +
        ((zeta+delta)+epsilon)*(weightedMass w K width (polyMul A (transferStep w K width A))*
          weightedMass w K width (polyMul b b)) := by
  exact Q'.le_trans' _ _ _
    (original_block_exact_score_cost_relative_tolerance sigma hsigma hw0 hw1 K width hK
      n r hN hp delta epsilon zeta hd he hz hdepth k hk hc)
    (Q'.add_le_add_right _ _ _ (exactScoreSignedBulk_le_centeredMixed sigma hw0 hw1 K width
      hK hquad n r hN hp (k+1) c))

end YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepCenteredMixedCost

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepCenteredMixedCost.centeredMixedBulk
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepCenteredMixedCost.exactScoreSignedBulk_le_centeredMixed
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepCenteredMixedCost.original_block_centered_mixed_cost_relative_tolerance
