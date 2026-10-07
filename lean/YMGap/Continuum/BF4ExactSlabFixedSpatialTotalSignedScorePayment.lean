/-
# Total finite approximation payment, including actual transmitted null states

The original positive spatial floor reflects a zero weighted transmitted
square into genuine Haar nullity. The existing signed-score null theorem
then constructs the zero-target branch. Positive targets use the adaptive
sigma-before-degree construction. Thus no source-survival premise is needed
to pay finite approximation overhead; the genuine original energy remains.

This is decidable rational branching on finite original data, not a uniform
scaling modulus, a continuum excitation or an all-vector RG comparison.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialAdaptiveSignedScorePayment
import YMGap.Continuum.QuaternionHaarPositiveWeightNullReflection
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepNullScore
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
import YMGap.Constructive.CauchyConv
import YMGap.Constructive.CRealExp

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTotalSignedScorePayment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep_supported)
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
  (relativeCutoff headCutoff_le_relativeCutoff)
open YMGap.Continuum.QuaternionHaarPositiveWeightNullReflection
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass weightedMass_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (spatialFloorCertificate)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headFloor_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy energy_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepExactScoreCost (exactScoreSignedBulk)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepNullScore (exactScoreSignedBulk_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAdaptiveSignedScorePayment

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks terminalMessage weightedMass originalBlockTransfer
  spatialWeight relativeCutoff exactScoreSignedBulk energy blockConditionalRatio
  signedScorePaymentBound

/-- An actual zero surviving square is null under EVERY Haar insertion,
not just one fitted observable or the transmitted-square test itself. -/
theorem original_weighted_square_zero_null {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) {b : RatPoly}
    (hb : SupportedQuaternionBlocks (N width) b)
    (hzero : weightedMass w K width (polyMul b b) ≈ 0) :
    HaarCarrierEqv (N width) b polyZero := by
  exact haar_null_of_positive_weight_square_zero hb
    (HKPos.pow_pos (headFloor_positive hw0 hw1) _)
    (spatialFloorCertificate hw0 hw1 K width
      (Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK))
    (by simpa only [weightedMass] using hzero)

/-- Construct finite sigma and an all-later degree onset for EVERY supported
source. No positive-transmitted-target hypothesis is supplied or inverted. -/
def totalSignedScorePayment {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : relativeCutoff w 32 ≤ K) (n r : Nat) (hN : 0 < N width)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    SignedScorePayment hw0 hw1 K width hK n r psi epsilon := by
  let hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let A := terminalMessage w K width (n+(r+1))
  let b := originalBlockTransfer w K width (r+1) (polyMul (terminalMessage w K width n) psi)
  let Z0 := weightedMass w K width (polyMul A A)
  let Z1 := weightedMass w K width (polyMul A (transferStep w K width A))
  let B := weightedMass w K width (polyMul b b)
  let Q := Z1*B
  by_cases hQ : (0 : Q') < Q
  · exact adaptiveSignedScorePayment hw0 hw1 K width hK n r hN hp epsilon hepsilon hQ
  · have hA := terminalMessage_supported w K width (n+(r+1))
    have hb : SupportedQuaternionBlocks (N width) b := by
      simpa only [b, originalBlockTransfer] using
        iterateStep_supported (kineticWeight_supported w K width)
          (spatialWeight_supported w K width) (r+1)
          (supported_polyMul (terminalMessage_supported w K width n) hp)
    have hZ0 : (0 : Q') ≤ Z0 :=
      weightedMass_nonnegative hw0 hw1 K width hhead (Certificate.square A hA)
    have hZ1 : (0 : Q') < Z1 := by
      dsimp only [Z1, A]
      rw [terminalMessage_next]
      exact terminalPair_positive hw0 hw1 K width hhead _ _
    have hB : (0 : Q') ≤ B :=
      weightedMass_nonnegative hw0 hw1 K width hhead (Certificate.square b hb)
    have hQzero : Q ≈ 0 := Int.le_antisymm (Int.le_of_not_gt hQ)
      (Q'.mul_nonneg _ _ (Q'.le_of_lt hZ1) hB)
    have hBzero : B ≈ 0 := Q'.mul_eqv_zero_of_pos hZ1 hQzero
    have hn := original_weighted_square_zero_null hw0 hw1 K width hK hb hBzero
    refine ⟨1, by decide, 0, ?_⟩
    unfold signedScorePaymentBound
    intro k _
    let phi := blockConditionalRatio hw0 hw1 K width hhead n (r+1) psi (k+1)
    have hE : (0 : Q') ≤ energy w K width A phi :=
      energy_nonnegative hw0 hw1 K width hhead hA
        (blockConditionalRatio_supported hw0 hw1 K width hhead n (r+1) hp (k+1))
        (terminalMessage_certificate hw0 hw1 K width hhead (n+(r+1)))
    have hbulk := exactScoreSignedBulk_zero 1 hw0 hw1 K width hK n r hN psi (k+1) hn
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hbulk) (Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ hZ0 hE)
      (Q'.mul_nonneg _ _ (Q'.le_of_lt hepsilon)
        (Q'.mul_nonneg _ _ (Q'.le_of_lt hZ1) hB)))

#print axioms original_weighted_square_zero_null
#print axioms totalSignedScorePayment

end YMGap.Continuum.BF4ExactSlabFixedSpatialTotalSignedScorePayment
