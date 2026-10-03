/-
# Constructed angular reconstruction of the ORIGINAL conditional ratio

The actual polynomial ratio G_k*b has cleared derivative converging to
A*db-b*dA in the original V-weighted square form, with a computed onset.
Every cost in that onset is an actual polynomial integral, not a supplied
analytic ceiling. The literal OWN-centered padded square discharges the
source support input. This is fixed-window reconstruction, not a bound on
the complete signed cost relative to the interacting filtered variance.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
import YMGap.Continuum.QuaternionHaarReciprocalAngularScoreModulus

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalScore

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (kineticFloor_le_cap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
open YMGap.Continuum.QuaternionHaarReciprocalAngularScore
open YMGap.Continuum.QuaternionHaarReciprocalAngularScoreModulus
open YMGap.Continuum.BF4DyadicWilsonSquare (side paddedSquare)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (sourceCharacter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredOwnYoung (ownMean)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks kineticWeight spatialWeight terminalMessage

def blockAngularScoreError {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t i j : Nat) (psi : RatPoly) (k : Nat) : RatPoly :=
  let A := terminalMessage w K width (n+t)
  let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
  polyAdd
    (polyMul (polyMul A A)
      (angularDerivative i j (blockConditionalRatio hw0 hw1 K width hK n t psi (k+1))))
    (polyNeg (score i j A b))

/-- Onset computed from the actual score and derivative costs at these
original parameters. No family-uniform bound on them is postulated. -/
def blockAngularScoreCutoff {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t i j : Nat) (psi : RatPoly) (epsilon : Q') : Nat :=
  let A := terminalMessage w K width (n+t)
  let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
  let u := blockWindowUpper w K width n t
  let hu := blockWindowUpper_positive hw0 hw1 K width hK n t
  let S := score i j A b
  let r := polyMul (polyMul A b) (angularDerivative i j (remainder A u hu))
  scoreErrorModulus (radius (blockWindowLower w K width n t) u hu)
    (weightedMass w K width (polyMul S S)) (weightedMass w K width (polyMul r r)) epsilon

/-- The actual ratio's cleared angular derivative has an explicit
same-action, same-weight reconstruction modulus. -/
theorem blockConditionalRatio_angular_reconstruction {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t i j : Nat)
    (hi : i < 4*N width) (hj : j < 4*N width) (hdepth : 1 ≤ n+t)
    {psi : RatPoly} (hp : SupportedQuaternionBlocks (N width) psi)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (k : Nat)
    (hk : blockAngularScoreCutoff hw0 hw1 K width hK n t i j psi epsilon ≤ k) :
    let e := blockAngularScoreError hw0 hw1 K width hK n t i j psi k
    weightedMass w K width (polyMul e e) ≤ epsilon := by
  dsimp only
  let A := terminalMessage w K width (n+t)
  let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
  let u := blockWindowUpper w K width n t
  let hu := blockWindowUpper_positive hw0 hw1 K width hK n t
  let G := reciprocal A u hu (k+1)
  let e := polyAdd (polyMul (polyMul A A) (angularDerivative i j (polyMul b G)))
    (polyNeg (score i j A b))
  have hb : SupportedQuaternionBlocks (N width) b :=
    iterateStep_supported (kineticWeight_supported w K width) (spatialWeight_supported w K width)
      t (supported_polyMul (terminalMessage_supported w K width n) hp)
  have hphi : RatPolyCoeffEqv
      (blockConditionalRatio hw0 hw1 K width hK n t psi (k+1)) (polyMul b G) :=
    RatPolyCoeffEqv.mul_comm G b
  have he : RatPolyCoeffEqv (blockAngularScoreError hw0 hw1 K width hK n t i j psi k) e :=
    ((angularDerivative_congr i j hphi).mul_left (polyMul A A)).add (.refl _)
  have ht := reciprocal_ratio_score_error_tolerance hi hj
    (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK)
    (terminalMessage_supported w K width (n+t)) hb
    (blockWindowLower_positive hw0 hw1 K width hK n t) hu
    (show blockWindowLower w K width n t ≤ u from
      Q'.mul_le_mul_of_nonneg_right _ _ _ (kineticFloor_le_cap hw0 hw1 width)
        (Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hK (n+t-1))))
    (blockWindowCertificates hw0 hw1 K width hK n t hdepth).1
    (blockWindowCertificates hw0 hw1 K width hK n t hdepth).2 hepsilon k hk
  unfold weightedMass
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (haar_of_coeff ((he.mul he).mul_left (spatialWeight w K width)))) ht

/-- Literal OWN-centered square-loop reconstruction: every analytic cost
is computed and its source support is constructed, not a new premise. -/
theorem ownPaddedSquareRatio_angular_reconstruction {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (n t scale i j : Nat)
    (hi : i < 4*N width) (hj : j < 4*N width)
    (hdepth : 1 ≤ n+t) (hwidth : side scale < width)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (k : Nat)
    (hk : blockAngularScoreCutoff hw0 hw1 K width hK n t i j
      (shifted (sourceCharacter width (paddedSquare scale width hwidth).edges 1)
        (ownMean hw0 hw1 K width hK n (paddedSquare scale width hwidth))) epsilon ≤ k) :
    let psi := shifted (sourceCharacter width (paddedSquare scale width hwidth).edges 1)
      (ownMean hw0 hw1 K width hK n (paddedSquare scale width hwidth))
    let e := blockAngularScoreError hw0 hw1 K width hK n t i j psi k
    weightedMass w K width (polyMul e e) ≤ epsilon :=
  blockConditionalRatio_angular_reconstruction hw0 hw1 K width hK n t i j hi hj hdepth
    (ownPaddedSquareInterval hw0 hw1 K width hK n scale hwidth).support epsilon hepsilon k hk

#print axioms blockAngularScoreError
#print axioms blockAngularScoreCutoff
#print axioms blockConditionalRatio_angular_reconstruction
#print axioms ownPaddedSquareRatio_angular_reconstruction

end YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalScore
