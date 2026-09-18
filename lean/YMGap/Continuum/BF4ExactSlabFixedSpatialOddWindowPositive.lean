/-
# Positive one-step quadratics on the original balanced odd window

Contract the observed left window to its actual signed message F. The
separated-window identity and reversal adjointness turn the numerator
of its bond-reflected pair into H[V*F*T F]. The original kinetic Gram
theorem supplies nonnegativity for this F with the FULL spatial action.

The denominator remains the original total-chain partition. Its existing
positive certificate retains 0<w<1 and the late-cutoff guard. No positivity
of F, replacement action, density normalization or finite stationarity is
assumed. This is finite-window positivity, not a strict spectral estimate.
-/

import YMGap.Continuum.SU2QuaternionHeadWindowReversal
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive
import YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedWindowPins

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialOddWindowPositive

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticSymmetry (kineticWeight_swap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (weightedMass_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (observedMessage observedMessage_supported windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput (inputNumerator)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTwoBoundary (inputPartition_terminal_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedWindowPins
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionSliceReversal (reversePolynomial)
open YMGap.Continuum.SU2QuaternionHeadWindowContraction (windowMessage)
open YMGap.Continuum.SU2QuaternionHeadWindowReversal (windowMessage_reversal)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks kineticWeight spatialWeight weightedMass

/-- The signed observed-window numerator is the ACTUAL original quadratic.
Use reversal with the unreflected probe, so no double-reversal substitution
or auxiliary observed-message congruence is needed. -/
theorem reversed_input_quadratic_pin (w : Q') (K width t R : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks ((R+1)*(N width)) p) :
    inputNumerator w K width R t
        (transferStep w K width (observedMessage w K width t R p))
        (reversePolynomial (N width) R p) ≈
      weightedMass w K width
        (polyMul (observedMessage w K width t R p)
          (transferStep w K width (observedMessage w K width t R p))) := by
  have h := windowMessage_reversal R (kineticWeight_supported w K width)
    (spatialWeight_supported w K width) (kineticWeight_swap w K width)
    (terminalMessage_supported w K width t)
    (transferStep_supported w K width (observedMessage_supported w K width t R hp)) hp
  have h' : weightedMass w K width
      (polyMul (observedMessage w K width t R p)
        (transferStep w K width (observedMessage w K width t R p))) ≈
    weightedMass w K width
      (polyMul (terminalMessage w K width t)
        (windowMessage (N width) (kineticWeight w K width) (spatialWeight w K width) R
          (transferStep w K width (observedMessage w K width t R p))
          (reversePolynomial (N width) R p))) := by
    simpa only [weightedMass, observedMessage] using h
  exact Q'.eqv_trans _ _ _
    (weightedMass_congr w K width (RatPolyCoeffEqv.mul_comm _ _)) (Q'.eqv_symm h')

/-- Balanced equal-depth boundaries and one central transition. The
original full partition is retained by the separated-window pin. -/
theorem reversed_windowRatio_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (t R : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks ((R+1)*(N width)) p) :
    (0 : Q') ≤ windowRatio hw0 hw1 K width hK t (2*R+1) t
      (polyMul p (liftBoundary ((R+1)*(N width)) (reversePolynomial (N width) R p))) := by
  have hZ := inputPartition_terminal_positive hw0 hw1 K width hK R t (t+R+1)
  have hpin := windowRatio_separated_joint hw0 hw1 K width hK t R 1 R t
    p (reversePolynomial (N width) R p) hZ
  have hquad := reversed_input_quadratic_pin w K width t R p hp
  have hn := Q'.le_trans' _ _ _
    (transferStep_quadratic_nonnegative w (Q'.le_of_lt hw0) K width
      (observedMessage w K width t R p) (observedMessage_supported w K width t R hp))
    (Q'.ge_of_eqv hquad)
  have hscaled := Q'.mul_nonneg _ _ hn (Q'.le_of_lt (Q'.recipPos_pos _ hZ))
  have hresult := Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hpin)
  simpa only [show R+1+R=2*R+1 by omega] using hresult

end YMGap.Continuum.BF4ExactSlabFixedSpatialOddWindowPositive

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOddWindowPositive.reversed_input_quadratic_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOddWindowPositive.reversed_windowRatio_nonnegative
