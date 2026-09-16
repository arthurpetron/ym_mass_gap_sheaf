/-
# Joint and marginal pins on one original separated-window partition

The left observation is contracted across its window and then through the
gap. The joint, left marginal and right marginal are all ratios on the SAME
total window L+g+R with the SAME external boundary lengths m,n. Their common
denominator is exactly the R-window input partition of u_(m+L+g), not a
separately normalized shorter-chain state.

The scalar pins are signed finite polynomial identities with no support
premises. The positive denominator proof is explicit and is supplied by the
existing inputPartition_terminal_positive theorem. No positivity is assumed
of either observation or its contracted message. Bounds, original ambient
placement, and limiting connected-correlator estimates are later consumers.
-/

import YMGap.Continuum.SU2QuaternionHeadSeparatedWindows
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTwoBoundary
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedWindowPins

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (weightedMass_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing
  (observedMessage windowRatio window_unobserved_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowInput
  (inputNumerator inputPartition inputNumerator_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTwoBoundary
  (inputPartition_terminal inputPartition_terminal_positive windowRatio_input_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws (windowRatio_congr)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHeadWindowContraction
open YMGap.Continuum.SU2QuaternionHeadSeparatedWindows (windowMessage_separated)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

/-- The actual observed left message after the same g unobserved transitions. -/
def separatedMessage (w : Q') (K width m L g : Nat) (p : RatPoly) : RatPoly :=
  iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) g
    (observedMessage w K width m L p)

attribute [local irreducible] weightedMass kineticWeight spatialWeight baseLinks

private theorem iterate_congr (blocks : Nat) (kernel weight : RatPoly) :
    (count : Nat) → {p q : RatPoly} → RatPolyCoeffEqv p q →
      RatPolyCoeffEqv (iterateStep blocks kernel weight count p)
        (iterateStep blocks kernel weight count q)
  | 0, _, _, h => h
  | count+1, _, _, h => iterate_congr blocks kernel weight count
      (partialHaarHeads_congr blocks ((h.mul_left weight).mul_left kernel))

/-- The unit left insertion gives the actual terminal message, with no
division by its possibly nonconstant polynomial values. -/
theorem separatedMessage_one (w : Q') (K width m L g : Nat) :
    RatPolyCoeffEqv (separatedMessage w K width m L g polyOne)
      (terminalMessage w K width (m+L+g)) := by
  have h := iterate_congr (N width) (kineticWeight w K width) (spatialWeight w K width) g
    (window_unobserved_pin w K width m L)
  change RatPolyCoeffEqv (separatedMessage w K width m L g polyOne)
    (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) g
      (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) (m+L) polyOne)) at h
  rw [← iterateStep_add] at h
  exact h

/-- Both presentations have exactly m+L+g+R+n transfer factors and the
same final spatial weight. This is literal scalar equality, not a bound. -/
theorem separatedPartition_eq (w : Q') (K width m L g R n : Nat) :
    inputPartition w K width (L+g+R) n (terminalMessage w K width m) =
      inputPartition w K width R n (terminalMessage w K width (m+L+g)) := by
  simp only [inputPartition_terminal, Nat.add_assoc]

section CommonPartition

attribute [local irreducible] inputNumerator inputPartition windowRatio terminalMessage

private theorem reciprocal_congr_eq {a b : Q'} (ha : (0 : Q') < a)
    (hb : (0 : Q') < b) (he : a = b) : Q'.recipPos a ha ≈ Q'.recipPos b hb := by
  cases he
  exact Q'.eqv_refl _

private theorem common_partition_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L g R n : Nat) (p : RatPoly)
    (hZ : (0 : Q') < inputPartition w K width R n (terminalMessage w K width (m+L+g))) :
    windowRatio hw0 hw1 K width hK m (L+g+R) n p ≈
      inputNumerator w K width (L+g+R) n (terminalMessage w K width m) p *
        Q'.recipPos (inputPartition w K width R n (terminalMessage w K width (m+L+g))) hZ := by
  have hZtotal := inputPartition_terminal_positive hw0 hw1 K width hK (L+g+R) n m
  have h := windowRatio_input_pin hw0 hw1 K width hK m (L+g+R) n p hZtotal
  exact Q'.eqv_trans _ _ _ h (Q'.mul_eqv_congr_left _ _ _
    (reciprocal_congr_eq hZtotal hZ (separatedPartition_eq w K width m L g R n)))

end CommonPartition

/-- Joint observation pin: left window, same gap, then right window, all
normalized by the unchanged total-chain partition. -/
theorem windowRatio_separated_joint {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L g R n : Nat) (p q : RatPoly)
    (hZ : (0 : Q') < inputPartition w K width R n (terminalMessage w K width (m+L+g))) :
    windowRatio hw0 hw1 K width hK m (L+g+R) n
        (polyMul p (liftBoundary ((L+g)*(N width)) q)) ≈
      inputNumerator w K width R n (separatedMessage w K width m L g p) q *
        Q'.recipPos (inputPartition w K width R n (terminalMessage w K width (m+L+g))) hZ := by
  have hmessage := windowMessage_separated (N width) (kineticWeight w K width)
    (spatialWeight w K width) L g R (terminalMessage w K width m) p q
  have hnum : inputNumerator w K width (L+g+R) n (terminalMessage w K width m)
      (polyMul p (liftBoundary ((L+g)*(N width)) q)) ≈
        inputNumerator w K width R n (separatedMessage w K width m L g p) q :=
    weightedMass_congr w K width (hmessage.mul_right (terminalMessage w K width n))
  exact Q'.eqv_trans _ _ _
    (common_partition_pin hw0 hw1 K width hK m L g R n
      (polyMul p (liftBoundary ((L+g)*(N width)) q)) hZ)
    (Q'.mul_eqv_congr_right _ _ _ hnum)

/-- Left marginal pin on the SAME total window. The unobserved right
window integrates the signed separated message without renormalizing it. -/
theorem windowRatio_separated_left {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L g R n : Nat) (p : RatPoly)
    (hZ : (0 : Q') < inputPartition w K width R n (terminalMessage w K width (m+L+g))) :
    windowRatio hw0 hw1 K width hK m (L+g+R) n p ≈
      inputPartition w K width R n (separatedMessage w K width m L g p) *
        Q'.recipPos (inputPartition w K width R n (terminalMessage w K width (m+L+g))) hZ := by
  have hfirst : RatPolyCoeffEqv
      (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) L
        (polyMul (terminalMessage w K width m) p))
      (observedMessage w K width m L p) :=
    (windowMessage_iterate (N width) (kineticWeight w K width) (spatialWeight w K width)
      L (terminalMessage w K width m) p).symm
  have htime : RatPolyCoeffEqv
      (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) (L+g+R)
        (polyMul (terminalMessage w K width m) p))
      (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) R
        (separatedMessage w K width m L g p)) := by
    rw [iterateStep_add, iterateStep_add]
    exact iterate_congr (N width) (kineticWeight w K width) (spatialWeight w K width) R
      (iterate_congr (N width) (kineticWeight w K width) (spatialWeight w K width) g hfirst)
  have hmessage := (windowMessage_iterate (N width) (kineticWeight w K width)
    (spatialWeight w K width) (L+g+R) (terminalMessage w K width m) p).trans htime
  have hnum : inputNumerator w K width (L+g+R) n (terminalMessage w K width m) p ≈
      inputPartition w K width R n (separatedMessage w K width m L g p) :=
    weightedMass_congr w K width (hmessage.mul_right (terminalMessage w K width n))
  exact Q'.eqv_trans _ _ _ (common_partition_pin hw0 hw1 K width hK m L g R n p hZ)
    (Q'.mul_eqv_congr_right _ _ _ hnum)

/-- Right marginal pin on the SAME total window. The unit left observation
produces u_(m+L+g), so the right numerator uses the common comparison input. -/
theorem windowRatio_separated_right {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L g R n : Nat) (q : RatPoly)
    (hZ : (0 : Q') < inputPartition w K width R n (terminalMessage w K width (m+L+g))) :
    windowRatio hw0 hw1 K width hK m (L+g+R) n (liftBoundary ((L+g)*(N width)) q) ≈
      inputNumerator w K width R n (terminalMessage w K width (m+L+g)) q *
        Q'.recipPos (inputPartition w K width R n (terminalMessage w K width (m+L+g))) hZ := by
  have hstart := windowRatio_congr hw0 hw1 K width hK m (L+g+R) n
    (RatPolyCoeffEqv.one_mul (liftBoundary ((L+g)*(N width)) q)).symm
  have hnum := inputNumerator_congr w K width R n (separatedMessage_one w K width m L g) q
  exact Q'.eqv_trans _ _ _ hstart
    (Q'.eqv_trans _ _ _ (windowRatio_separated_joint hw0 hw1 K width hK m L g R n polyOne q hZ)
      (Q'.mul_eqv_congr_right _ _ _ hnum))

end YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedWindowPins

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedWindowPins.separatedMessage
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedWindowPins.separatedMessage_one
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedWindowPins.separatedPartition_eq
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedWindowPins.windowRatio_separated_joint
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedWindowPins.windowRatio_separated_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedWindowPins.windowRatio_separated_right
