/-
# Computed dual lower bounds for the ORIGINAL one-step response

For the actual terminal message g=T^n 1, put u=V*(g*h). The kinetic
positive form gives D^2 <= N*C, where D=H[u*P(b)], N=H[u*P(u)] and
C=H[b*P(b)]. N divided by the SAME odd partition is exactly the existing
windowRatio of h(x)h(y). Thus every supported signed polynomial b supplies
the computable nonnegative lower bound D^2/((1+C)*Z).

No detection, inverse heat identity, nonzero response, or uniform limiting
estimate is assumed or concluded. In particular a zero detector gives a
zero floor. The added one makes the dual denominator positive even for a
kinetic null test. All spatial factors, both terminal messages, and the
original partition remain present. The next consumer needs an actual
detecting test and estimates stable through the required limits.
-/

import YMGap.Continuum.SU2QuaternionProductHeatDualForm
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialResponseDual

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindowPairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks spatialWeight terminalMessage weightedMass

/-- The full interacting endpoint, not a spectator-independent replacement. -/
def weightedSource (w : Q') (K width n : Nat) (h : RatPoly) : RatPoly :=
  polyMul (spatialWeight w K width) (polyMul (terminalMessage w K width n) h)

theorem weightedSource_supported (w : Q') (K width n : Nat) {h : RatPoly}
    (hh : SupportedQuaternionBlocks (N width) h) :
    SupportedQuaternionBlocks (N width) (weightedSource w K width n h) :=
  supported_polyMul (spatialWeight_supported w K width)
    (supported_polyMul (terminalMessage_supported w K width n) hh)

/-- The exact original kinetic detector of the weighted signed source. -/
def detector (w : Q') (K width n : Nat) (h b : RatPoly) : Q' :=
  kineticPair (N width) w K (activeBlocks width) (weightedSource w K width n h) b

def testCost (w : Q') (K width : Nat) (b : RatPoly) : Q' :=
  kineticPair (N width) w K (activeBlocks width) b b

theorem testCost_nonnegative (w : Q') (hw : (0 : Q') ≤ w) (K width : Nat)
    {b : RatPoly} (hb : SupportedQuaternionBlocks (N width) b) :
    (0 : Q') ≤ testCost w K width b :=
  kineticPair_nonnegative (N width) w hw K (activeBlocks width) (activeBlocks_lt width) b hb

/-- No positive-test-cost assumption is needed, including at finite cutoff. -/
theorem regularizedCost_positive (w : Q') (hw : (0 : Q') ≤ w) (K width : Nat)
    {b : RatPoly} (hb : SupportedQuaternionBlocks (N width) b) :
    (0 : Q') < 1 + testCost w K width b :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.add_le_self_of_nonneg 1 _ (testCost_nonnegative w hw K width hb))

/-- The kinetic quadratic is the existing original one-step window numerator. -/
theorem response_numerator_pin (w : Q') (K width n : Nat) {h : RatPoly}
    (hh : SupportedQuaternionBlocks (N width) h) :
    kineticPair (N width) w K (activeBlocks width)
        (weightedSource w K width n h) (weightedSource w K width n h) ≈
      weightedMass w K width (polyMul
        (observedMessage w K width n 1 (polyMul h (liftBoundary (N width) h)))
        (terminalMessage w K width n)) := by
  have hp : SupportedQuaternionBlocks (N width+N width)
      (polyMul h (liftBoundary (N width) h)) :=
    supported_polyMul
      (fun t ht => Nat.le_trans (hh t ht) (Nat.mul_le_mul_left 4 (Nat.le_add_right _ _)))
      (lift_supported hh (N width))
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (original_quadratic_pin w K width (polyMul (terminalMessage w K width n) h)))
    (Q'.eqv_trans _ _ _
      (Q'.eqv_symm (edge_pairing w K width (terminalMessage w K width n) h h))
      (edge_window_pairing w K width n hp))

/-- A finite rational witness; its numerator may be zero. -/
def responseFloor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (h b : RatPoly)
    (hb : SupportedQuaternionBlocks (N width) b) : Q' :=
  ((detector w K width n h b * detector w K width n h b) *
    Q'.recipPos (1 + testCost w K width b)
      (regularizedCost_positive w (Q'.le_of_lt hw0) K width hb)) *
    Q'.recipPos (oddMass w K width n) (oddMass_positive hw0 hw1 K width hK n)

theorem responseFloor_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (h b : RatPoly)
    (hb : SupportedQuaternionBlocks (N width) b) :
    (0 : Q') ≤ responseFloor hw0 hw1 K width hK n h b hb :=
  Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (SumOfSquares.q_mul_self_nonneg _)
      (Q'.le_of_lt (Q'.recipPos_pos _ _)))
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

/-- Every supported dual test yields a checked lower bound for the SAME
original finite response; no inverse, non-erasure or limiting bound is supplied. -/
theorem responseFloor_le_window {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) {h b : RatPoly}
    (hh : SupportedQuaternionBlocks (N width) h)
    (hb : SupportedQuaternionBlocks (N width) b) :
    responseFloor hw0 hw1 K width hK n h b hb ≤
      windowRatio hw0 hw1 K width hK n 1 n (polyMul h (liftBoundary (N width) h)) := by
  let u := weightedSource w K width n h
  let A := kineticPair (N width) w K (activeBlocks width) u u
  let C := testCost w K width b
  have hu := weightedSource_supported w K width n hh
  have hA : (0 : Q') ≤ A :=
    kineticPair_nonnegative (N width) w (Q'.le_of_lt hw0) K
      (activeBlocks width) (activeBlocks_lt width) u hu
  have hC : C ≤ 1+C :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg C 1 Q'.zero_le_one)
      (Q'.le_of_eqv (Q'.add_comm_eqv C 1))
  have hcs : detector w K width n h b * detector w K width n h b ≤ A*C :=
    kineticPair_cauchySchwarz (N width) w (Q'.le_of_lt hw0) K
      (activeBlocks width) (activeBlocks_lt width) u b hu hb
  have hbound := Q'.le_trans' _ _ _ hcs
    (Q'.mul_le_mul_of_nonneg_left _ _ A hC hA)
  have hc := regularizedCost_positive w (Q'.le_of_lt hw0) K width hb
  let r := Q'.recipPos (1+C) hc
  have hr : (0 : Q') ≤ r := Q'.le_of_lt (Q'.recipPos_pos _ hc)
  have hcancel : (A*(1+C))*r ≈ A :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv _ hc))
        (Q'.mul_one_eqv A))
  have hraw := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ r hbound hr) (Q'.le_of_eqv hcancel)
  have hz := oddMass_positive hw0 hw1 K width hK n
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ (Q'.recipPos _ hz) hraw
      (Q'.le_of_lt (Q'.recipPos_pos _ hz)))
    (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ (response_numerator_pin w K width n hh)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialResponseDual

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialResponseDual.weightedSource_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialResponseDual.testCost_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialResponseDual.regularizedCost_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialResponseDual.response_numerator_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialResponseDual.responseFloor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialResponseDual.responseFloor_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialResponseDual.responseFloor_le_window
