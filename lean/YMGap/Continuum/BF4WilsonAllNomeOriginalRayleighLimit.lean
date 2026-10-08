/-
# Original filtered OWN cost and variance for radius-zero Wilson syntax

For any fixed signed radius-zero expression, the literal finite source is
b=T^t(g_stage*(f-c_stage)), where c_stage is its computed original odd-window
mean. The squared norm uses Z0=ell(A^2); the cleared cost uses BOTH original
chronological partitions Z0 and Z1=ell(A*T A). Their limits are the existing
centeredTimeMoment at 2t and its 2t-(2t+1) difference on the SAME carrier.

No source-norm inverse, new completion or limit functional is constructed.
Nome, width, expression and t stay fixed. No relative budget, Casimir claim
for the filtered ratio, changing-source modulus or scaling bound is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighWindow
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOwnCenterLimit

namespace YMGap.Continuum.BF4WilsonAllNomeOriginalRayleighLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalPair_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockWindowPin (normalized_block_window_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit (clearedRayleighCost)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighWindow (clearedRayleighCost_window_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMovingCenterLagDifference (centeredPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOwnCenterLimit
  (expressionOwn_centeredPair_converges)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.BF4WilsonAllNomeZeroRadiusIncrement (state)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments (centeredTimeMoment)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  {width : Nat} (e : WindowExpression width) (he : Within 0 e)

attribute [local irreducible] baseLinks weightedMass terminalMessage centeredPair

section Finite

variable (stage t : Nat)

local notation "K" => headCutoff w+stage
local notation "f" => sourcePolynomial e
local notation "c" => middleRatio hw0 hw1 K width (Nat.le_add_right _ _) (stage+1) stage f
local notation "A" => terminalMessage w K width (stage+t)
local notation "b" => originalBlockTransfer w K width t
  (polyMul (terminalMessage w K width stage) (shifted f c))
local notation "Z0" => weightedMass w K width (polyMul A A)
local notation "Z1" => weightedMass w K width (polyMul A (transferStep w K width A))

include hw0 hw1 in
private theorem zeroPartition_positive : (0 : Q') < Z0 :=
  terminalPair_positive hw0 hw1 K width (Nat.le_add_right _ _) (stage+t) (stage+t)

include hw0 hw1 in
private theorem onePartition_positive : (0 : Q') < Z1 := by
  rw [terminalMessage_next w K width (stage+t)]
  exact terminalPair_positive hw0 hw1 K width (Nat.le_add_right _ _) (stage+t) (stage+t+1)

include he in
private theorem source_support : SupportedQuaternionBlocks (N width) f := by
  simpa only [Nat.zero_add, Nat.one_mul] using source_supported 0 e he

/-- Literal filtered squared norm divided only by its chronological mass. -/
def originalOwnBlockVariance : Q' :=
  weightedMass w K width (polyMul b b) *
    Q'.recipPos Z0 (zeroPartition_positive hw0 hw1 (width := width) stage t)

/-- Literal cleared Rayleigh cost divided by BOTH chronological masses. -/
def originalOwnBlockCost : Q' :=
  clearedRayleighCost w K width A b *
    Q'.recipPos (Z0*Z1) (Q'.mul_pos
      (zeroPartition_positive hw0 hw1 (width := width) stage t)
      (onePartition_positive hw0 hw1 (width := width) stage t))

include he in
theorem originalOwnBlockVariance_pin :
    originalOwnBlockVariance hw0 hw1 e stage t ≈
      centeredPair hw0 hw1 K width (Nat.le_add_right _ _) stage (2*t) f c := by
  simpa only [originalOwnBlockVariance, centeredPair, Nat.add_zero] using
    normalized_block_window_pin hw0 hw1 K width (Nat.le_add_right _ _) stage t 0
      (shifted_supported (source_support e he) c)

include he in
theorem originalOwnBlockCost_pin :
    originalOwnBlockCost hw0 hw1 e stage t ≈
      centeredPair hw0 hw1 K width (Nat.le_add_right _ _) stage (2*t) f c +
        -(centeredPair hw0 hw1 K width (Nat.le_add_right _ _) stage (2*t+1) f c) := by
  let d := centeredPair hw0 hw1 K width (Nat.le_add_right _ _) stage (2*t) f c +
    -(centeredPair hw0 hw1 K width (Nat.le_add_right _ _) stage (2*t+1) f c)
  let r := Q'.recipPos (Z0*Z1) (Q'.mul_pos
    (zeroPartition_positive hw0 hw1 (width := width) stage t)
    (onePartition_positive hw0 hw1 (width := width) stage t))
  have hpin : clearedRayleighCost w K width A b ≈ (Z0*Z1)*d := by
    simpa only [d, centeredPair] using
      clearedRayleighCost_window_pin hw0 hw1 K width (Nat.le_add_right _ _) stage t
        (shifted_supported (source_support e he) c)
  have hr : (Z0*Z1)*r ≈ 1 := Q'.mul_recipPos_eqv _ _
  change clearedRayleighCost w K width A b*r ≈ d
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ r hpin)
    (Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
        (fun | 0 => Z0*Z1 | 1 => d | _ => r))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ d hr) (Q'.one_mul_eqv d)))

end Finite

/-- The fixed actual expression reaches its SAME completed centered moment. -/
theorem originalOwnBlockVariance_converges (t : Nat) :
    ConvergesTo (fun k => ofQ' (originalOwnBlockVariance hw0 hw1 e k t))
      (centeredTimeMoment hw0 hw1 (2*t) (state e he) (state e he)) :=
  TrigAddCReal.convergesTo_congr_seq
    (s := fun k => ofQ' (centeredPair hw0 hw1 (headCutoff w+k) width
      (Nat.le_add_right _ _) k (2*t) (sourcePolynomial e)
      (middleRatio hw0 hw1 (headCutoff w+k) width (Nat.le_add_right _ _) (k+1) k
        (sourcePolynomial e))))
    (fun k => SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.eqv_symm (originalOwnBlockVariance_pin hw0 hw1 e he k t)))
    (expressionOwn_centeredPair_converges hw0 hw1 e he (2*t))

/-- No norm inverse: the cost reaches the literal difference of moments. -/
theorem originalOwnBlockCost_converges (t : Nat) :
    ConvergesTo (fun k => ofQ' (originalOwnBlockCost hw0 hw1 e k t))
      (sub (centeredTimeMoment hw0 hw1 (2*t) (state e he) (state e he))
        (centeredTimeMoment hw0 hw1 (2*t+1) (state e he) (state e he))) := by
  have h := TrigAddCReal.convergesTo_add
    (expressionOwn_centeredPair_converges hw0 hw1 e he (2*t))
    (TrigAddCReal.convergesTo_neg
      (expressionOwn_centeredPair_converges hw0 hw1 e he (2*t+1)))
  exact TrigAddCReal.convergesTo_congr_seq
    (s := fun k => add
      (ofQ' (centeredPair hw0 hw1 (headCutoff w+k) width
        (Nat.le_add_right _ _) k (2*t) (sourcePolynomial e)
        (middleRatio hw0 hw1 (headCutoff w+k) width (Nat.le_add_right _ _)
          (k+1) k (sourcePolynomial e))))
      (neg (ofQ' (centeredPair hw0 hw1 (headCutoff w+k) width
        (Nat.le_add_right _ _) k (2*t+1) (sourcePolynomial e)
        (middleRatio hw0 hw1 (headCutoff w+k) width (Nat.le_add_right _ _)
          (k+1) k (sourcePolynomial e))))))
    (fun k => SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.eqv_symm (originalOwnBlockCost_pin hw0 hw1 e he k t))) h

#print axioms originalOwnBlockVariance
#print axioms originalOwnBlockCost
#print axioms originalOwnBlockVariance_pin
#print axioms originalOwnBlockCost_pin
#print axioms originalOwnBlockVariance_converges
#print axioms originalOwnBlockCost_converges

end YMGap.Continuum.BF4WilsonAllNomeOriginalRayleighLimit
