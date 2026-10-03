/-
# Original block cost and variance reach the SAME completed dyadic response

Both finite quantities use b=T^t(g_k*(f-c_k)), A=g_(k+t), the actual
odd-window mean c_k, and the complete original action. Dividing the cleared
Rayleigh cost by its TWO positive chronological partitions gives the actual
centered lag difference. Dividing ell(b^2) by its own partition gives its
actual centered lag pair. Their joint cutoff/time limits are, respectively,

    N*(R_(2t)-R_(2t+1))  and  N*R_(2t),

where N and R are the EXISTING dyadic original norm and unit response on the
SAME completed carrier. No separate state, normalizer or limit is constructed.
For an even dyadic side and t=side/2 these are the required producer numerator
and denominator. A useful relative inequality between them is NOT proved.
Nome, width, scale and t remain fixed; no scaling trajectory is supplied.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighWindow
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOwnCenterLimit
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMovingCenterLagCauchy

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicOriginalRayleighLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4CompactActionCPOrder
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
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMovingCenterLagCauchy
  (ownCenteredLagDifference ownCenteredLagDifference_converges)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOwnCenterLimit (own_centeredPair_converges)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.BF4DyadicWilsonSquare (side paddedSquare)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments (centeredTimeMoment)
open YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation (dyadicOriginalNorm dyadicUnitResponse)
open YMGap.Continuum.BF4WilsonAllNomeDyadicChronologicalResponse

local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (scale width : Nat) (hwidth : side scale < width)

local notation "square" => paddedSquare scale width hwidth
local notation "Norm" => dyadicOriginalNorm hw0 hw1 scale width hwidth
local notation:max "Response" lag:arg => dyadicUnitResponse hw0 hw1 scale width hwidth lag

attribute [local irreducible] baseLinks weightedMass terminalMessage
  dyadicOriginalNorm dyadicUnitResponse centeredPair

section Finite

variable (stage t : Nat)

local notation "K" => headCutoff w+stage
local notation "f" => sourceCharacter width (SourceLoop.edges square) 1
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

/-- Original half-smoothed squared norm divided by its OWN original mass. -/
def originalOwnBlockVariance : Q' :=
  weightedMass w K width (polyMul b b) *
    Q'.recipPos Z0 (zeroPartition_positive hw0 hw1 width stage t)

/-- Original vacuum-subtracted cost divided by BOTH original masses. -/
def originalOwnBlockCost : Q' :=
  clearedRayleighCost w K width A b *
    Q'.recipPos (Z0*Z1) (Q'.mul_pos
      (zeroPartition_positive hw0 hw1 width stage t)
      (onePartition_positive hw0 hw1 width stage t))

private theorem variance_pin :
    originalOwnBlockVariance hw0 hw1 scale width hwidth stage t ≈
      centeredPair hw0 hw1 K width (Nat.le_add_right _ _) stage (2*t) f c := by
  simpa only [originalOwnBlockVariance, centeredPair, Nat.add_zero] using
    normalized_block_window_pin hw0 hw1 K width (Nat.le_add_right _ _) stage t 0
      (shifted_supported (sourceCharacter_supported width (square).edges 1) c)

private theorem cost_pin :
    originalOwnBlockCost hw0 hw1 scale width hwidth stage t ≈
      ownCenteredLagDifference hw0 hw1 width square (2*t) (2*t+1) stage stage := by
  let d := ownCenteredLagDifference hw0 hw1 width square (2*t) (2*t+1) stage stage
  let r := Q'.recipPos (Z0*Z1) (Q'.mul_pos
    (zeroPartition_positive hw0 hw1 width stage t)
    (onePartition_positive hw0 hw1 width stage t))
  have hpin : clearedRayleighCost w K width A b ≈ (Z0*Z1)*d := by
    simpa only [d, ownCenteredLagDifference, centeredPair] using
      clearedRayleighCost_window_pin hw0 hw1 K width (Nat.le_add_right _ _) stage t
      (shifted_supported (sourceCharacter_supported width (square).edges 1) c)
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

/-- The original denominator-side variance reaches the SAME norm times
unit response, not an auxiliary reflected or free-source norm. -/
theorem originalOwnBlockVariance_converges (t : Nat) :
    ConvergesTo (fun k => ofQ' (originalOwnBlockVariance hw0 hw1 scale width hwidth k t))
      (mul Norm (Response (2*t))) := by
  have h := TrigAddCReal.convergesTo_congr_seq
    (s := fun k => ofQ'
      (centeredPair hw0 hw1 (headCutoff w+k) width (Nat.le_add_right _ _) k (2*t)
        (sourceCharacter width (square).edges 1)
        (middleRatio hw0 hw1 (headCutoff w+k) width (Nat.le_add_right _ _) (k+1) k
          (sourceCharacter width (square).edges 1))))
    (t := fun k => ofQ' (originalOwnBlockVariance hw0 hw1 scale width hwidth k t))
    (hs := own_centeredPair_converges hw0 hw1 square (2*t))
    (fun k => SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.eqv_symm (variance_pin hw0 hw1 scale width hwidth k t)))
  have hmoment : Equiv (centeredTimeMoment hw0 hw1 (2*t) (loopState square) (loopState square))
      (mul Norm (Response (2*t))) :=
    (centeredTimeMoment_chronological_pin hw0 hw1 square (2*t)).trans
      (dyadicUnitResponse_cleared_pin hw0 hw1 scale width hwidth (2*t)).symm
  exact ArctanTrigConvergesProof.convergesTo_of_equiv h hmoment

/-- The exact finite producer numerator reaches the SAME cleared completed
lag difference. Its explicit diagonal Cauchy witness is already constructed. -/
theorem originalOwnBlockCost_converges (t : Nat) :
    ConvergesTo (fun k => ofQ' (originalOwnBlockCost hw0 hw1 scale width hwidth k t))
      (mul Norm (sub (Response (2*t)) (Response (2*t+1)))) :=
  ArctanTrigConvergesProof.convergesTo_of_equiv
    (TrigAddCReal.convergesTo_congr_seq
      (s := fun k => ofQ' (ownCenteredLagDifference hw0 hw1 width square (2*t) (2*t+1) k k))
      (fun k => SumOfSquares.Equiv_of_approx_eqv (fun _ =>
        Q'.eqv_symm (cost_pin hw0 hw1 scale width hwidth k t)))
      (ownCenteredLagDifference_converges hw0 hw1 width square (2*t) (2*t+1)))
    (dyadicUnitResponse_difference_cleared_pin hw0 hw1 scale width hwidth (2*t) (2*t+1)).symm

#print axioms originalOwnBlockVariance
#print axioms originalOwnBlockCost
#print axioms originalOwnBlockVariance_converges
#print axioms originalOwnBlockCost_converges

end YMGap.Continuum.BF4WilsonAllNomeDyadicOriginalRayleighLimit
