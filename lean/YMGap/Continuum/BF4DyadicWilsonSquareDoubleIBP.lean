/-
The ordered double-IBP source of the literal padded Wilson-square character.
The existing selected-link head swap supplies the exact degree-one source and
the original carrier amplitude four. No density is changed or integrated here.
-/

import YMGap.Continuum.QuaternionHaarPairedLinearDoubleIBP
import YMGap.Continuum.BF4DyadicWilsonSquareWardMoments
import YMGap.Continuum.QuaternionHaarPairedHessianTrace

namespace YMGap.Continuum.BF4DyadicWilsonSquareDoubleIBP

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPairedFrameAt (pairedDerivativeAt_zero)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (angularSquare)
open YMGap.Continuum.QuaternionHaarPairedHessianTrace (paired_gradient_square_pin)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.BF4ExactSlabSelectedFaceFold (blockDegree_reindex)
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
  (headSwapBlockInvolution headSwapBlockInvolution_map_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (sourceCharacter)
open YMGap.Continuum.BF4DyadicWilsonSquare (paddedSquare side)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelPartition
  (observableBlocks observableBlocks_lt)
open YMGap.Continuum.BF4DyadicWilsonSquareWardMoments (paddedSquare_head_gamma)
open YMGap.Continuum.QuaternionHaarPairedLinearDoubleIBP

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks

/-- Exact selected-link source pin for the literal head-swapped padded Wilson
square. The ordered derivatives act on its character before any weighting. -/
theorem paddedSquare_doubleIBPSource_amplitude (scale width : Nat)
    (hwidth : side scale < width) (block : Nat)
    (hb : block ∈ observableBlocks scale width hwidth) :
    let swap := headSwapBlockInvolution (N width) block
      (observableBlocks_lt scale width hwidth block hb)
    let f := reindexQuaternionPolynomial swap
      (sourceCharacter width (paddedSquare scale width hwidth).edges 1)
    HaarCarrierEqv (N width) (doubleIBPSource f)
      (polyAdd (polySmul 12 (cap 4))
        (polySmul (-16) (gradientSquare f))) := by
  dsimp only
  let p := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let hidx := observableBlocks_lt scale width hwidth block hb
  let swap := headSwapBlockInvolution (N width) block hidx
  let f := reindexQuaternionPolynomial swap p
  have h0 : 0 < N width := Nat.lt_of_le_of_lt (Nat.zero_le block) hidx
  have hdegree : HasQuaternionBlockDegree 0 1 f :=
    blockDegree_reindex swap h0 (headSwapBlockInvolution_map_zero _ _ _)
      (BF4DyadicWilsonSquareVarianceTaylor.paddedSquare_character_degree
        scale width hwidth block hb)
  have hgamma : HaarCarrierEqv (N width) (gradientSquare f)
      (polyAdd (cap 4) (polyNeg (polyMul f f))) := by
    have hcoeff : RatPolyCoeffEqv (gradientSquare f) (angularSquare f) := by
      simpa only [gradientSquare, gradient, pairedDerivativeAt_zero,
        Nat.mul_zero, Nat.zero_add, angularSquare] using
        (paired_gradient_square_pin 0 f)
    have h := paddedSquare_head_gamma scale width hwidth block hb
    change HaarCarrierEqv (N width) (angularSquare f)
      (polyAdd (cap 4) (polyNeg (polyMul f f))) at h
    exact (RatPolyCoeffEqv.haarCarrier hcoeff).trans h
  have hamp : HaarCarrierEqv (N width)
      (polyAdd (polyMul f f) (gradientSquare f)) (cap 4) :=
    (HaarCarrierEqv.add (HaarCarrierEqv.refl (N width) (polyMul f f)) hgamma).trans
      (RatPolyCoeffEqv.haarCarrier (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.var 0))
          (.add (.var 1) (.neg (.mul (.var 0) (.var 0)))))
        (.var 1) (by decide) (fun | 0 => f | _ => cap 4)))
  have hconstant : HasQuaternionBlockDegree 0 0 (cap 4) :=
    (hasQuaternionBlockDegree_one 0).smul 4
  exact doubleIBPSource_amplitude_pin h0 f (cap 4) hdegree hconstant hamp

/-- Equivalent integer-cap normalization of the same actual source. -/
theorem paddedSquare_doubleIBPSource_48 (scale width : Nat)
    (hwidth : side scale < width) (block : Nat)
    (hb : block ∈ observableBlocks scale width hwidth) :
    let swap := headSwapBlockInvolution (N width) block
      (observableBlocks_lt scale width hwidth block hb)
    let f := reindexQuaternionPolynomial swap
      (sourceCharacter width (paddedSquare scale width hwidth).edges 1)
    HaarCarrierEqv (N width) (doubleIBPSource f)
      (polyAdd (cap 48) (polySmul (-16) (gradientSquare f))) := by
  dsimp only
  let p := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let hidx := observableBlocks_lt scale width hwidth block hb
  let swap := headSwapBlockInvolution (N width) block hidx
  let f := reindexQuaternionPolynomial swap p
  have h := paddedSquare_doubleIBPSource_amplitude scale width hwidth block hb
  change HaarCarrierEqv (N width) (doubleIBPSource f)
    (polyAdd (polySmul 12 (cap 4)) (polySmul (-16) (gradientSquare f))) at h
  have hc : RatPolyCoeffEqv (polySmul 12 (cap 4)) (cap 48) :=
    (RatPolyCoeffEqv.smul_assoc 12 4 polyOne).trans
      (RatPolyCoeffEqv.smul_coefficient
        (by decide : Q'.eqv (12 * 4) 48) polyOne)
  exact h.trans (RatPolyCoeffEqv.haarCarrier
    (hc.add (RatPolyCoeffEqv.refl _)))

end YMGap.Continuum.BF4DyadicWilsonSquareDoubleIBP

#print axioms YMGap.Continuum.BF4DyadicWilsonSquareDoubleIBP.paddedSquare_doubleIBPSource_amplitude
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareDoubleIBP.paddedSquare_doubleIBPSource_48
