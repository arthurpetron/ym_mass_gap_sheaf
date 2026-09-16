/-
# Explicit cutoff-Cauchy control of the same completed ordinary-Haar transfer

The actual signed difference of two K*V weights has a computed small
certificate interval. Its signed-kernel norm bound applies on the dense
carrier and passes to arbitrary points of the existing completion. The
cutoff is uniform in the input vector, not in nome or spatial width.

This is an operator-norm Cauchy estimate, not yet construction of a limiting
operator, a stationary vacuum, physical OS identification or a strict gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferTail
import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedHaarTransfer
import YMGap.Continuum.SU2QuaternionHaarSignedKernelBound

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedCutoffControl

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferTail
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedHaarTransfer
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarBoundedCompletion
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation:max "N" width:arg => List.length (baseLinks width)

/-- A computed threshold for both actual finite-cutoff completions and the signed tail. -/
def transferCutoff (w : Q') (width : Nat) (epsilon : Q') : Nat :=
  max (headCutoff w) (stepTailCutoff w width epsilon)

/-- The same signed polynomial maps satisfy the norm-relative difference estimate. -/
theorem transferStep_difference_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (epsilon : Q') (he : (0 : Q') < epsilon) (K J : Nat)
    (hK : stepTailCutoff w width epsilon ≤ K) (hJ : stepTailCutoff w width epsilon ≤ J)
    {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    quaternionHaar (N width) (polyMul
      (polyAdd (transferStep w J width f) (polySmul (-1) (transferStep w K width f)))
      (polyAdd (transferStep w J width f) (polySmul (-1) (transferStep w K width f)))) ≤
      (epsilon*epsilon) * quaternionHaar (N width) (polyMul f f) := by
  have h := SU2QuaternionHaarSignedKernelBound.kernelMap_difference_bound
    (stepWeightDifferenceInterval hw0 hw1 width epsilon he K J hK hJ) hf
  have heq := (transferStep_kernelMap w J width f).add
    ((transferStep_kernelMap w K width f).smul (-1))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff (heq.mul heq))) h

private theorem completed_difference_bound {D : GNSData} {C E F : Q'}
    (T : BoundedMap D C) (U : BoundedMap D E)
    (bound : ∀ f, D.distSqQ (T.toFun f) (U.toFun f) ≤ (F*F)*D.B f f)
    (x : GNSCompletionSpace D) :
    CReal.RCle
      (D.cinnerCompl (D.cSub (T.completionMap x) (U.completionMap x))
        (D.cSub (T.completionMap x) (U.completionMap x)))
      (CReal.RCscale (F*F) (D.cinnerCompl x x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  change CReal.leEv
    (CReal.ofQ'CauchySeq _ (D.distSqSeqCauchy (T.mapCauchy X) (U.mapCauchy X)))
    (CReal.mul (CReal.ofQ' (F*F)) (D.cinnerRep X X))
  exact CReal.leEv_of_convergesTo_le
    (CReal.convergesTo_ofQ'CauchySeq _ (D.distSqSeqCauchy (T.mapCauchy X) (U.mapCauchy X)))
    (CReal.convergesTo_const_mul (CReal.ofQ' (F*F))
      (CReal.convergesTo_ofQ'CauchySeq _ (D.cInnerQCauchy X X)))
    (fun n => CReal.leEv_of_le (fun k => Q'.le_trans' _ _ _ (bound (X.seq n))
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt (Q'.invSucc_pos k)))))

private theorem dense_difference_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (epsilon : Q') (he : (0 : Q') < epsilon) (K J : Nat)
    (hK : transferCutoff w width epsilon ≤ K) (hJ : transferCutoff w width epsilon ≤ J)
    (f : (sliceData width).toGNSData.V) :
    (sliceData width).toGNSData.distSqQ
      ((denseTransfer hw0 hw1 J width (Nat.le_trans (Nat.le_max_left _ _) hJ)).toFun f)
      ((denseTransfer hw0 hw1 K width (Nat.le_trans (Nat.le_max_left _ _) hK)).toFun f) ≤
      (epsilon*epsilon) * (sliceData width).toGNSData.B f f := by
  let D := (sliceData width).toGNSData
  let a := (denseTransfer hw0 hw1 J width (Nat.le_trans (Nat.le_max_left _ _) hJ)).toFun f
  let b := (denseTransfer hw0 hw1 K width (Nat.le_trans (Nat.le_max_left _ _) hK)).toFun f
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haarData_pair (N width) (D.sub a b) (D.sub a b)))
    (Q'.le_trans' _ _ _
      (transferStep_difference_bound hw0 hw1 width epsilon he K J
        (Nat.le_trans (Nat.le_max_right _ _) hK) (Nat.le_trans (Nat.le_max_right _ _) hJ) f.property)
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (haarData_pair (N width) f f)))))

/-- Norm-relative cutoff control on EVERY point of the same completion.
The threshold depends only on nome, width and epsilon, not the input vector. -/
theorem completedTransfer_difference_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (epsilon : Q') (he : (0 : Q') < epsilon) (K J : Nat)
    (hK : transferCutoff w width epsilon ≤ K) (hJ : transferCutoff w width epsilon ≤ J)
    (x : GNSCompletionSpace (sliceData width).toGNSData) :
    CReal.RCle
      ((sliceData width).toGNSData.cinnerCompl
        ((sliceData width).toGNSData.cSub
          (completedTransfer hw0 hw1 J width (Nat.le_trans (Nat.le_max_left _ _) hJ) x)
          (completedTransfer hw0 hw1 K width (Nat.le_trans (Nat.le_max_left _ _) hK) x))
        ((sliceData width).toGNSData.cSub
          (completedTransfer hw0 hw1 J width (Nat.le_trans (Nat.le_max_left _ _) hJ) x)
          (completedTransfer hw0 hw1 K width (Nat.le_trans (Nat.le_max_left _ _) hK) x)))
      (CReal.RCscale (epsilon*epsilon) ((sliceData width).toGNSData.cinnerCompl x x)) :=
  completed_difference_bound
    (denseTransfer hw0 hw1 J width (Nat.le_trans (Nat.le_max_left _ _) hJ))
    (denseTransfer hw0 hw1 K width (Nat.le_trans (Nat.le_max_left _ _) hK))
    (dense_difference_bound hw0 hw1 width epsilon he K J hK hJ) x

end YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedCutoffControl

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedCutoffControl.transferCutoff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedCutoffControl.transferStep_difference_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedCutoffControl.completedTransfer_difference_bound
