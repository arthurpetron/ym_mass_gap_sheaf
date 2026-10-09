/-
The exact centered paired Ward identity at a selected quaternion block.
The derivative of the full weight is retained, and the constant center is
annihilated coefficientwise before integrating. No positivity is used.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFisherMean
import YMGap.Continuum.QPolyHaarPairedAtFrozenZero
import YMGap.Continuum.QPolyHaarPairedAtFrozenProduct

namespace YMGap.Continuum.QPolyHaarPairedAtCenteredWard

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter (HasQuaternionBlockDegree)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (quaternionBlockIndependent_polyOne quaternionBlockIndependent_polySmul)
open YMGap.Continuum.SU2QuaternionPairedFrameAt (pairedDerivativeAt)
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (threeSum)
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (threeSquare)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QPolyHaarFrozenChain (threeSum_congr)
open YMGap.Continuum.QPolyHaarPairedAtFrozenChain (frozenFirstAt pairedAt_mul)
open YMGap.Continuum.QPolyHaarPairedAtFrozenProduct (pairedAt_add frozenFirstAt_mul)
open YMGap.Continuum.QPolyHaarPairedAtFrozenZero (pairedAt_independent_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFisherMean (paired_linear_mean_ward)

local infix:50 " ≈ " => Q'.eqv

/-- Subtracting a scalar from a polynomial does not change a selected-block
paired derivative, including its signed middle plane. -/
theorem pairedAt_centered (s : Nat) (i : Fin 3) (f : RatPoly) (c : Q') :
    RatPolyCoeffEqv
      (pairedDerivativeAt s i (polyAdd f (polySmul (-c) polyOne)))
      (pairedDerivativeAt s i f) := by
  have hz : RatPolyCoeffEqv
      (pairedDerivativeAt s i (polySmul (-c) polyOne)) polyZero :=
    pairedAt_independent_zero s i
      (quaternionBlockIndependent_polySmul (-c)
        (quaternionBlockIndependent_polyOne s))
  exact (pairedAt_add s i f (polySmul (-c) polyOne)).trans
    (((RatPolyCoeffEqv.refl _).add hz).trans (RatPolyCoeffEqv.add_zero _))

/-- The frozen direction is the actual gradient, so its derivative of the
centered observable is exactly its three-square energy coefficientwise. -/
theorem frozenFirstAt_centered_gradient (s : Nat) (f : RatPoly) (c : Q') :
    RatPolyCoeffEqv
      (frozenFirstAt s (fun i => pairedDerivativeAt s i f)
        (polyAdd f (polySmul (-c) polyOne)))
      (threeSquare (fun i => pairedDerivativeAt s i f)) :=
  threeSum_congr (fun i =>
    (pairedAt_centered s i f c).mul_left (pairedDerivativeAt s i f))

private theorem haar_three (blocks : Nat) (f : Fin 3 → RatPoly) :
    quaternionHaar blocks (threeSum f) ≈
      quaternionHaar blocks (f 0) +
        (quaternionHaar blocks (f 1) + quaternionHaar blocks (f 2)) :=
  Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (quaternionHaar_append blocks _ _))

/-- The full-weight derivative and the selected energy have the exact signed
centered Ward balance, with the original product Haar and no zero-mean
assumption on the chosen center. -/
theorem pairedAt_centered_ward {blocks s : Nat} (hs : s < blocks)
    (W f : RatPoly) (c : Q')
    (hf : SupportedQuaternionBlocks blocks f)
    (hdegree : HasQuaternionBlockDegree s 1 f) :
    let h := polyAdd f (polySmul (-c) polyOne)
    let u := fun i => pairedDerivativeAt s i f
    quaternionHaar blocks (polyMul W (threeSquare u)) +
      quaternionHaar blocks (polyMul (frozenFirstAt s u W) h) ≈
    3*quaternionHaar blocks (polyMul W (polyMul h f)) := by
  let h := polyAdd f (polySmul (-c) polyOne)
  let u := fun i => pairedDerivativeAt s i f
  have hfirst : RatPolyCoeffEqv
      (frozenFirstAt s u (polyMul W h))
      (polyAdd (polyMul W (threeSquare u))
        (polyMul (frozenFirstAt s u W) h)) :=
    (frozenFirstAt_mul s u W h).trans
      (((RatPolyCoeffEqv.refl _).add
        ((frozenFirstAt_centered_gradient s f c).mul_left W)).trans
        (RatPolyCoeffEqv.add_comm _ _))
  have hleft : quaternionHaar blocks (frozenFirstAt s u (polyMul W h)) ≈
      quaternionHaar blocks (polyMul W (threeSquare u)) +
        quaternionHaar blocks (polyMul (frozenFirstAt s u W) h) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff hfirst)
      (quaternionHaar_append blocks _ _)
  have hward :
      quaternionHaar blocks
          (polyMul (pairedDerivativeAt s 0 (polyMul W h)) (u 0)) +
        (quaternionHaar blocks
          (polyMul (pairedDerivativeAt s 1 (polyMul W h)) (u 1)) +
         quaternionHaar blocks
          (polyMul (pairedDerivativeAt s 2 (polyMul W h)) (u 2))) ≈
      3*quaternionHaar blocks (polyMul (polyMul W h) f) :=
    paired_linear_mean_ward hs (polyMul W h) f hf hdegree
  have hthree : quaternionHaar blocks (frozenFirstAt s u (polyMul W h)) ≈
      quaternionHaar blocks
          (polyMul (pairedDerivativeAt s 0 (polyMul W h)) (u 0)) +
        (quaternionHaar blocks
          (polyMul (pairedDerivativeAt s 1 (polyMul W h)) (u 1)) +
         quaternionHaar blocks
          (polyMul (pairedDerivativeAt s 2 (polyMul W h)) (u 2))) :=
    Q'.eqv_trans _ _ _
      (haar_three blocks (fun i => polyMul (u i)
        (pairedDerivativeAt s i (polyMul W h))))
      (Q'.add_eqv_congr'
        (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
        (Q'.add_eqv_congr'
          (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
          (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft)
    (Q'.eqv_trans _ _ _ hthree
      (Q'.eqv_trans _ _ _ hward
        (Q'.mul_eqv_congr_left 3 _ _
          (haar_of_coeff (RatPolyCoeffEqv.mul_assoc W h f)))))

end YMGap.Continuum.QPolyHaarPairedAtCenteredWard

#print axioms YMGap.Continuum.QPolyHaarPairedAtCenteredWard.pairedAt_centered
#print axioms YMGap.Continuum.QPolyHaarPairedAtCenteredWard.frozenFirstAt_centered_gradient
#print axioms YMGap.Continuum.QPolyHaarPairedAtCenteredWard.pairedAt_centered_ward
