/-
# Same-action plaquette time-correlator equality for the Wilson carrier

At radius zero, the literal separated Wilson loop probes are coefficient-
equivalent to the existing face-character probes, for every physical lag.
Their joint and marginal cutoff expectations have the SAME selected action,
extent and partition. Thus their finite connected scalars agree exactly.

Their separate existing three-regulator diagonal convergence witnesses then
identify the original limiting connected scalars. No equality of moduli,
interchange of limits, whole-carrier isomorphism or additional estimate is
used. The consumer is positive nonzero-time response on the actual Wilson
completion. This fixed-spacing scalar pin is not continuum/OS/QFT closure.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteForm
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonUniformConnectedDecay
import YMGap.Continuum.BF4ExactSlabFixedSpatialUniformConnectedDecay
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredTimeMoments
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredForm

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteTimePin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceCharacter (faceSpan faceSpan_radius)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette (recentered_fundamental_placedSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteForm (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalVariance (recenter_faceSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSeparatedProbeControl (upperProbe lowerProbe)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOriginalConnectedCorrelator
  (connectedScalar connectedScalar_time_converges)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredTimeMoments (centeredTimeMoment)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth recenter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (physicalTime)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes (chartExtent chartIds chartIds_physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredForm
  (spatialCenteredMoment originalConnected_diagonal_converges)
open YMGap.Continuum.BF4ExactSlabSelectedTwoProbeCovariance (finiteValue_coeff_congr)
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse (finiteCovariance)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential (RatPolyCoeffEqv)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

local infix:50 " ≈ " => Q'.eqv

/-- The reflected endpoint keeps its actual lag, orientation and recentered face. -/
theorem upperProbe_plaquette {base : Nat} (face : Z4Plaq) (hf : face ∈ spatialFaces base)
    (r n t : Nat) :
    RatPolyCoeffEqv (upperProbe base r 0 n t (plaquette face hf))
      (BF4ExactSlabFixedSpatialSeparatedProbeControl.upperProbe base r 0 n t
        (faceSpan base face hf)) := by
  unfold upperProbe BF4ExactSlabFixedSpatialSeparatedProbeControl.upperProbe
  rw [recenter_faceSpan base face hf r]
  exact recentered_fundamental_placedSpan (space := r+1)
    (by unfold paddedWidth; omega : base+(r+1) ≤ paddedWidth base r)
    (chartExtent base r (0+n) t) (paddedWidth base r+1+t+(0+n)) face hf

/-- The other endpoint is compared separately, with no reflection-plane shift. -/
theorem lowerProbe_plaquette {base : Nat} (face : Z4Plaq) (hf : face ∈ spatialFaces base)
    (r n t : Nat) :
    RatPolyCoeffEqv (lowerProbe base r 0 n t (plaquette face hf))
      (BF4ExactSlabFixedSpatialSeparatedProbeControl.lowerProbe base r 0 n t
        (faceSpan base face hf)) := by
  unfold lowerProbe BF4ExactSlabFixedSpatialSeparatedProbeControl.lowerProbe
  rw [recenter_faceSpan base face hf r]
  exact recentered_fundamental_placedSpan (space := r+1)
    (by unfold paddedWidth; omega : base+(r+1) ≤ paddedWidth base r)
    (chartExtent base r (0+n) t) (paddedWidth base r+1+t) face hf

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

/-- All three expectations use the identical finite original action and partition. -/
theorem connectedScalar_plaquette_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (face : Z4Plaq) (hf : face ∈ spatialFaces base) (r stage t n : Nat) :
    connectedScalar hw0 hw1 n r stage t (plaquette face hf) (advance n (plaquette face hf)) ≈
      BF4ExactSlabFixedSpatialOriginalConnectedCorrelator.connectedScalar hw0 hw1
        (paddedWidth base r) stage n (recenter r (faceSpan base face hf))
        (physicalTime n (recenter r (faceSpan base face hf))) t := by
  have hp := upperProbe_plaquette face hf r n t
  have hq := lowerProbe_plaquette face hf r n t
  have hcov : finiteCovariance w hw0 hw1 (chartExtent base r (0+n) t)
      (chartIds base r (0+n) t) (fun _ hi => chartIds_physical hi)
      (upperProbe base r 0 n t (plaquette face hf))
      (lowerProbe base r 0 n t (plaquette face hf)) stage ≈
    finiteCovariance w hw0 hw1 (chartExtent base r (0+n) t)
      (chartIds base r (0+n) t) (fun _ hi => chartIds_physical hi)
      (BF4ExactSlabFixedSpatialSeparatedProbeControl.upperProbe base r 0 n t (faceSpan base face hf))
      (BF4ExactSlabFixedSpatialSeparatedProbeControl.lowerProbe base r 0 n t (faceSpan base face hf)) stage := by
    unfold finiteCovariance
    apply Q'.add_eqv_congr'
    · exact finiteValue_coeff_congr w hw0 hw1 _ _ _ _ _ (hp.mul hq) stage
    · exact Q'.neg_eqv_congr _ _ (qmul
        (finiteValue_coeff_congr w hw0 hw1 _ _ _ _ _ hp stage)
        (finiteValue_coeff_congr w hw0 hw1 _ _ _ _ _ hq stage))
  have hnew := BF4ExactSlabFixedSpatialWilsonUniformConnectedDecay.connectedScalar_selected_pin
    hw0 hw1 base r 0 n t stage (plaquette face hf) (plaquette face hf)
    (Nat.le_refl 0) (Nat.le_refl 0)
  have hold := BF4ExactSlabFixedSpatialUniformConnectedDecay.connectedScalar_selected_pin
    hw0 hw1 base r 0 n t stage (faceSpan base face hf) (faceSpan base face hf) (Nat.le_refl 0)
  simpa only [Nat.zero_add] using Q'.eqv_trans _ _ _ hnew (Q'.eqv_trans _ _ _ hcov (Q'.eqv_symm hold))

attribute [local irreducible] connectedScalar
  BF4ExactSlabFixedSpatialOriginalConnectedCorrelator.connectedScalar
  BF4ExactSlabFixedSpatialWilsonIntrinsicForm.intrinsicForm
  BF4ExactSlabFixedSpatialSpatialPairingLaws.spatialPairing

/-- Fixed physical lag; the original three regulators recede on their unchanged diagonal. -/
theorem centeredTimeMoment_plaquette_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {base : Nat} (hb : 0<base) (face : Z4Plaq) (hf : face ∈ spatialFaces base) (n : Nat) :
    Equiv (centeredTimeMoment hw0 hw1 hsmall hd hs hb n (plaquette face hf) (plaquette face hf))
      (spatialCenteredMoment hw0 hw1 base hsmall hd hs hb n
        (faceSpan base face hf) (faceSpan base face hf)) := by
  apply Equiv_of_limit_of_equal
    (bSeq := fun k => ofQ'
      (BF4ExactSlabFixedSpatialOriginalConnectedCorrelator.connectedScalar hw0 hw1
        (paddedWidth base k) k n (recenter k (faceSpan base face hf))
        (physicalTime n (recenter k (faceSpan base face hf))) k))
    (fun k => SumOfSquares.Equiv_of_approx_eqv
      (fun _ => connectedScalar_plaquette_pin hw0 hw1 face hf k k k n))
    (connectedScalar_time_converges hw0 hw1 hsmall hd hs hb n n
      (plaquette face hf) (plaquette face hf) (Nat.zero_le n) (by simp only [plaquette, Nat.zero_add, Nat.le_refl]))
  apply originalConnected_diagonal_converges hw0 hw1 base hsmall hd hs hb n n
    (faceSpan base face hf) (faceSpan base face hf) (Nat.zero_le n)
  exact Nat.le_trans
    (BF4ExactSlabFixedSpatialPhysicalTimeShift.radius_advance_le n (faceSpan base face hf).val)
    (by simp only [faceSpan_radius, Nat.zero_add, Nat.le_refl])

#print axioms upperProbe_plaquette
#print axioms lowerProbe_plaquette
#print axioms connectedScalar_plaquette_pin
#print axioms centeredTimeMoment_plaquette_pin

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteTimePin
