/-
# Original product-heat score against the SAME centered variance

The two identical endpoint sources make the integrated first kernel response
zero. Centering therefore changes no score numerator. Applying the checked
coefficient-square bound to the centered test gives the exact original
normalized variance, not a second moment or a changed measure.

This remains a response inequality. It does not identify that response with
Wilson temporal jump energy, control the finite-P source correction, or give
scaling-uniform constants or a physical mass gap.
-/

import YMGap.Continuum.SU2QuaternionProductHeatCoefficientSquareScore
import YMGap.Continuum.SU2QuaternionProductHeatScoreCentering
import YMGap.Continuum.QuaternionHaarNormalizedCenter

namespace YMGap.Continuum.SU2QuaternionProductHeatScoreVariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionSignedAngularHeatResponse
open YMGap.Continuum.SU2QuaternionProductHeatAngularHessian
open YMGap.Continuum.SU2QuaternionAngularCoefficientSquareBudget
open YMGap.Continuum.SU2QuaternionHeatLogCurvature
open YMGap.Continuum.SU2QuaternionProductHeatCoefficientSquareScore
open YMGap.Continuum.SU2QuaternionProductHeatScoreCentering
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
open YMGap.Continuum.QuaternionHaarDensityVariance (normalizedMoment normalizedVariance)
open YMGap.Continuum.QuaternionHaarNormalizedCenter (center center_supported center_norm_identity)

local infix:50 " ≈ " => Q'.eqv

/-- The existing polynomial center has exactly the SAME normalized variance. -/
theorem normalized_center_square (blocks : Nat) (weight f : RatPoly)
    (hZ : (0 : Q') < quaternionHaar blocks weight) :
    Q'.recipPos (quaternionHaar blocks weight) hZ *
      quaternionHaar blocks (polyMul weight
        (polyMul (center blocks weight hZ f) (center blocks weight hZ f))) ≈
      normalizedVariance blocks weight f hZ := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (center_norm_identity blocks weight hZ f)) ?_
  exact poly_identity_of_normal_eq
    (.mul (.var 0) (.add (.var 1)
      (.neg (.mul (.mul (.var 2) (.var 2)) (.var 0)))))
    (.add (.mul (.var 1) (.var 0))
      (.neg (.mul (.mul (.var 2) (.var 0)) (.mul (.var 2) (.var 0)))))
    (by decide)
    (fun
      | 0 => Q'.recipPos (quaternionHaar blocks weight) hZ
      | 1 => quaternionHaar blocks (polyMul weight (polyMul f f))
      | _ => quaternionHaar blocks (polyMul weight f))

/-- Whole original score controlled by the original centered variance, with
explicit local term multiplicity and repeated-factor coefficient budget. -/
theorem productHeat_normalized_coefficientSquare_variance_bound
    (n : Nat) (terms : List (AngularTerm n)) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : relativeCutoff w 32 ≤ K)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    (m : Nat)
    (hlocal : ∀ i, i ∈ ids →
      (terms.filter (fun t => decide (t.block.val = i))).length ≤ m)
    (a f : RatPoly) (ha : SupportedQuaternionBlocks n a)
    (A : Certificate n a) (hf : SupportedQuaternionBlocks (n+n) f)
    (hZ : (0 : Q') < quaternionHaar (n+n)
      (polyMul (polyMul a (liftBoundary n a)) (productHeat n w K ids))) :
    let W := productHeat n w K ids
    let d := signedAngularDirection (upperTerms terms) W
    let R := polyMul a (liftBoundary n a)
    let r := Q'.recipPos (quaternionHaar (n+n) (polyMul R W)) hZ
    (r*quaternionHaar (n+n) (polyMul R (polyMul d f))) *
        (r*quaternionHaar (n+n) (polyMul R (polyMul d f))) ≤
      ((Q'.ofNat m * logCurvatureCap w hw0 hw1) *
        productCoefficientSquareSum terms ids) *
        normalizedVariance (n+n) (polyMul R W) f hZ := by
  let W := productHeat n w K ids
  let d := signedAngularDirection (upperTerms terms) W
  let R := polyMul a (liftBoundary n a)
  let r := Q'.recipPos (quaternionHaar (n+n) (polyMul R W)) hZ
  let f0 := center (n+n) (polyMul R W) hZ f
  have hf0 := center_supported (n+n) (polyMul R W) hZ hf
  have hbound := productHeat_normalized_coefficientSquare_score_bound
    n terms hw0 hw1 K hK ids hids m hlocal a f0 ha A hf0 hZ
  have hshift : quaternionHaar (n+n) (polyMul R (polyMul d f0)) ≈
      quaternionHaar (n+n) (polyMul R (polyMul d f)) := by
    exact productHeat_upperDirection_center_congr n terms w K ids hids a ha f hf
      (normalizedMoment (n+n) (polyMul R W) f hZ)
  have hscaled := Q'.mul_eqv_congr_left r _ _ hshift
  have hsquare := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hscaled)
    (Q'.mul_eqv_congr_left _ _ _ hscaled)
  have hvariance : r * quaternionHaar (n+n)
      (polyMul R (polyMul W (polyMul f0 f0))) ≈
      normalizedVariance (n+n) (polyMul R W) f hZ :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left r _ _ (haar_of_coeff
        (RatPolyCoeffEqv.mul_assoc R W (polyMul f0 f0)).symm))
      (normalized_center_square (n+n) (polyMul R W) f hZ)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hsquare)
    (Q'.le_trans' _ _ _ hbound
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hvariance)))

end YMGap.Continuum.SU2QuaternionProductHeatScoreVariance

#print axioms YMGap.Continuum.SU2QuaternionProductHeatScoreVariance.normalized_center_square
#print axioms YMGap.Continuum.SU2QuaternionProductHeatScoreVariance.productHeat_normalized_coefficientSquare_variance_bound
