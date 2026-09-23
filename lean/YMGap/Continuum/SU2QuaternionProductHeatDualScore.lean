/-
# Whole original product heat: a normalized signed dual score

The whole signed direction is estimated at once. All local mixed terms and
both complete endpoint sources remain. The only cost is the additive
block-local curvature budget; the finite product floor is used for integrated
cancellation but introduces no additional factor into the final bound.
-/

import YMGap.Continuum.SU2QuaternionProductHeatSignedLogCurvature
import YMGap.Continuum.SU2QuaternionProductHeatPositiveFloor
import YMGap.Continuum.SU2QuaternionRelativeHeatDualScore

namespace YMGap.Continuum.SU2QuaternionProductHeatDualScore

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionSignedAngularHeatResponse
open YMGap.Continuum.SU2QuaternionProductHeatAngularHessian
open YMGap.Continuum.SU2QuaternionProductHeatSignedLogCurvature
open YMGap.Continuum.SU2QuaternionProductHeatPositiveFloor
open YMGap.Continuum.SU2QuaternionHeatLogCurvature
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
open YMGap.Continuum.QuaternionHaarCurvatureDualBound
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor)

/-- Whole-direction dual estimate for the actual selected product kernel.
Repeated directions and factors are allowed and retain their local costs. -/
theorem productHeat_dual_score_bound
    (n : Nat) (terms : List (AngularTerm n)) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : relativeCutoff w 32 ≤ K)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    (a f : RatPoly) (ha : SupportedQuaternionBlocks n a)
    (A : Certificate n a) (hf : SupportedQuaternionBlocks (n+n) f) :
    let W := productHeat n w K ids
    let d := signedAngularDirection (upperTerms terms) W
    let R := polyMul a (liftBoundary n a)
    quaternionHaar (n+n) (polyMul R (polyMul d f)) *
        quaternionHaar (n+n) (polyMul R (polyMul d f)) ≤
      quaternionHaar (n+n) (polyMul R (polyMul W (polyMul f f))) *
        (productCurvatureCost terms (logCurvatureCap w hw0 hw1) ids *
          quaternionHaar (n+n) (polyMul R W)) := by
  let W := productHeat n w K ids
  have hW := productHeat_supported n w K ids hids
  have hd := signedAngularDirection_supported (upperTerms terms) hW
  have hdd := signedAngularDirection_supported (upperTerms terms) hd
  let I := polynomialInterval (n+n) W hW
  let ell := headFloor w ^ ids.length
  let u := ell + polynomialCap W
  have hell : (0 : Q') < ell := productFloor_positive hw0 hw1 ids
  have hle : ell ≤ u := Q'.add_le_self_of_nonneg _ _ I.nonnegative
  have hu : (0 : Q') < u := Q'.pos_of_lt_of_le hell hle
  let U : Certificate (n+n) (polyAdd (cap u) (polyNeg W)) :=
    Certificate.ofCoeff
      (((cap_add ell _).symm.add (RatPolyCoeffEqv.refl _)).trans
        (coeffEvalExpr_eqv_of_normalize_eq
          (.add (.add (.var 0) (.var 1)) (.neg (.var 2)))
          (.add (.var 0) (.add (.var 1) (.neg (.var 2)))) (by decide)
          (fun | 0 => cap ell | 1 => cap (polynomialCap W) | _ => W)))
      ((Certificate.constant (n+n) ell (Q'.le_of_lt hell)).add I.upper)
  exact curvature_dual_bound hW hd hdd hf hell hu hle
    (productHeat_floorCertificate n hw0 hw1 K
      (Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK) ids hids) U
    ((certificate_extend n ha A).mul (lift_certificate n A))
    (productHeat_signedCurvature n terms hw0 hw1 K hK ids hids)
    (productHeat_upperHessian_nonpositive n terms w (Q'.le_of_lt hw0) K ids hids a ha)

/-- Same original positive edge mass on both sides; no factorwise
normalization or discarded mixed term. The positive-mass premise does not
assign a normalized law to the zero-source case. -/
theorem productHeat_normalized_dual_score_bound
    (n : Nat) (terms : List (AngularTerm n)) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : relativeCutoff w 32 ≤ K)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n)
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
      productCurvatureCost terms (logCurvatureCap w hw0 hw1) ids *
        (r*quaternionHaar (n+n) (polyMul R (polyMul W (polyMul f f)))) :=
  RationalQuadraticDiscriminant.normalize_squared_bound _ _ _ _ hZ
    (productHeat_dual_score_bound n terms hw0 hw1 K hK ids hids a f ha A hf)

end YMGap.Continuum.SU2QuaternionProductHeatDualScore

#print axioms YMGap.Continuum.SU2QuaternionProductHeatDualScore.productHeat_dual_score_bound
#print axioms YMGap.Continuum.SU2QuaternionProductHeatDualScore.productHeat_normalized_dual_score_bound
