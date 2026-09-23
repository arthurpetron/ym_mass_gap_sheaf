/-
# Centering the whole product-heat angular score

The first signed angular response of the actual product heat has zero mean
against two identical endpoint sources.  Consequently subtracting any scalar
from a test leaves its score response unchanged.  This is a finite original-
kernel identity, not a Wilson-jump or physical-gap statement.
-/

import YMGap.Constructive.CauchyConv
import YMGap.Continuum.SU2QuaternionProductHeatDualScore
import YMGap.Continuum.QuaternionHaarNormalizedCenter

namespace YMGap.Continuum.SU2QuaternionProductHeatScoreCentering

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.SU2QuaternionSignedAngularHeatResponse
open YMGap.Continuum.SU2QuaternionProductHeatAngularHessian
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarAngularCarrier

local infix:50 " ≈ " => Q'.eqv

/-- The first whole upper angular response of the actual product kernel has
zero Haar mean against two copies of any signed supported source. -/
theorem productHeat_upperDirection_mean_zero
    (n : Nat) (terms : List (AngularTerm n)) (w : Q') (K : Nat)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    (a : RatPoly) (ha : SupportedQuaternionBlocks n a) :
    quaternionHaar (n+n)
      (polyMul (polyMul a (liftBoundary n a))
        (signedAngularDirection (upperTerms terms)
          (productHeat n w K ids))) ≈ 0 := by
  let A := polyMul a (liftBoundary n a)
  let W := productHeat n w K ids
  let D := signedAngularDirection terms a
  let U := upperTerms terms
  have hDa : SupportedQuaternionBlocks n D :=
    signedAngularDirection_supported terms ha
  have hskew := kineticPair_signedAngular_sum_zero
    n terms w K ids hids a a ha ha
  have hsymm := kineticPair_symm n w K ids hids D a hDa ha
  have htwice : (Q'.ofNat 2) * kineticPair n w K ids D a ≈ 0 :=
    Q'.eqv_trans _
      (kineticPair n w K ids D a + kineticPair n w K ids D a) _
      (poly_identity_of_normal_eq
        (.mul (.const 2) (.var 0))
        (.add (.var 0) (.var 0)) (by decide)
        (fun _ => kineticPair n w K ids D a))
      (Q'.eqv_trans _
        (kineticPair n w K ids D a + kineticPair n w K ids a D) _
        (Q'.add_eqv_congr' (Q'.eqv_refl _) hsymm)
        hskew)
  have hzero : kineticPair n w K ids D a ≈ 0 :=
    Q'.mul_eqv_zero_of_pos (Q'.ofNat_succ_pos 1) htwice
  have hsource := upperDirection_source terms a a ha
  have hinterior : quaternionHaar (n+n)
      (polyMul (signedAngularDirection U A) W) ≈ 0 :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (hsource.mul_right W))
      (Q'.eqv_trans _ _ _
        (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
        (Q'.eqv_trans _ _ _
          (Q'.eqv_symm (productMap_pairing n w K ids a D)) hzero))
  exact Q'.eqv_trans _ _ _ (signedAngular_haar_pair U A W)
    (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hinterior)
      (by change -(0 : Q') ≈ 0; decide))

/-- Subtracting an arbitrary scalar from a supported two-slice test leaves
the whole product-kernel score response unchanged. -/
theorem productHeat_upperDirection_center_congr
    (n : Nat) (terms : List (AngularTerm n)) (w : Q') (K : Nat)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    (a : RatPoly) (ha : SupportedQuaternionBlocks n a)
    (f : RatPoly) (_hf : SupportedQuaternionBlocks (n+n) f) (c : Q') :
    let R := polyMul a (liftBoundary n a)
    let d := signedAngularDirection (upperTerms terms) (productHeat n w K ids)
    let centered := polyAdd f (polyNeg (cap c))
    quaternionHaar (n+n) (polyMul R (polyMul d centered)) ≈
      quaternionHaar (n+n) (polyMul R (polyMul d f)) := by
  let R := polyMul a (liftBoundary n a)
  let d := signedAngularDirection (upperTerms terms) (productHeat n w K ids)
  have hz : quaternionHaar (n+n) (polyMul R d) ≈ 0 :=
    productHeat_upperDirection_mean_zero n terms w K ids hids a ha
  have hneg : RatPolyCoeffEqv (polyNeg (cap c)) (polySmul (-c) polyOne) :=
    (neg_smul (cap c)).trans
      ((RatPolyCoeffEqv.smul_assoc (-1) c polyOne).trans
        (RatPolyCoeffEqv.smul_coefficient
          (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0))
            (.neg (.var 0)) (by decide) (fun _ => c)) polyOne))
  have hconstant : RatPolyCoeffEqv
      (polyMul R (polyMul d (polyNeg (cap c))))
      (polySmul (-c) (polyMul R d)) :=
    ((((hneg.mul_left d).trans
        (RatPolyCoeffEqv.polyMul_smul_right (-c) d polyOne)).trans
        ((RatPolyCoeffEqv.mul_one d).smul (-c))).mul_left R).trans
      (RatPolyCoeffEqv.polyMul_smul_right (-c) R d)
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff
      (((RatPolyCoeffEqv.mul_add_right d f (polyNeg (cap c))).mul_left R).trans
        (RatPolyCoeffEqv.mul_add_right R (polyMul d f)
          (polyMul d (polyNeg (cap c))))))
    (Q'.eqv_trans _ _ _ (quaternionHaar_append (n+n) _ _)
      (Q'.eqv_trans _
        (quaternionHaar (n+n) (polyMul R (polyMul d f)) +
          ((-c) * quaternionHaar (n+n) (polyMul R d))) _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.eqv_trans _ _ _ (haar_of_coeff hconstant)
            (quaternionHaar_polySmul (n+n) (-c) (polyMul R d))))
        (Q'.eqv_trans _
          (quaternionHaar (n+n) (polyMul R (polyMul d f)) + (-c)*0) _
          (Q'.add_eqv_congr' (Q'.eqv_refl _)
            (Q'.mul_eqv_congr_left (-c) _ _ hz))
          (poly_identity_of_normal_eq
            (.add (.var 0) (.mul (.var 1) (.const 0))) (.var 0)
            (by decide)
            (fun i => if i = 0 then
              quaternionHaar (n+n) (polyMul R (polyMul d f)) else -c)))))

end YMGap.Continuum.SU2QuaternionProductHeatScoreCentering

#print axioms YMGap.Continuum.SU2QuaternionProductHeatScoreCentering.productHeat_upperDirection_mean_zero
#print axioms YMGap.Continuum.SU2QuaternionProductHeatScoreCentering.productHeat_upperDirection_center_congr
