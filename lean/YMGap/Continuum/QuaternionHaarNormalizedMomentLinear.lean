/-
# Exact linearity and reweighting for normalized original Haar moments

These are finite polynomial identities.  The only inverses are the supplied
positive Haar masses; no new density or probability-law assumption is added.
-/

import YMGap.Continuum.QuaternionHaarNormalizedMomentCongruence

namespace YMGap.Continuum.QuaternionHaarNormalizedMomentLinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarNormalizedMomentCongruence
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

local infix:50 " ≈ " => Q'.eqv

theorem normalizedMoment_add {blocks : Nat} {W p q : RatPoly}
    (hW : (0 : Q') < quaternionHaar blocks W) :
    normalizedMoment blocks W (polyAdd p q) hW ≈
      normalizedMoment blocks W p hW + normalizedMoment blocks W q hW := by
  have hnum :
      quaternionHaar blocks (polyMul W (polyAdd p q)) ≈
        quaternionHaar blocks (polyMul W p) +
          quaternionHaar blocks (polyMul W q) :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.mul_add_right W p q))
      (quaternionHaar_append blocks _ _)
  unfold normalizedMoment
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hnum)
    (Q'.add_mul_eqv _ _ _)

theorem normalizedMoment_smul {blocks : Nat} {W p : RatPoly} {c : Q'}
    (hW : (0 : Q') < quaternionHaar blocks W) :
    normalizedMoment blocks W (polySmul c p) hW ≈
      c * normalizedMoment blocks W p hW := by
  have hnum :
      quaternionHaar blocks (polyMul W (polySmul c p)) ≈
        c * quaternionHaar blocks (polyMul W p) :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right c W p))
      (quaternionHaar_polySmul blocks c (polyMul W p))
  unfold normalizedMoment
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hnum)
    (Q'.mul_assoc_eqv _ _ _)

theorem normalizedMoment_one {blocks : Nat} {W : RatPoly}
    (hW : (0 : Q') < quaternionHaar blocks W) :
    normalizedMoment blocks W polyOne hW ≈ (1 : Q') := by
  have hnum :
      quaternionHaar blocks (polyMul W polyOne) ≈ quaternionHaar blocks W :=
    haar_of_coeff (RatPolyCoeffEqv.mul_one W)
  unfold normalizedMoment
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hnum)
    (Q'.mul_recipPos_eqv _ hW)

theorem normalizedMoment_mul_symm {blocks : Nat} {W p q : RatPoly}
    (hW : (0 : Q') < quaternionHaar blocks W) :
    normalizedMoment blocks W (polyMul p q) hW ≈
      normalizedMoment blocks W (polyMul q p) hW := by
  exact normalizedMoment_congr hW hW (RatPolyCoeffEqv.refl W)
    (RatPolyCoeffEqv.mul_comm p q)

theorem normalizedMoment_reweight {blocks : Nat} {B V p : RatPoly}
    {hB : (0 : Q') < quaternionHaar blocks B}
    {hBV : (0 : Q') < quaternionHaar blocks (polyMul B V)} :
    normalizedMoment blocks B (polyMul V p) hB * quaternionHaar blocks B *
        Q'.recipPos (quaternionHaar blocks (polyMul B V)) hBV ≈
      normalizedMoment blocks (polyMul B V) p hBV := by
  let N := quaternionHaar blocks (polyMul B (polyMul V p))
  let Z := quaternionHaar blocks B
  let ZV := quaternionHaar blocks (polyMul B V)
  let rZ := Q'.recipPos Z hB
  let rZV := Q'.recipPos ZV hBV
  have hcancel : ((N * rZ) * Z).eqv N := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv N rZ Z)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left N _ _ (Q'.mul_comm_eqv rZ Z))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left N _ _ (Q'.mul_recipPos_eqv Z hB))
          (Q'.mul_one_eqv N)))
  have hassoc : N ≈ quaternionHaar blocks (polyMul (polyMul B V) p) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_assoc B V p).symm
  unfold normalizedMoment
  change ((N * rZ) * Z) * rZV ≈
    quaternionHaar blocks (polyMul (polyMul B V) p) * rZV
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right ((N * rZ) * Z) N rZV hcancel)
    (Q'.mul_eqv_congr_right N _ rZV hassoc)

#print axioms normalizedMoment_add
#print axioms normalizedMoment_smul
#print axioms normalizedMoment_one
#print axioms normalizedMoment_mul_symm
#print axioms normalizedMoment_reweight

end YMGap.Continuum.QuaternionHaarNormalizedMomentLinear
