/-
# Exact normalized cost of an orthogonal polynomial pair

If the mixed Haar moment of two signed polynomials vanishes under the
original weight, their normalized squared-sum cost is exactly the sum of the
two diagonal costs.  Combining this identity with existing Haar interval
second-moment bounds avoids the generic factor two.  The result does not
construct orthogonality or change the supplied weight.
-/

import YMGap.Continuum.QuaternionHaarIntervalSecondMoment

namespace YMGap.Continuum.QuaternionHaarOrthogonalPairCost

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarNormalizedMomentCongruence
open YMGap.Continuum.QuaternionHaarNormalizedMomentLinear
open YMGap.Continuum.QuaternionHaarIntervalSecondMoment
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

local infix:50 " ≈ " => Q'.eqv

/-- Exact Pythagorean identity for two polynomials whose mixed numerator
vanishes under the same original weight. -/
theorem normalized_square_add_of_cross_zero
    {blocks : Nat} {W p q : RatPoly}
    (hZ : (0 : Q') < quaternionHaar blocks W)
    (hcross : quaternionHaar blocks (polyMul (polyMul p q) W) ≈ 0) :
    normalizedMoment blocks W
        (polyMul (polyAdd p q) (polyAdd p q)) hZ ≈
      normalizedMoment blocks W (polyMul p p) hZ +
        normalizedMoment blocks W (polyMul q q) hZ := by
  let pp := polyMul p p
  let pq := polyMul p q
  let qq := polyMul q q
  have hexpand : RatPolyCoeffEqv
      (polyMul (polyAdd p q) (polyAdd p q))
      (polyAdd pp (polyAdd pq (polyAdd pq qq))) := by
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))
      (.add (.mul (.var 0) (.var 0))
        (.add (.mul (.var 0) (.var 1))
          (.add (.mul (.var 0) (.var 1)) (.mul (.var 1) (.var 1)))))
      (by decide) (fun | 0 => p | _ => q)
  have hcrossNumerator :
      quaternionHaar blocks (polyMul W pq) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.mul_comm W pq)) hcross
  have hcrossNormalized : normalizedMoment blocks W pq hZ ≈ 0 := by
    unfold normalizedMoment
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hcrossNumerator)
      (Q'.zero_mul_eqv _)
  have hlinear :
      normalizedMoment blocks W (polyAdd pp (polyAdd pq (polyAdd pq qq))) hZ ≈
        normalizedMoment blocks W pp hZ +
          (normalizedMoment blocks W pq hZ +
            (normalizedMoment blocks W pq hZ +
              normalizedMoment blocks W qq hZ)) := by
    exact Q'.eqv_trans _ _ _ (normalizedMoment_add hZ)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (normalizedMoment_add hZ)
          (Q'.add_eqv_congr' (Q'.eqv_refl _)
            (normalizedMoment_add hZ))))
  have hzeroCross :
      normalizedMoment blocks W pp hZ +
          (normalizedMoment blocks W pq hZ +
            (normalizedMoment blocks W pq hZ +
              normalizedMoment blocks W qq hZ)) ≈
        normalizedMoment blocks W pp hZ +
          ((0 : Q') + (0 + normalizedMoment blocks W qq hZ)) :=
    Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.add_eqv_congr' hcrossNormalized
        (Q'.add_eqv_congr' hcrossNormalized (Q'.eqv_refl _)))
  have hcancel :
      normalizedMoment blocks W pp hZ +
          ((0 : Q') + (0 + normalizedMoment blocks W qq hZ)) ≈
        normalizedMoment blocks W pp hZ + normalizedMoment blocks W qq hZ :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.add (.const 0) (.add (.const 0) (.var 1))))
      (.add (.var 0) (.var 1)) (by decide)
      (fun | 0 => normalizedMoment blocks W pp hZ
           | _ => normalizedMoment blocks W qq hZ)
  exact Q'.eqv_trans _ _ _
    (normalizedMoment_congr hZ hZ (RatPolyCoeffEqv.refl W) hexpand)
    (Q'.eqv_trans _ _ _ hlinear (Q'.eqv_trans _ _ _ hzeroCross hcancel))

/-- Orthogonality removes the factor two from the interval estimate for the
normalized squared sum.  Both diagonal estimates retain the same certified
weight and positive normalizer. -/
theorem normalized_square_add_le
    {blocks : Nat} {W p q : RatPoly} {a b : Q'}
    (P : Interval blocks p a) (Q : Interval blocks q b)
    (H : Certificate blocks W)
    (hZ : (0 : Q') < quaternionHaar blocks W)
    (hcross : quaternionHaar blocks (polyMul (polyMul p q) W) ≈ 0) :
    normalizedMoment blocks W
        (polyMul (polyAdd p q) (polyAdd p q)) hZ ≤
      a * a + b * b := by
  have hp := Interval.normalized_square_le (Interval.squareBound P) H hZ
  have hq := Interval.normalized_square_le (Interval.squareBound Q) H hZ
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (normalized_square_add_of_cross_zero hZ hcross))
    (ExpNeg.add_le_add2 hp hq)

end YMGap.Continuum.QuaternionHaarOrthogonalPairCost

#print axioms YMGap.Continuum.QuaternionHaarOrthogonalPairCost.normalized_square_add_of_cross_zero
#print axioms YMGap.Continuum.QuaternionHaarOrthogonalPairCost.normalized_square_add_le
