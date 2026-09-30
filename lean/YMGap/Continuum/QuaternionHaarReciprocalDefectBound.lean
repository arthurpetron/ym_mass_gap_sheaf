/-
# Positive finite reciprocal defect under an arbitrary certified weight

For a positive-window polynomial normalizer D, the finite geometric
corrector leaves the literal defect 1-DG_k. Its sign comes from the
certified negative geometric remainder, and its upper bound from the
existing residual interval. Multiplying by any certified nonnegative
weight retains all original variables. No pointwise reciprocal or limiting
conditional law is introduced.
-/

import YMGap.Continuum.QuaternionHaarReciprocalCrossComparison
import YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder

namespace YMGap.Continuum.QuaternionHaarReciprocalDefectBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder (haar_order)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse
open YMGap.Continuum.QuaternionHaarMonotoneGeometricInverse
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse

local infix:50 " ≈ " => Q'.eqv

/-- The signed expression is deliberately `1-DG_k`, not `DG_k-1`. -/
def reciprocalDefect (D : RatPoly) (u : Q') (hu : (0 : Q') < u)
    (k : Nat) : RatPoly :=
  polyAdd polyOne (polyNeg (polyMul D (reciprocal D u hu k)))

private theorem residual_defect (D : RatPoly) (u : Q')
    (hu : (0 : Q') < u) (k : Nat) :
    RatPolyCoeffEqv (residual (remainder D u hu) k)
      (reciprocalDefect D u hu k) := by
  let e := residual (remainder D u hu) k
  let G := reciprocal D u hu k
  have hcancel : RatPolyCoeffEqv (polyAdd (polyMul D G) e) polyOne :=
    reciprocal_cancellation D u hu k
  exact (coeffEvalExpr_eqv_of_normalize_eq
    (.var 0) (.add (.add (.var 1) (.var 0)) (.neg (.var 1)))
    (by decide) (fun | 0 => e | _ => polyMul D G)).trans
    (RatPolyCoeffEqv.add hcancel (RatPolyCoeffEqv.refl _))

/-- Constructed nonnegativity of the literal finite defect. -/
def reciprocalDefectCertificate {n : Nat} {D : RatPoly} {u : Q'}
    (hu : (0 : Q') < u)
    (U : Certificate n (polyAdd (cap u) (polyNeg D))) (k : Nat) :
    Certificate n (reciprocalDefect D u hu k) :=
  .ofCoeff (residual_defect D u hu k).symm
    (residualCertificate (remainderNegative hu U) k)

/-- Its geometric cap is certified on the very same polynomial carrier. -/
def reciprocalDefectUpperCertificate {n : Nat} {D : RatPoly} {ell u : Q'}
    (hD : SupportedQuaternionBlocks n D) (hu : (0 : Q') < u)
    (hle : ell ≤ u)
    (L : Certificate n (polyAdd D (polyNeg (cap ell))))
    (U : Certificate n (polyAdd (cap u) (polyNeg D))) (k : Nat) :
    Certificate n
      (polyAdd (cap ((radius ell u hu)^k))
        (polyNeg (reciprocalDefect D u hu k))) :=
  .ofCoeff
    ((RatPolyCoeffEqv.refl _).add
      (RatPolyCoeffEqv.neg (residual_defect D u hu k).symm))
    ((residualInterval (remainderInterval hD hu hle L U) k).upper)

/-- The finite defect is positive and at most the geometric radius under
every certified nonnegative joint insertion. -/
theorem reciprocalDefect_haar_bounds {n : Nat} {D V : RatPoly} {ell u : Q'}
    (hD : SupportedQuaternionBlocks n D) (hu : (0 : Q') < u)
    (hle : ell ≤ u)
    (L : Certificate n (polyAdd D (polyNeg (cap ell))))
    (U : Certificate n (polyAdd (cap u) (polyNeg D)))
    (W : Certificate n V) (k : Nat) :
    (0 : Q') ≤ quaternionHaar n (polyMul (reciprocalDefect D u hu k) V) ∧
    quaternionHaar n (polyMul (reciprocalDefect D u hu k) V) ≤
      (radius ell u hu)^k * quaternionHaar n V := by
  let c := (radius ell u hu)^k
  have hcap : quaternionHaar n (polyMul (cap c) V) ≈
      c * quaternionHaar n V :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (cap_mul_left c V))
      (quaternionHaar_polySmul n c V)
  constructor
  · exact ((reciprocalDefectCertificate hu U k).mul W).haar_nonnegative
  · exact Q'.le_trans' _ _ _
      (haar_order (reciprocalDefectUpperCertificate hD hu hle L U k) W)
      (Q'.le_of_eqv hcap)

/-- An explicit cutoff inherited from the same finite normalizer window. -/
def reciprocalDefectCutoff (ell u : Q') (hu : (0 : Q') < u)
    (epsilon : Q') : Nat := approximationCutoff ell u hu epsilon

/-- Any later iterate has at most epsilon times the original certified
weight mass; the nonnegative defect is retained, not bounded absolutely. -/
theorem reciprocalDefect_haar_error_le {n : Nat} {D V : RatPoly} {ell u : Q'}
    (hD : SupportedQuaternionBlocks n D) (hell : (0 : Q') < ell)
    (hu : (0 : Q') < u) (hle : ell ≤ u)
    (L : Certificate n (polyAdd D (polyNeg (cap ell))))
    (U : Certificate n (polyAdd (cap u) (polyNeg D)))
    (W : Certificate n V) (epsilon : Q') (he : (0 : Q') < epsilon)
    (k : Nat) (hk : reciprocalDefectCutoff ell u hu epsilon ≤ k) :
    quaternionHaar n (polyMul (reciprocalDefect D u hu k) V) ≤
      epsilon * quaternionHaar n V := by
  have hr : (radius ell u hu)^k ≤ epsilon :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _))
      (PositiveContractionResidual.geometric_bound
        (radius_nonnegative hu hle) (radius_lt_one hell hu)
        Q'.zero_le_one he k hk)
  exact Q'.le_trans' _ _ _
    (reciprocalDefect_haar_bounds hD hu hle L U W k).2
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hr W.haar_nonnegative)

#print axioms reciprocalDefect
#print axioms reciprocalDefectCertificate
#print axioms reciprocalDefectUpperCertificate
#print axioms reciprocalDefect_haar_bounds
#print axioms reciprocalDefectCutoff
#print axioms reciprocalDefect_haar_error_le

end YMGap.Continuum.QuaternionHaarReciprocalDefectBound
