/-
# Exact second-moment bounds from original Haar polynomial intervals

An interval `p ∈ [-c,c]` yields the square certificate `p² ≤ c²` on
the same shared-variable Haar carrier.  A positive certificate background
then turns that certificate into a normalized second-moment bound.
-/

import YMGap.Continuum.QuaternionHaarNormalizedMomentLinear
import YMGap.Continuum.QuaternionHaarPolynomialIntervalProduct

namespace YMGap.Continuum.QuaternionHaarIntervalSecondMoment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

local infix:50 " ≈ " => Q'.eqv

private def minus (a b : PolyExpr) : PolyExpr := .add a (.neg b)

/-- Haar linearity for polynomial negation, kept local because the carrier
interface exposes coefficient transport rather than a dedicated negation law. -/
private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | term :: rest => by
      change
        (-term.2) * quaternionHaarMono blocks term.1 +
            quaternionHaar blocks (polyNeg rest) ≈
          -((term.2 * quaternionHaarMono blocks term.1) +
            quaternionHaar blocks rest)
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.neg_mul_eqv term.2 (quaternionHaarMono blocks term.1))
          (haar_neg blocks rest))
        (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

namespace Interval

/-- A two-sided interval gives a square certificate without changing the
shared Haar variables. -/
def squareBound {blocks : Nat} {p : RatPoly} {c : Q'}
    (P : Interval blocks p c) :
    SquareBound blocks p (c*c) where
  support := P.support
  nonnegative := Q'.mul_nonneg _ _ P.nonnegative P.nonnegative
  certificate := Certificate.ofCoeff
    (((cap_mul c c).symm.add (RatPolyCoeffEqv.refl (polyNeg (polyMul p p)))).trans
      (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 2) (.var 2))))
      (.mul (minus (.var 0) (.var 2)) (.add (.var 0) (.var 2)))
      (by decide) (fun | 0 => cap c | _ => p)))
    (P.upper.mul P.lower)

theorem normalized_square_le {blocks : Nat} {p : RatPoly} {c : Q'}
    (P : SquareBound blocks p c) {B : RatPoly}
    (H : Certificate blocks B) (hB : (0 : Q') < quaternionHaar blocks B) :
    normalizedMoment blocks B (polyMul p p) hB ≤ c := by
  have hpos : (0 : Q') ≤ quaternionHaar blocks
      (polyMul B (gap c p)) :=
    (H.mul P.certificate).haar_nonnegative
  have hcap :
      quaternionHaar blocks (polyMul B (cap c)) ≈
        c * quaternionHaar blocks B := by
    exact Q'.eqv_trans _ _ _
      (haar_of_coeff ((RatPolyCoeffEqv.mul_comm B (cap c)).trans
        (cap_mul_left c B)))
      (quaternionHaar_polySmul blocks c B)
  have he : quaternionHaar blocks (polyMul B (gap c p)) ≈
      c * quaternionHaar blocks B +
        -(quaternionHaar blocks (polyMul B (polyMul p p))) := by
    exact Q'.eqv_trans _ _ _
      (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
        (.add (.mul (.var 0) (.var 1))
          (.neg (.mul (.var 0) (.var 2))))
        (by decide) (fun | 0 => B | 1 => cap c | _ => polyMul p p)))
      (Q'.eqv_trans _ _ _
        (quaternionHaar_append blocks _ _)
        (Q'.add_eqv_congr'
          hcap
          (haar_neg blocks (polyMul B (polyMul p p)))))
  have hraw : quaternionHaar blocks (polyMul B (polyMul p p)) ≤
      c * quaternionHaar blocks B :=
    Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hpos (Q'.le_of_eqv he))
  let r := Q'.recipPos (quaternionHaar blocks B) hB
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ r hraw
    (Q'.le_of_lt (Q'.recipPos_pos _ hB))
  unfold normalizedMoment
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv c (quaternionHaar blocks B) r)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left c _ _ (Q'.mul_recipPos_eqv _ hB))
        (Q'.mul_one_eqv c))))

end Interval

theorem normalizedVariance_nonnegative {blocks : Nat} {W p : RatPoly}
    (H : Certificate blocks W) (hW : (0 : Q') < quaternionHaar blocks W)
    (hp : SupportedQuaternionBlocks blocks p) :
    (0 : Q') ≤ normalizedVariance blocks W p hW := by
  let m := normalizedMoment blocks W p hW
  let r := shifted p m
  have hr : SupportedQuaternionBlocks blocks r := shifted_supported hp m
  have hsq : (0 : Q') ≤ quaternionHaar blocks
      (polyMul (polyMul r r) W) :=
    H.square_insertion_nonnegative r hr
  have hnum : (0 : Q') ≤ quaternionHaar blocks
      (polyMul W (polyMul r r)) :=
    Q'.le_trans' _ _ _ hsq (Q'.le_of_eqv
      (haar_of_coeff (RatPolyCoeffEqv.mul_comm (polyMul r r) W)))
  have hcenter : (0 : Q') ≤ normalizedMoment blocks W (polyMul r r) hW := by
    unfold normalizedMoment
    exact Q'.mul_nonneg _ _ hnum
      (Q'.le_of_lt (Q'.recipPos_pos _ hW))
  have hpin := own_mean_pin H hp hW
  exact Q'.le_trans' _ _ _ hcenter (Q'.le_of_eqv hpin)

#print axioms Interval.squareBound
#print axioms Interval.normalized_square_le
#print axioms normalizedVariance_nonnegative

end YMGap.Continuum.QuaternionHaarIntervalSecondMoment
