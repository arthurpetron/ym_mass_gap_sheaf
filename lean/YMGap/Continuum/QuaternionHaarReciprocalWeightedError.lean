/-
# Weighted square-error bound for finite positive-window reciprocals

If a supported multiplier has a certified positive interval, its explicit
polynomial reciprocal has an error interval. Squaring that interval and
inserting the actual positive background and the input square controls the
same weighted Haar norm. No limiting inverse or change of weight is used.
-/

import YMGap.Continuum.QuaternionHaarPositiveWindowInverse
import YMGap.Continuum.QuaternionHaarSignedInterval
import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
import YMGap.Continuum.QuaternionHaarIntervalSecondMoment

namespace YMGap.Continuum.QuaternionHaarReciprocalWeightedError

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSignedInterval
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse

local infix:50 " ≈ " => Q'.eqv

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t :: rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1))
        (haar_neg blocks rest))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem haar_cap_product (blocks : Nat) (c : Q') (p : RatPoly) :
    quaternionHaar blocks (polyMul p (cap c)) ≈ c * quaternionHaar blocks p :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff ((RatPolyCoeffEqv.mul_comm p (cap c)).trans (cap_mul_left c p)))
    (quaternionHaar_polySmul blocks c p)

def reciprocalError (D : RatPoly) (u : Q') (hu : (0 : Q') < u)
    (k : Nat) : RatPoly :=
  polyAdd (polyMul D (reciprocal D u hu k)) (polyNeg polyOne)

def reciprocalWeightedError (r D : RatPoly) (u : Q') (hu : (0 : Q') < u)
    (k : Nat) : RatPoly :=
  polyAdd r (polyNeg (polyMul (polyMul r (reciprocal D u hu k)) D))

/-- The finite reciprocal error in the positive weighted Haar norm, with the
same background and input square on both sides. -/
theorem reciprocal_weighted_error_le {blocks : Nat} {W D r : RatPoly} {ell u : Q'}
    (P : Certificate blocks W)
    (hD : SupportedQuaternionBlocks blocks D)
    (hr : SupportedQuaternionBlocks blocks r)
    (hu : (0 : Q') < u) (hle : ell ≤ u)
    (L : Certificate blocks (polyAdd D (polyNeg (cap ell))))
    (U : Certificate blocks (polyAdd (cap u) (polyNeg D))) (k : Nat) :
    weightedPair blocks W (reciprocalWeightedError r D u hu k)
        (reciprocalWeightedError r D u hu k) ≤
      (radius ell u hu ^ k * radius ell u hu ^ k) * weightedPair blocks W r r := by
  let G := reciprocal D u hu k
  let E := reciprocalError D u hu k
  let c := radius ell u hu ^ k
  let I := multiplierErrorInterval hD hu hle L U k
  let J := QuaternionHaarSignedInterval.Interval.neg I
  let S := QuaternionHaarIntervalSecondMoment.Interval.squareBound J
  let Background := P.mul ((Certificate.square r hr).mul S.certificate)
  let A := polyMul W (polyMul r r)
  have hpos : (0 : Q') ≤ quaternionHaar blocks
      (polyMul A (gap (c*c) (polyNeg E))) := by
    exact Q'.le_trans' _ _ _ Background.haar_nonnegative
      (Q'.le_of_eqv (haar_of_coeff
        (RatPolyCoeffEqv.mul_assoc W (polyMul r r) (gap (c*c) (polyNeg E))).symm))
  have he : quaternionHaar blocks (polyMul A (gap (c*c) (polyNeg E))) ≈
      c*c * quaternionHaar blocks A +
        -(quaternionHaar blocks
          (polyMul A (polyMul (polyNeg E) (polyNeg E)))) := by
    exact Q'.eqv_trans _ _ _
      (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
        (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
        (by decide) (fun | 0 => A | 1 => cap (c*c) | _ => polyMul (polyNeg E) (polyNeg E))))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
        (Q'.add_eqv_congr' (haar_cap_product blocks (c*c) A)
          (haar_neg blocks
            (polyMul A (polyMul (polyNeg E) (polyNeg E))))))
  have hraw : quaternionHaar blocks
      (polyMul A (polyMul (polyNeg E) (polyNeg E))) ≤
      (c*c) * quaternionHaar blocks A :=
    Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hpos (Q'.le_of_eqv he))
  have herror : RatPolyCoeffEqv (reciprocalWeightedError r D u hu k)
      (polyMul r (polyNeg E)) := by
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (.var 0) (.neg (.mul (.mul (.var 0) (.var 1)) (.var 2))))
      (.mul (.var 0) (.neg (.add (.mul (.var 2) (.var 1)) (.neg (.const 1)))))
      (by decide) (fun | 0 => r | 1 => G | _ => D)
  have hsquare : RatPolyCoeffEqv
      (polyMul (polyMul (reciprocalWeightedError r D u hu k)
        (reciprocalWeightedError r D u hu k)) W)
      (polyMul A (polyMul (polyNeg E) (polyNeg E))) := by
    exact (herror.mul herror).mul_right W |>.trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.mul (.var 0) (.neg (.var 1)))
            (.mul (.var 0) (.neg (.var 1)))) (.var 2))
        (.mul (.mul (.var 2) (.mul (.var 0) (.var 0)))
            (.mul (.neg (.var 1)) (.neg (.var 1))))
        (by decide) (fun | 0 => r | 1 => E | _ => W))
  have hbase : quaternionHaar blocks A ≈ weightedPair blocks W r r :=
    haar_of_coeff (RatPolyCoeffEqv.mul_comm (polyMul r r) W).symm
  change quaternionHaar blocks
      (polyMul (polyMul (reciprocalWeightedError r D u hu k)
        (reciprocalWeightedError r D u hu k)) W) ≤ _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff hsquare))
    (Q'.le_trans' _ _ _ hraw
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left (c*c) _ _ hbase)))

end YMGap.Continuum.QuaternionHaarReciprocalWeightedError

#print axioms YMGap.Continuum.QuaternionHaarReciprocalWeightedError.reciprocalError
#print axioms YMGap.Continuum.QuaternionHaarReciprocalWeightedError.reciprocalWeightedError
#print axioms YMGap.Continuum.QuaternionHaarReciprocalWeightedError.reciprocal_weighted_error_le
