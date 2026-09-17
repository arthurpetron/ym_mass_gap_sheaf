/-
# Quantitative norm cancellation from a certified positive polynomial floor

If the actual polynomial m has a certificate m-ell>=0 with ell>0,
then ell^2*H[g^2]<=H[(m*g)^2] and
ell*H[m*g^2]<=H[(m*g)^2] for every supported polynomial g.
Positivity of m is constructed from the floor certificate and the positive
constant; it is not an extra analytic premise. Products retain all shared
variables. The bounds are raw Haar inequalities, with no density normalization.

The consumer is the finite approximation error in the original odd marginal.
The displayed ell may depend on all finite regulators; no uniform spectral
bound or inverse-function observable is asserted.
-/

import YMGap.Continuum.QuaternionHaarPolynomialSquareBound

namespace YMGap.Continuum.QuaternionHaarPositiveFloorCancellation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound

local infix:50 " ≈ " => Q'.eqv

/-- Add back the certified nonnegative constant to obtain the actual weight. -/
def certificate_of_floor {blocks : Nat} {m : RatPoly} {ell : Q'}
    (hell : (0 : Q') ≤ ell)
    (L : Certificate blocks (polyAdd m (polyNeg (cap ell)))) :
    Certificate blocks m :=
  .ofCoeff (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
    (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (by decide)
    (fun | 0 => m | _ => cap ell))
    (L.add (.constant blocks ell hell))

/-- The product (m-ell)*(m+ell) is an actual square-floor certificate. -/
def squareFloorCertificate {blocks : Nat} {m : RatPoly} {ell : Q'}
    (hell : (0 : Q') ≤ ell)
    (L : Certificate blocks (polyAdd m (polyNeg (cap ell)))) :
    Certificate blocks (polyAdd (polyMul m m) (polyNeg (cap (ell*ell)))) :=
  .ofCoeff
    (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (cap_mul ell ell).symm)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 1) (.var 1))))
        (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.var 1)))
        (by decide) (fun | 0 => m | _ => cap ell)))
    (L.mul ((certificate_of_floor hell L).add (.constant blocks ell hell)))

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::rest => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1))
        (haar_neg blocks rest))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

/-- Every certified nonnegative insertion preserves the same raw floor.
No independence, normalization, or extra sign condition on ell is needed. -/
theorem floor_insertion {blocks : Nat} {m p : RatPoly} {ell : Q'}
    (P : Certificate blocks p)
    (L : Certificate blocks (polyAdd m (polyNeg (cap ell)))) :
    ell * quaternionHaar blocks p ≤ quaternionHaar blocks (polyMul p m) := by
  have hpos := (P.mul L).haar_nonnegative
  have hc : quaternionHaar blocks (polyMul p (cap ell)) ≈ ell * quaternionHaar blocks p :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff ((RatPolyCoeffEqv.mul_comm _ _).trans (cap_mul_left ell p)))
      (quaternionHaar_polySmul blocks ell p)
  have he : quaternionHaar blocks (polyMul p (polyAdd m (polyNeg (cap ell)))) ≈
      quaternionHaar blocks (polyMul p m) + -(ell * quaternionHaar blocks p) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
      (by decide) (fun | 0 => p | 1 => m | _ => cap ell)))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.eqv_trans _ _ _ (haar_neg blocks _) (Q'.neg_eqv_congr _ _ hc))))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hpos (Q'.le_of_eqv he))

/-- Cancel a certified positive multiplier at the price of its explicit
squared floor. The polynomial g remains arbitrary and signed. -/
theorem square_norm_floor {blocks : Nat} {m g : RatPoly} {ell : Q'}
    (hg : SupportedQuaternionBlocks blocks g) (hell : (0 : Q') < ell)
    (L : Certificate blocks (polyAdd m (polyNeg (cap ell)))) :
    (ell*ell) * quaternionHaar blocks (polyMul g g) ≤
      quaternionHaar blocks (polyMul (polyMul m g) (polyMul m g)) :=
  Q'.le_trans' _ _ _
    (floor_insertion (Certificate.square g hg) (squareFloorCertificate (Q'.le_of_lt hell) L))
    (Q'.le_of_eqv (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 1) (.var 1)) (.mul (.var 0) (.var 0)))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => m | _ => g))))

/-- For an actual density m, only one power of its floor is lost when the
left norm retains the SAME density. No partition factor is removed. -/
theorem weighted_norm_floor {blocks : Nat} {m g : RatPoly} {ell : Q'}
    (hg : SupportedQuaternionBlocks blocks g) (hell : (0 : Q') < ell)
    (L : Certificate blocks (polyAdd m (polyNeg (cap ell)))) :
    ell * quaternionHaar blocks (polyMul m (polyMul g g)) ≤
      quaternionHaar blocks (polyMul (polyMul m g) (polyMul m g)) :=
  Q'.le_trans' _ _ _
    (floor_insertion ((certificate_of_floor (Q'.le_of_lt hell) L).mul (Certificate.square g hg)) L)
    (Q'.le_of_eqv (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 0))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => m | _ => g))))

/-- Certificate-level cancellation, so finite signed sums can use the existing
SquareBound.add rather than first passing to scalar Cauchy--Schwarz. -/
def cancelSquareBound {blocks : Nat} {m g : RatPoly} {ell C : Q'}
    (hg : SupportedQuaternionBlocks blocks g) (hell : (0 : Q') < ell)
    (L : Certificate blocks (polyAdd m (polyNeg (cap ell))))
    (B : SquareBound blocks (polyMul m g) C) :
    SquareBound blocks g (Q'.recipPos (ell*ell) (Q'.mul_pos hell hell) * C) := by
  let a := Q'.recipPos (ell*ell) (Q'.mul_pos hell hell)
  have ha : (0 : Q') ≤ a := Q'.le_of_lt (Q'.recipPos_pos _ _)
  refine ⟨hg, Q'.mul_nonneg _ _ ha B.nonnegative, ?_⟩
  let D : Certificate blocks
      (polyAdd (cap C) (polyNeg (polyMul (cap (ell*ell)) (polyMul g g)))) :=
    .ofCoeff (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.var 0) (.neg (.mul (.var 3) (.mul (.var 2) (.var 2)))))
      (.add
        (.add (.var 0) (.neg (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2)))))
        (.mul (.add (.mul (.var 1) (.var 1)) (.neg (.var 3))) (.mul (.var 2) (.var 2))))
      (by decide) (fun | 0 => cap C | 1 => m | 2 => g | _ => cap (ell*ell)))
      (B.certificate.add ((squareFloorCertificate (Q'.le_of_lt hell) L).mul
        (Certificate.square g hg)))
  have hi : a*(ell*ell) ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ _)
  have hc : RatPolyCoeffEqv (polyMul (cap a) (cap (ell*ell))) polyOne :=
    (cap_mul a (ell*ell)).trans
      ((RatPolyCoeffEqv.smul_coefficient hi polyOne).trans (RatPolyCoeffEqv.one_smul polyOne))
  have he : RatPolyCoeffEqv
      (polySmul a (polyAdd (cap C) (polyNeg (polyMul (cap (ell*ell)) (polyMul g g)))))
      (gap (a*C) g) :=
    (cap_mul_left a _).symm.trans
      ((coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.add (.var 1) (.neg (.mul (.var 2) (.var 3)))))
        (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.mul (.var 0) (.var 2)) (.var 3))))
        (by decide) (fun | 0 => cap a | 1 => cap C | 2 => cap (ell*ell) | _ => polyMul g g)).trans
        ((cap_mul a C).add (RatPolyCoeffEqv.neg
          ((hc.mul_right (polyMul g g)).trans (RatPolyCoeffEqv.one_mul (polyMul g g))))))
  exact .ofCoeff he.symm (D.smul a ha)

end YMGap.Continuum.QuaternionHaarPositiveFloorCancellation

#print axioms YMGap.Continuum.QuaternionHaarPositiveFloorCancellation.certificate_of_floor
#print axioms YMGap.Continuum.QuaternionHaarPositiveFloorCancellation.squareFloorCertificate
#print axioms YMGap.Continuum.QuaternionHaarPositiveFloorCancellation.floor_insertion
#print axioms YMGap.Continuum.QuaternionHaarPositiveFloorCancellation.square_norm_floor
#print axioms YMGap.Continuum.QuaternionHaarPositiveFloorCancellation.weighted_norm_floor
#print axioms YMGap.Continuum.QuaternionHaarPositiveFloorCancellation.cancelSquareBound
