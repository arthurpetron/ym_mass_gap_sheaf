/-
# Remove only the first denominator from a certified cross comparison

From a*p*E >= b*q*D and the actual finite reciprocal G_k of D,
construct a*p*G_k*E >= b*(1-rho^k)*q. The second denominator stays
literal. This is the form needed to integrate the second exterior into
the original partition; no reciprocal of E or extra error factor is used.
-/

import YMGap.Continuum.QuaternionHaarReciprocalCrossComparison
import YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder

namespace YMGap.Continuum.QuaternionHaarOneSidedReciprocalComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder (haar_order)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
open YMGap.Continuum.QuaternionHaarReciprocalCrossComparison
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private def subExpr (x y : PolyExpr) : PolyExpr := .add x (.neg y)

-- a,b,p,q,D,E,G,rho,unit occupy positions 0,...,8.
private def leftExpr : PolyExpr :=
  subExpr (.mul (.var 0) (.mul (.mul (.var 2) (.var 6)) (.var 5)))
    (.mul (.var 1) (.mul (subExpr (.var 8) (.var 7)) (.var 3)))

private def rightExpr : PolyExpr :=
  .add
    (.mul (subExpr (.mul (.var 0) (.mul (.var 2) (.var 5)))
      (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.var 6))
    (.mul (.mul (.var 1) (.var 3))
      (.add (.var 7) (subExpr (.mul (.var 4) (.var 6)) (.var 8))))

private theorem one_sided_ring : normalize leftExpr = normalize rightExpr := by decide

/-- A certificate with one finite denominator correction and the other
denominator retained as a polynomial factor. -/
def oneSidedCertificate {n : Nat} (p q D E : RatPoly) (a b ell u : Q')
    (hb : (0 : Q') ≤ b) (hu : (0 : Q') < u) (hle : ell ≤ u)
    (hD : SupportedQuaternionBlocks n D) (Q : Certificate n q)
    (H : Certificate n
      (polyAdd (polyMul (cap a) (polyMul p E))
        (polyNeg (polyMul (cap b) (polyMul q D)))))
    (L : Certificate n (polyAdd D (polyNeg (cap ell))))
    (U : Certificate n (polyAdd (cap u) (polyNeg D))) (k : Nat) :
    Certificate n
      (polyAdd (polyMul (cap a) (polyMul (polyMul p (reciprocal D u hu k)) E))
        (polyNeg (polyMul (cap b)
          (polyMul (polyAdd polyOne (polyNeg (cap ((radius ell u hu)^k)))) q)))) := by
  let G := reciprocal D u hu k
  have C := H.mul (reciprocalCertificate u hu U k)
  have M := (multiplierErrorInterval hD hu hle L U k).lower
  have R := ((Certificate.constant n b hb).mul Q).mul M
  let env : Nat → RatPoly
    | 0 => cap a | 1 => cap b | 2 => p | 3 => q | 4 => D | 5 => E
    | 6 => G | 7 => cap ((radius ell u hu)^k) | _ => polyOne
  exact .ofCoeff
    (coeffEvalExpr_eqv_of_normalize_eq leftExpr rightExpr one_sided_ring env) (C.add R)

private theorem cap_one_sub (r : Q') :
    RatPolyCoeffEqv (polyAdd polyOne (polyNeg (cap r))) (cap (1 + -r)) := by
  have hn : RatPolyCoeffEqv (polyNeg (cap r)) (cap (-r)) := by
    intro weight
    change (-(r*1))*weight []+0 ≈ ((-r)*1)*weight []+0
    exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.neg_mul_eqv r 1))) (Q'.eqv_refl _)
  exact ((RatPolyCoeffEqv.one_smul polyOne).symm.add hn).trans (cap_add 1 (-r))

private theorem corrected_scale (b r : Q') (q : RatPoly) :
    RatPolyCoeffEqv
      (polyMul (cap b) (polyMul (polyAdd polyOne (polyNeg (cap r))) q))
      (polySmul (b * (1 + -r)) q) :=
  (cap_mul_left b _).trans
    ((((cap_one_sub r).mul (.refl q)).trans (cap_mul_left (1 + -r) q)).smul b |>.trans
      (RatPolyCoeffEqv.smul_assoc b (1 + -r) q))

private theorem haar_smul_left (n : Nat) (c : Q') (p r : RatPoly) :
    quaternionHaar n (polyMul (polySmul c p) r) ≈
      c * quaternionHaar n (polyMul p r) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left c p r))
    (quaternionHaar_polySmul n c (polyMul p r))

/-- The single geometric correction holds under every certified positive
joint insertion. All constants and the normalizer window are explicit. -/
theorem weighted_one_sided_comparison {n : Nat} (p q D E : RatPoly) (a b ell u : Q')
    (hb : (0 : Q') ≤ b) (hu : (0 : Q') < u) (hle : ell ≤ u)
    (hD : SupportedQuaternionBlocks n D) (Q : Certificate n q)
    (H : Certificate n
      (polyAdd (polyMul (cap a) (polyMul p E))
        (polyNeg (polyMul (cap b) (polyMul q D)))))
    (L : Certificate n (polyAdd D (polyNeg (cap ell))))
    (U : Certificate n (polyAdd (cap u) (polyNeg D)))
    (k : Nat) {r : RatPoly} (R : Certificate n r) :
    (b * (1 + -((radius ell u hu)^k))) * quaternionHaar n (polyMul q r) ≤
      a * quaternionHaar n (polyMul (polyMul (polyMul p (reciprocal D u hu k)) E) r) := by
  have C := Certificate.ofCoeff
    ((cap_mul_left a _).symm.add (RatPolyCoeffEqv.neg (corrected_scale b _ q).symm))
    (oneSidedCertificate p q D E a b ell u hb hu hle hD Q H L U k)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (haar_smul_left n _ q r))
    (Q'.le_trans' _ _ _ (haar_order C R) (Q'.le_of_eqv (haar_smul_left n a _ r)))

#print axioms oneSidedCertificate
#print axioms weighted_one_sided_comparison

end YMGap.Continuum.QuaternionHaarOneSidedReciprocalComparison
