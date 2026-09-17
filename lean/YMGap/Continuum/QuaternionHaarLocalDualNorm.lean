/-
# Sharp norms for finite local reciprocal duals

For the existing finite polynomial reciprocal G_k of a certified positive
window ell<=S<=u, combine
  1-(S*G_k)^2 >= 0,  S*(S-ell)*G_k^2 >= 0.
Their sum is exactly 1-ell*S*G_k^2. Consequently a dual polynomial p*G_k
in the actual weight R*S has squared norm at most H[R*p^2]/ell, for EVERY
finite degree k. No limit, configuration-valued reciprocal, or norm bound
on G_k alone is used.

The consumer is an original four-link star dual. This local estimate does
not supply a bounded-overlap family theorem or a physical spectral gap.
-/

import YMGap.Continuum.QuaternionHaarPositiveWindowInverse
import YMGap.Continuum.QuaternionHaarPositiveFloorCancellation
import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

namespace YMGap.Continuum.QuaternionHaarLocalDualNorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse (residual residualInterval)
open YMGap.Continuum.QuaternionHaarPositiveFloorCancellation (floor_insertion)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv

/-- Exact positivity of the finite local-dual norm defect. The multiplier
bound, not an assumed bound on the inverse polynomial, supplies the first term. -/
def localDualNormCertificate {blocks : Nat} {S : RatPoly} {ell u : Q'}
    (hS : SupportedQuaternionBlocks blocks S) (hell : (0 : Q') < ell)
    (hu : (0 : Q') < u) (hle : ell ≤ u)
    (Spos : Certificate blocks S)
    (L : Certificate blocks (polyAdd S (polyNeg (cap ell))))
    (U : Certificate blocks (polyAdd (cap u) (polyNeg S))) (k : Nat) :
    Certificate blocks (polyAdd polyOne (polyNeg
      (polyMul (cap ell) (polyMul S
        (polyMul (reciprocal S u hu k) (reciprocal S u hu k)))))) := by
  let G := reciprocal S u hu k
  have hG := reciprocal_supported hS u hu k
  have M := multiplierSquareCertificate hS hell hu hle L U k
  have P := (Spos.mul L).mul (Certificate.square G hG)
  apply Certificate.ofCoeff _ (M.add P)
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.const 1) (.neg (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 2))))))
    (.add
      (.add (.const 1) (.neg (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2)))))
      (.mul (.mul (.var 1) (.add (.var 1) (.neg (.var 0)))) (.mul (.var 2) (.var 2))))
    (by decide) (fun | 0 => cap ell | 1 => S | _ => G)

private theorem haar_cap_mul (blocks : Nat) (a : Q') (p : RatPoly) :
    quaternionHaar blocks (polyMul (cap a) p) ≈ a*quaternionHaar blocks p :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right blocks a p polyOne)
      (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_one p))))

/-- Every finite local inverse degree obeys the SAME weighted norm estimate.
The positive remaining action R and the signed probe p are retained literally. -/
theorem local_dual_norm_le {blocks : Nat} {S : RatPoly} {ell u : Q'}
    (hS : SupportedQuaternionBlocks blocks S) (hell : (0 : Q') < ell)
    (hu : (0 : Q') < u) (hle : ell ≤ u)
    (Spos : Certificate blocks S)
    (L : Certificate blocks (polyAdd S (polyNeg (cap ell))))
    (U : Certificate blocks (polyAdd (cap u) (polyNeg S))) (k : Nat)
    {R p : RatPoly} (Rpos : Certificate blocks R)
    (hp : SupportedQuaternionBlocks blocks p) :
    ell * quaternionHaar blocks
      (polyMul (polyMul R (polyMul p p))
        (polyMul S (polyMul (reciprocal S u hu k) (reciprocal S u hu k)))) ≤
      quaternionHaar blocks (polyMul R (polyMul p p)) := by
  let W := polyMul R (polyMul p p)
  let F := polyMul S (polyMul (reciprocal S u hu k) (reciprocal S u hu k))
  let D := polyAdd polyOne (polyNeg (polyMul (cap ell) F))
  have hn := ((Rpos.mul (Certificate.square p hp)).mul
    (localDualNormCertificate hS hell hu hle Spos L U k)).haar_nonnegative
  have hid : RatPolyCoeffEqv
      (polyAdd (polyMul (cap ell) (polyMul W F)) (polyMul W D)) W :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 1) (.add (.const 1) (.neg (.mul (.var 0) (.var 2))))))
      (.var 1) (by decide) (fun | 0 => cap ell | 1 => W | _ => F)
  have he : ell*quaternionHaar blocks (polyMul W F) +
      quaternionHaar blocks (polyMul W D) ≈ quaternionHaar blocks W :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_symm (haar_cap_mul blocks ell (polyMul W F)))
        (Q'.eqv_refl _))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append blocks _ _)) (haar_of_coeff hid))
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hn) (Q'.le_of_eqv he)

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem weighted_haar_cs {blocks : Nat} {R p q : RatPoly}
    (Rpos : Certificate blocks R) (hp : SupportedQuaternionBlocks blocks p)
    (hq : SupportedQuaternionBlocks blocks q) :
    quaternionHaar blocks (polyMul R (polyMul p q)) *
      quaternionHaar blocks (polyMul R (polyMul p q)) ≤
      quaternionHaar blocks (polyMul R (polyMul p p)) *
        quaternionHaar blocks (polyMul R (polyMul q q)) := by
  have pin (a b : RatPoly) : weightedPair blocks R a b ≈
      quaternionHaar blocks (polyMul R (polyMul a b)) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (qmul (pin p q) (pin p q)))
    (Q'.le_trans' _ _ _ (weighted_cauchySchwarz blocks R p q Rpos hp hq)
      (Q'.le_of_eqv (qmul (pin p p) (pin q q))))

/-- The finite local reciprocal error is controlled in the ORIGINAL input
norm R*S. No coefficient cap or independence of shared variables is required. -/
theorem local_dual_pairing_error {blocks : Nat} {S : RatPoly} {ell u : Q'}
    (hS : SupportedQuaternionBlocks blocks S) (hell : (0 : Q') < ell)
    (hu : (0 : Q') < u) (hle : ell ≤ u)
    (L : Certificate blocks (polyAdd S (polyNeg (cap ell))))
    (U : Certificate blocks (polyAdd (cap u) (polyNeg S))) (k : Nat)
    {R p f : RatPoly} (Rpos : Certificate blocks R)
    (hp : SupportedQuaternionBlocks blocks p) (hf : SupportedQuaternionBlocks blocks f) :
    let e := residual (remainder S u hu) k
    let rho := radius ell u hu
    ell * (quaternionHaar blocks (polyMul R (polyMul p (polyMul f e))) *
      quaternionHaar blocks (polyMul R (polyMul p (polyMul f e)))) ≤
      ((rho^k)*(rho^k)*quaternionHaar blocks (polyMul R (polyMul p p))) *
        quaternionHaar blocks (polyMul (polyMul R S) (polyMul f f)) := by
  let e := residual (remainder S u hu) k
  let rho := radius ell u hu
  let A := quaternionHaar blocks (polyMul R (polyMul p p))
  let F := quaternionHaar blocks (polyMul R (polyMul f f))
  let V := quaternionHaar blocks (polyMul R (polyMul (polyMul f e) (polyMul f e)))
  let x := quaternionHaar blocks (polyMul R (polyMul p (polyMul f e)))
  have I := residualInterval (remainderInterval hS hu hle L U) k
  have hcs : x*x ≤ A*V := weighted_haar_cs Rpos hp (supported_polyMul hf I.support)
  have hA : (0 : Q') ≤ A := (Rpos.mul (Certificate.square p hp)).haar_nonnegative
  have hr : (0 : Q') ≤ (rho^k)*(rho^k) :=
    Q'.mul_nonneg _ _ I.nonnegative I.nonnegative
  have hV : V ≤ ((rho^k)*(rho^k))*F := by
    have he : RatPolyCoeffEqv
        (polyMul R (polyMul (polyMul f e) (polyMul f e)))
        (polyMul (polyMul R (polyMul f f)) (polyMul e e)) :=
      coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
        (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2)))
        (by decide) (fun | 0 => R | 1 => f | _ => e)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff he))
      (Q'.le_trans' _ _ _ (Q'.le_abs_self _)
        ((I.mul I).weighted_haar_bound (Rpos.mul (Certificate.square f hf))))
  have hfloor : ell*F ≤ quaternionHaar blocks (polyMul (polyMul R S) (polyMul f f)) :=
    Q'.le_trans' _ _ _ (floor_insertion (Rpos.mul (Certificate.square f hf)) L)
      (Q'.le_of_eqv (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 2))
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 1)))
        (by decide) (fun | 0 => R | 1 => f | _ => S))))
  have h1 : ell*(x*x) ≤ ell*(A*V) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hcs (Q'.le_of_lt hell)
  have h2 : ell*(A*V) ≤ ell*(A*(((rho^k)*(rho^k))*F)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ A hV hA) (Q'.le_of_lt hell)
  have he : ell*(A*(((rho^k)*(rho^k))*F)) ≈
      (((rho^k)*(rho^k))*A)*(ell*F) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
      (.mul (.mul (.var 2) (.var 1)) (.mul (.var 0) (.var 3)))
      (by decide) (fun | 0 => ell | 1 => A | 2 => (rho^k)*(rho^k) | _ => F)
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hfloor (Q'.mul_nonneg _ _ hr hA))))

end YMGap.Continuum.QuaternionHaarLocalDualNorm

#print axioms YMGap.Continuum.QuaternionHaarLocalDualNorm.localDualNormCertificate
#print axioms YMGap.Continuum.QuaternionHaarLocalDualNorm.local_dual_norm_le
#print axioms YMGap.Continuum.QuaternionHaarLocalDualNorm.local_dual_pairing_error
