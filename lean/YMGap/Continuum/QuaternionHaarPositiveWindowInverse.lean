/-
# Finite polynomial reciprocal from an explicit positive Haar window

Given a supported polynomial p and actual certificates ell<=p<=u with
0<ell<=u, put alpha=1/u, rho=1-alpha*ell, R=alpha*p-1, and
G_k=alpha*sum_{j<k}(-R)^j. Every G_k is a finite supported polynomial.
The exact identity p*G_k+(-R)^k=1 and the certified geometric error
have an explicit rational tolerance modulus. A sharp unit square cap
for p*G_k follows from the certified sign of -R.

The consumer is the product of the original odd marginal with one of its
coordinate marginals. Its finite positive window is constructed separately;
no coordinate independence, limiting inverse, approximation budget, or
volume-uniform spectral estimate is assumed or asserted here.
-/

import YMGap.Continuum.QuaternionHaarMonotoneGeometricInverse
import YMGap.Continuum.PositiveContractionResidual

namespace YMGap.Continuum.QuaternionHaarPositiveWindowInverse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse
open YMGap.Continuum.QuaternionHaarMonotoneGeometricInverse

local infix:50 " ≈ " => Q'.eqv

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (a : Q') :
    SupportedQuaternionBlocks blocks (polySmul a p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem cap_neg (a : Q') : RatPolyCoeffEqv (polyNeg (cap a)) (cap (-a)) := by
  intro weight
  change (-(a*1))*weight []+0 ≈ ((-a)*1)*weight []+0
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.neg_mul_eqv a 1))) (Q'.eqv_refl _)

private theorem cap_sub (a b : Q') :
    RatPolyCoeffEqv (cap (a + -b)) (polyAdd (cap a) (polyNeg (cap b))) :=
  (cap_add a (-b)).symm.trans ((RatPolyCoeffEqv.refl _).add (cap_neg b).symm)

private theorem smul_sub (a : Q') (p q : RatPoly) :
    RatPolyCoeffEqv (polySmul a (polyAdd p (polyNeg q)))
      (polyAdd (polySmul a p) (polyNeg (polySmul a q))) :=
  (cap_mul_left a _).symm.trans
    ((coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2)))) (by decide)
      (fun | 0 => cap a | 1 => p | _ => q)).trans
      ((cap_mul_left a p).add (RatPolyCoeffEqv.neg (cap_mul_left a q))))

private def normalized (alpha : Q') (p : RatPoly) : RatPoly :=
  polyAdd (polySmul alpha p) (polyNeg polyOne)

private theorem normalized_support {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (alpha : Q') :
    SupportedQuaternionBlocks blocks (normalized alpha p) :=
  supported_add (support_smul hp alpha) (support_neg (supported_one _))

private def normalizedNegative {blocks : Nat} {p : RatPoly} {alpha u : Q'}
    (ha : (0 : Q') ≤ alpha) (hu : alpha*u ≈ 1)
    (U : Certificate blocks (polyAdd (cap u) (polyNeg p))) :
    Certificate blocks (polyNeg (normalized alpha p)) := by
  have he : RatPolyCoeffEqv (polySmul alpha (polyAdd (cap u) (polyNeg p)))
      (polyAdd polyOne (polyNeg (polySmul alpha p))) :=
    (smul_sub alpha _ _).trans
      (((RatPolyCoeffEqv.smul_assoc alpha u polyOne).trans
        ((RatPolyCoeffEqv.smul_coefficient hu polyOne).trans (RatPolyCoeffEqv.one_smul polyOne))).add (.refl _))
  exact .ofCoeff
    ((coeffEvalExpr_eqv_of_normalize_eq (.neg (.add (.var 0) (.neg (.const 1))))
      (.add (.const 1) (.neg (.var 0))) (by decide) (fun _ => polySmul alpha p)).trans he.symm)
    (U.smul alpha ha)

private def normalizedInterval {blocks : Nat} {p : RatPoly} {alpha ell : Q'}
    (hp : SupportedQuaternionBlocks blocks p) (ha : (0 : Q') ≤ alpha)
    (heta : alpha*ell ≤ (1 : Q'))
    (L : Certificate blocks (polyAdd p (polyNeg (cap ell))))
    (U : Certificate blocks (polyNeg (normalized alpha p))) :
    Interval blocks (normalized alpha p) (1 + -(alpha*ell)) := by
  have h0 := Q'.sub_nonneg_of_le heta
  refine ⟨normalized_support hp alpha, h0, (Certificate.constant blocks _ h0).add U, ?_⟩
  have he : RatPolyCoeffEqv
      (polyAdd (cap (1 + -(alpha*ell))) (normalized alpha p))
      (polySmul alpha (polyAdd p (polyNeg (cap ell)))) :=
    (((cap_sub 1 (alpha*ell)).trans
      ((RatPolyCoeffEqv.one_smul polyOne).add (.refl _))).add (.refl _)).trans
      ((coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.const 1) (.neg (.var 0))) (.add (.var 1) (.neg (.const 1))))
        (.add (.var 1) (.neg (.var 0))) (by decide)
        (fun | 0 => cap (alpha*ell) | _ => polySmul alpha p)).trans
        (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg
          (RatPolyCoeffEqv.smul_assoc alpha ell polyOne).symm)).trans (smul_sub alpha p (cap ell)).symm))
  exact .ofCoeff he (L.smul alpha ha)

def scale (u : Q') (hu : (0 : Q') < u) : Q' := Q'.recipPos u hu

theorem scale_positive (u : Q') (hu : (0 : Q') < u) :
    (0 : Q') < scale u hu := Q'.recipPos_pos _ _

private theorem scale_upper (u : Q') (hu : (0 : Q') < u) : scale u hu * u ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ _)

private theorem scaled_lower_le_one {ell u : Q'} (hu : (0 : Q') < u) (hle : ell ≤ u) :
    scale u hu * ell ≤ (1 : Q') :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hle (Q'.le_of_lt (scale_positive u hu)))
    (Q'.le_of_eqv (scale_upper u hu))

/-- The approximation rate retains the supplied finite window. -/
def radius (ell u : Q') (hu : (0 : Q') < u) : Q' := 1 + -(scale u hu * ell)

theorem radius_nonnegative {ell u : Q'} (hu : (0 : Q') < u) (hle : ell ≤ u) :
    (0 : Q') ≤ radius ell u hu :=
  Q'.sub_nonneg_of_le (scaled_lower_le_one hu hle)

theorem radius_lt_one {ell u : Q'} (hell : (0 : Q') < ell) (hu : (0 : Q') < u) :
    radius ell u hu < (1 : Q') :=
  PositiveContractionResidual.rate_lt_one (Q'.mul_pos (scale_positive u hu) hell)

def remainder (p : RatPoly) (u : Q') (hu : (0 : Q') < u) : RatPoly :=
  normalized (scale u hu) p

theorem remainder_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (u : Q') (hu : (0 : Q') < u) :
    SupportedQuaternionBlocks blocks (remainder p u hu) := normalized_support hp _

def remainderNegative {blocks : Nat} {p : RatPoly} {u : Q'} (hu : (0 : Q') < u)
    (U : Certificate blocks (polyAdd (cap u) (polyNeg p))) :
    Certificate blocks (polyNeg (remainder p u hu)) :=
  normalizedNegative (Q'.le_of_lt (scale_positive u hu)) (scale_upper u hu) U

def remainderInterval {blocks : Nat} {p : RatPoly} {ell u : Q'}
    (hp : SupportedQuaternionBlocks blocks p) (hu : (0 : Q') < u) (hle : ell ≤ u)
    (L : Certificate blocks (polyAdd p (polyNeg (cap ell))))
    (U : Certificate blocks (polyAdd (cap u) (polyNeg p))) :
    Interval blocks (remainder p u hu) (radius ell u hu) :=
  normalizedInterval hp (Q'.le_of_lt (scale_positive u hu)) (scaled_lower_le_one hu hle)
    L (remainderNegative hu U)

/-- Finite polynomial output; no reciprocal function of a configuration is used. -/
def reciprocal (p : RatPoly) (u : Q') (hu : (0 : Q') < u) (k : Nat) : RatPoly :=
  polySmul (scale u hu) (corrector (remainder p u hu) k)

theorem reciprocal_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (u : Q') (hu : (0 : Q') < u) (k : Nat) :
    SupportedQuaternionBlocks blocks (reciprocal p u hu k) :=
  support_smul (corrector_supported (remainder_supported hp u hu) k) _

private theorem multiplier_pin (p : RatPoly) (u : Q') (hu : (0 : Q') < u) (k : Nat) :
    RatPolyCoeffEqv (polyMul p (reciprocal p u hu k)) (corrected (remainder p u hu) k) := by
  let a := scale u hu
  let r := remainder p u hu
  have hp : RatPolyCoeffEqv (polyAdd polyOne r) (polySmul a p) :=
    coeffEvalExpr_eqv_of_normalize_eq (.add (.const 1) (.add (.var 0) (.neg (.const 1))))
      (.var 0) (by decide) (fun _ => polySmul a p)
  exact (RatPolyCoeffEqv.polyMul_smul_right a p (corrector r k)).trans
    ((RatPolyCoeffEqv.polyMul_smul_left a p (corrector r k)).symm.trans
      (hp.symm.mul (.refl _)))

theorem reciprocal_cancellation (p : RatPoly) (u : Q') (hu : (0 : Q') < u) (k : Nat) :
    RatPolyCoeffEqv (polyAdd (polyMul p (reciprocal p u hu k))
      (residual (remainder p u hu) k)) polyOne :=
  ((multiplier_pin p u hu k).add (.refl _)).trans (cancellation _ k)

def multiplierSquareCertificate {blocks : Nat} {p : RatPoly} {ell u : Q'}
    (hp : SupportedQuaternionBlocks blocks p) (hell : (0 : Q') < ell)
    (hu : (0 : Q') < u) (hle : ell ≤ u)
    (L : Certificate blocks (polyAdd p (polyNeg (cap ell))))
    (U : Certificate blocks (polyAdd (cap u) (polyNeg p))) (k : Nat) :
    Certificate blocks (polyAdd polyOne (polyNeg (polyMul
      (polyMul p (reciprocal p u hu k)) (polyMul p (reciprocal p u hu k))))) :=
  .ofCoeff ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg
    ((multiplier_pin p u hu k).mul (multiplier_pin p u hu k))))
    (correctedSquareCertificate (remainderInterval hp hu hle L U)
      (remainderNegative hu U) (Q'.le_of_lt (radius_lt_one hell hu)) k)

def multiplierErrorInterval {blocks : Nat} {p : RatPoly} {ell u : Q'}
    (hp : SupportedQuaternionBlocks blocks p) (hu : (0 : Q') < u) (hle : ell ≤ u)
    (L : Certificate blocks (polyAdd p (polyNeg (cap ell))))
    (U : Certificate blocks (polyAdd (cap u) (polyNeg p))) (k : Nat) :
    Interval blocks (polyAdd (polyMul p (reciprocal p u hu k)) (polyNeg polyOne))
      ((radius ell u hu)^k) :=
  .ofCoeff (supported_add (supported_polyMul hp (reciprocal_supported hp u hu k))
    (support_neg (supported_one _)))
    ((multiplier_pin p u hu k).add (.refl _))
    (correctedErrorInterval (remainderInterval hp hu hle L U) k)

/-- Explicit tolerance modulus; all finite-window dependence is visible. -/
def approximationCutoff (ell u : Q') (hu : (0 : Q') < u) (epsilon : Q') : Nat :=
  PositiveContractionResidual.geometricCutoff (radius ell u hu) 1 epsilon

def approximationInterval {blocks : Nat} {p : RatPoly} {ell u : Q'}
    (hp : SupportedQuaternionBlocks blocks p) (hell : (0 : Q') < ell)
    (hu : (0 : Q') < u) (hle : ell ≤ u)
    (L : Certificate blocks (polyAdd p (polyNeg (cap ell))))
    (U : Certificate blocks (polyAdd (cap u) (polyNeg p)))
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (k : Nat)
    (hk : approximationCutoff ell u hu epsilon ≤ k) :
    Interval blocks (polyAdd (polyMul p (reciprocal p u hu k)) (polyNeg polyOne)) epsilon :=
  (multiplierErrorInterval hp hu hle L U k).weaken
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _))
      (PositiveContractionResidual.geometric_bound (radius_nonnegative hu hle)
        (radius_lt_one hell hu) Q'.zero_le_one hepsilon k hk))

end YMGap.Continuum.QuaternionHaarPositiveWindowInverse

#print axioms YMGap.Continuum.QuaternionHaarPositiveWindowInverse.scale
#print axioms YMGap.Continuum.QuaternionHaarPositiveWindowInverse.scale_positive
#print axioms YMGap.Continuum.QuaternionHaarPositiveWindowInverse.radius
#print axioms YMGap.Continuum.QuaternionHaarPositiveWindowInverse.radius_nonnegative
#print axioms YMGap.Continuum.QuaternionHaarPositiveWindowInverse.radius_lt_one
#print axioms YMGap.Continuum.QuaternionHaarPositiveWindowInverse.remainder
#print axioms YMGap.Continuum.QuaternionHaarPositiveWindowInverse.remainder_supported
#print axioms YMGap.Continuum.QuaternionHaarPositiveWindowInverse.remainderNegative
#print axioms YMGap.Continuum.QuaternionHaarPositiveWindowInverse.remainderInterval
#print axioms YMGap.Continuum.QuaternionHaarPositiveWindowInverse.reciprocal
#print axioms YMGap.Continuum.QuaternionHaarPositiveWindowInverse.reciprocal_supported
#print axioms YMGap.Continuum.QuaternionHaarPositiveWindowInverse.reciprocal_cancellation
#print axioms YMGap.Continuum.QuaternionHaarPositiveWindowInverse.multiplierSquareCertificate
#print axioms YMGap.Continuum.QuaternionHaarPositiveWindowInverse.multiplierErrorInterval
#print axioms YMGap.Continuum.QuaternionHaarPositiveWindowInverse.approximationCutoff
#print axioms YMGap.Continuum.QuaternionHaarPositiveWindowInverse.approximationInterval
