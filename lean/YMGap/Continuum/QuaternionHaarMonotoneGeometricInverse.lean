/-
# Positive geometric corrections with arbitrary contraction radius below one

Reuse G_k=sum_{j<k}(-R)^j and eps_k=(-R)^k. In addition to the two-sided
interval for R, retain a certificate for -R>=0. Then eps_k>=0 is proved
separately, and 0<=eps_k<=rho^k<=1 implies
  1-((1+R)*G_k)^2 = eps_k*(2-eps_k) >= 0.
This controls the corrected multiplier, not the inverse polynomial itself.
It needs no radius-1/2 restriction. Independence and all original variables
survive. The consumer is the actual erased-message dual-energy comparison;
no conditional reciprocal or uniform physical estimate is assumed here.
-/

import YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse
import YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
import YMGap.Continuum.HeatKernelPos

namespace YMGap.Continuum.QuaternionHaarMonotoneGeometricInverse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse

local infix:50 " ≈ " => Q'.eqv

private theorem support_neg {blocks : Nat} {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem corrector_supported {blocks : Nat} {R : RatPoly}
    (hR : SupportedQuaternionBlocks blocks R) : ∀ k,
    SupportedQuaternionBlocks blocks (corrector R k)
  | 0 => fun _ h => False.elim (List.not_mem_nil h)
  | k+1 => supported_add (supported_one _) (supported_polyMul (support_neg hR) (corrector_supported hR k))

theorem corrector_independent {block : Nat} {R : RatPoly}
    (hR : QuaternionBlockIndependent block R) : ∀ k,
    QuaternionBlockIndependent block (corrector R k)
  | 0 => fun _ h => False.elim (List.not_mem_nil h)
  | k+1 => quaternionBlockIndependent_polyAdd (quaternionBlockIndependent_polyOne _)
      (quaternionBlockIndependent_polyMul (quaternionBlockIndependent_polyNeg hR) (corrector_independent hR k))

/-- Positivity does NOT follow from the interval: it is proved by this
separate induction from the actual certified sign of -R. -/
def residualCertificate {blocks : Nat} {R : RatPoly} (N : Certificate blocks (polyNeg R)) :
    (k : Nat) → Certificate blocks (residual R k)
  | 0 => Certificate.one _
  | k+1 => N.mul (residualCertificate N k)

def oneSubResidualCertificate {blocks : Nat} {R : RatPoly} {rho : Q'}
    (P : Interval blocks R rho) (hrho : rho ≤ (1 : Q')) (k : Nat) :
    Certificate blocks (polyAdd polyOne (polyNeg (residual R k))) := by
  have H := ((residualInterval P k).weaken (HKPos.pow_le_one P.nonnegative hrho k)).upper
  exact .ofCoeff ((RatPolyCoeffEqv.one_smul polyOne).symm.add (.refl _)) H

/-- The original finite multiplier, not a limiting reciprocal. -/
def corrected (R : RatPoly) (k : Nat) : RatPoly :=
  polyMul (polyAdd polyOne R) (corrector R k)

theorem corrected_pin (R : RatPoly) (k : Nat) :
    RatPolyCoeffEqv (corrected R k) (polyAdd polyOne (polyNeg (residual R k))) := by
  have hp : RatPolyCoeffEqv (corrected R k)
      (polyAdd (polyAdd (corrected R k) (residual R k)) (polyNeg (residual R k))) :=
    coeffEvalExpr_eqv_of_normalize_eq (.var 0)
      (.add (.add (.var 0) (.var 1)) (.neg (.var 1))) (by decide)
      (fun | 0 => corrected R k | _ => residual R k)
  exact hp.trans ((cancellation R k).add (.refl _))

/-- A sharp unit square cap for the corrected multiplier. No bound on G_k
by 2, and no small-Haar-perturbation premise, is used. -/
def correctedSquareCertificate {blocks : Nat} {R : RatPoly} {rho : Q'}
    (P : Interval blocks R rho) (N : Certificate blocks (polyNeg R))
    (hrho : rho ≤ (1 : Q')) (k : Nat) :
    Certificate blocks (polyAdd polyOne (polyNeg (polyMul (corrected R k) (corrected R k)))) := by
  let e := residual R k
  have hp : RatPolyCoeffEqv (polyAdd polyOne (polyNeg (polyMul (corrected R k) (corrected R k))))
      (polyMul e (polyAdd polyOne (polyAdd polyOne (polyNeg e)))) :=
    ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg ((corrected_pin R k).mul (corrected_pin R k)))).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.const 1) (.neg (.mul (.add (.const 1) (.neg (.var 0))) (.add (.const 1) (.neg (.var 0))))))
        (.mul (.var 0) (.add (.const 1) (.add (.const 1) (.neg (.var 0))))) (by decide) (fun _ => e))
  exact .ofCoeff hp ((residualCertificate N k).mul ((Certificate.one _).add (oneSubResidualCertificate P hrho k)))

/-- Geometric signed error for any radius; rho<1 is needed only by the
eventual-error modulus, not this finite coefficient/certificate result. -/
def correctedErrorInterval {blocks : Nat} {R : RatPoly} {rho : Q'}
    (P : Interval blocks R rho) (k : Nat) :
    Interval blocks (polyAdd (corrected R k) (polyNeg polyOne)) (rho^k) :=
  .ofCoeff
    (supported_add (supported_polyMul (supported_add (supported_one _) P.support) (corrector_supported P.support k))
      (support_neg (supported_one _)))
    (defect_pin (RatPolyCoeffEqv.refl (polyAdd polyOne R)) k)
    (negInterval (residualInterval P k))

end YMGap.Continuum.QuaternionHaarMonotoneGeometricInverse

#print axioms YMGap.Continuum.QuaternionHaarMonotoneGeometricInverse.corrector_supported
#print axioms YMGap.Continuum.QuaternionHaarMonotoneGeometricInverse.corrector_independent
#print axioms YMGap.Continuum.QuaternionHaarMonotoneGeometricInverse.residualCertificate
#print axioms YMGap.Continuum.QuaternionHaarMonotoneGeometricInverse.oneSubResidualCertificate
#print axioms YMGap.Continuum.QuaternionHaarMonotoneGeometricInverse.corrected_pin
#print axioms YMGap.Continuum.QuaternionHaarMonotoneGeometricInverse.correctedSquareCertificate
#print axioms YMGap.Continuum.QuaternionHaarMonotoneGeometricInverse.correctedErrorInterval
