/-
# Angular differentiation respects the original Haar carrier

Integration by parts moves the derivative onto an arbitrary insertion.
Consequently equality under every original Haar insertion is preserved by
the tangential derivative. This permits padded coordinate/word identities
to transport actual derivative certificates, without identifying padded
monomials by false raw coefficient equalities.
-/

import YMGap.Continuum.SU2QuaternionAngularSupport
import YMGap.Continuum.SU2QuaternionHaarCertificateReindex
import YMGap.Continuum.QuaternionHaarPolynomialIntervalProduct

namespace YMGap.Continuum.QuaternionHaarAngularCarrier

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionHaarAngularIBP
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval

local infix:50 " ≈ " => Q'.eqv

private theorem neg_of_sum_zero (a b : Q') (h : a+b ≈ 0) : b ≈ -a := by
  apply QPoly.q_eqv_of_sub_zero
  exact Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.add (.var 0) (.neg (.neg (.var 1))))
      (.add (.var 1) (.var 0)) (by decide) (fun n => if n = 0 then b else a)) h

theorem angular_pair (tail : Nat) {i j : Nat} (hi : i < 4) (hj : j < 4)
    (r p : RatPoly) :
    quaternionHaar (tail+1) (polyMul r (angularDerivative i j p)) ≈
      -(quaternionHaar (tail+1) (polyMul (angularDerivative i j r) p)) :=
  neg_of_sum_zero _ _ (Q'.eqv_trans _ _ _
    (Q'.eqv_symm (quaternionHaar_append (tail+1) _ _))
    (quaternionHaar_weighted_angular tail hi hj r p))

/-- A genuine tangential derivation of the SAME Haar carrier, with no
support or analytic positivity assumptions on intermediate representatives. -/
theorem angularDerivative_carrier {blocks i j : Nat} {p q : RatPoly}
    (hb : 0 < blocks) (hi : i < 4) (hj : j < 4) (h : HaarCarrierEqv blocks p q) :
    HaarCarrierEqv blocks (angularDerivative i j p) (angularDerivative i j q) := by
  cases blocks with
  | zero => exact False.elim (Nat.not_lt_zero 0 hb)
  | succ tail =>
      intro r
      exact Q'.eqv_trans _ _ _ (angular_pair tail hi hj r p)
        (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (h (angularDerivative i j r)))
          (Q'.eqv_symm (angular_pair tail hi hj r q)))

/-- Finite coordinate-prefix equality becomes arbitrary-insertion equality
only after BOTH original support guards have been checked. -/
theorem carrierOfPrefix {blocks : Nat} {p q : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q)
    (h : QuaternionPrefixPolynomialEqv blocks p q) : HaarCarrierEqv blocks p q := by
  apply carrier_of_supported hp hq
  intro r hr
  exact quaternionHaar_prefixPolynomialEqv blocks
    ((QuaternionPrefixPolynomialEqv.refl blocks r).mul h)
    (supported_polyMul hr hp) (supported_polyMul hr hq)

/-- Transport the two certificate endpoints through genuine Haar equality. -/
def intervalOfCarrier {blocks : Nat} {p q : RatPoly} {c : Q'}
    (hp : SupportedQuaternionBlocks blocks p) (h : HaarCarrierEqv blocks p q)
    (Q : Interval blocks q c) : Interval blocks p c where
  support := hp
  nonnegative := Q.nonnegative
  upper := .transport (HaarCarrierEqv.add (HaarCarrierEqv.refl blocks _) (HaarCarrierEqv.neg h)) Q.upper
  lower := .transport (HaarCarrierEqv.add (HaarCarrierEqv.refl blocks _) h) Q.lower

theorem neg_smul (p : RatPoly) : RatPolyCoeffEqv (polyNeg p) (polySmul (-1) p) :=
  (coeffEvalExpr_eqv_of_normalize_eq (.neg (.var 0)) (.mul (.const (-1)) (.var 0))
    (by decide) (fun _ => p)).trans (cap_mul_left (-1) p)

theorem angularDerivative_neg (i j : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (angularDerivative i j (polyNeg p)) (polyNeg (angularDerivative i j p)) :=
  (angularDerivative_congr i j (neg_smul p)).trans
    ((angularDerivative_smul i j (-1) p).trans (neg_smul _).symm)

/-- Negation exchanges the two actual endpoint certificates. -/
def intervalNeg {blocks : Nat} {p : RatPoly} {c : Q'} (P : Interval blocks p c) :
    Interval blocks (polyNeg p) c where
  support := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact P.support s hs
  nonnegative := P.nonnegative
  upper := .ofCoeff ((RatPolyCoeffEqv.refl _).add
    (coeffEvalExpr_eqv_of_normalize_eq (.neg (.neg (.var 0))) (.var 0) (by decide) (fun _ => p))) P.lower
  lower := P.upper

end YMGap.Continuum.QuaternionHaarAngularCarrier

#print axioms YMGap.Continuum.QuaternionHaarAngularCarrier.angular_pair
#print axioms YMGap.Continuum.QuaternionHaarAngularCarrier.angularDerivative_carrier
#print axioms YMGap.Continuum.QuaternionHaarAngularCarrier.carrierOfPrefix
#print axioms YMGap.Continuum.QuaternionHaarAngularCarrier.intervalOfCarrier
#print axioms YMGap.Continuum.QuaternionHaarAngularCarrier.neg_smul
#print axioms YMGap.Continuum.QuaternionHaarAngularCarrier.angularDerivative_neg
#print axioms YMGap.Continuum.QuaternionHaarAngularCarrier.intervalNeg
