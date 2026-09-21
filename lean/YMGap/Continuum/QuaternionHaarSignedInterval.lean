/-
# Signed scalar transport for shared-variable polynomial intervals

The interval cap is an absolute-value cap, so a negative scalar is handled
by reflecting the interval rather than discarding its sign.  This is purely
finite coefficient algebra on the existing Haar carrier.
-/

import YMGap.Continuum.QuaternionHaarPolynomialInterval

namespace YMGap.Continuum.QuaternionHaarSignedInterval

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (a : Q') :
    SupportedQuaternionBlocks blocks (polySmul a p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private def negativeInterval {blocks : Nat} {p : RatPoly} {c : Q'}
    (P : Interval blocks p c) : Interval blocks (polyNeg p) c where
  support := support_neg P.support
  nonnegative := P.nonnegative
  upper := .ofCoeff ((RatPolyCoeffEqv.refl _).add
    (coeffEvalExpr_eqv_of_normalize_eq (.neg (.neg (.var 0))) (.var 0) (by decide) (fun _ => p))) P.lower
  lower := P.upper

private theorem negative_smul (a : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polySmul (-a) p) (polyNeg (polySmul a p)) := by
  have hminus : RatPolyCoeffEqv (polySmul (-1) (polySmul a p))
      (polyNeg (polySmul a p)) :=
    (cap_mul_left (-1) (polySmul a p)).symm.trans
      (coeffEvalExpr_eqv_of_normalize_eq (.mul (.const (-1)) (.var 0))
        (.neg (.var 0)) (by decide) (fun _ => polySmul a p))
  exact ((RatPolyCoeffEqv.smul_coefficient
      (Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 a)
        (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv a)))) p).trans
    (RatPolyCoeffEqv.smul_assoc (-1) a p).symm).trans hminus

namespace Interval

def neg {blocks : Nat} {p : RatPoly} {c : Q'}
    (P : Interval blocks p c) : Interval blocks (polyNeg p) c :=
  negativeInterval P

def smul_abs {blocks : Nat} {p : RatPoly} {c : Q'} (a : Q')
    (P : Interval blocks p c) :
    Interval blocks (polySmul a p) (Q'.abs a * c) := by
  by_cases ha : (0 : Q') ≤ a
  · have hcap : Q'.eqv (a * c) (Q'.abs a * c) :=
      Q'.mul_eqv_congr_right a (Q'.abs a) c
        (Q'.eqv_of_eq (ExpNeg.abs_of_nonneg ha).symm)
    exact (Interval.smul a ha P).changeCap hcap
  · have hna : (0 : Q') ≤ -a := Q'.neg_nonneg_of_not_nonneg ha
    have hcap : Q'.eqv ((-a) * c) (Q'.abs a * c) :=
      Q'.mul_eqv_congr_right (-a) (Q'.abs a) c (by
        unfold Q'.abs
        rw [if_neg ha]
        exact Q'.eqv_refl (-a))
    have hpoly : RatPolyCoeffEqv (polyNeg (polySmul (-a) p))
        (polySmul a p) :=
      (negative_smul (-a) p).symm.trans
        (RatPolyCoeffEqv.smul_coefficient (Q'.neg_neg_eqv a) p)
    exact (Interval.ofCoeff (support_smul P.support a) hpoly.symm
      (neg (Interval.smul (-a) hna P))).changeCap hcap

end Interval
end YMGap.Continuum.QuaternionHaarSignedInterval

#print axioms YMGap.Continuum.QuaternionHaarSignedInterval.Interval.neg
#print axioms YMGap.Continuum.QuaternionHaarSignedInterval.Interval.smul_abs
