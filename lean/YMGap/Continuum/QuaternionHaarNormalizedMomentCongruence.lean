/-
# Congruence of normalized original Haar moments

The numerator and its positive Haar denominator may be recoded by coefficient
equivalence independently; this packages the resulting normalized-moment
invariance for finite original carriers.
-/

import YMGap.Continuum.QuaternionHaarDensityVariance
import YMGap.Constructive.CRealLogRatCongruence

namespace YMGap.Continuum.QuaternionHaarNormalizedMomentCongruence

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

/-- Coefficient-equivalent densities and probes have equivalent normalized moments.
The two supplied positivity proofs are used only for the actual Haar masses. -/
theorem normalizedMoment_congr {blocks : Nat} {W V p q : RatPoly}
    (hW : (0 : Q') < quaternionHaar blocks W)
    (hV : (0 : Q') < quaternionHaar blocks V)
    (hWV : RatPolyCoeffEqv W V) (hpq : RatPolyCoeffEqv p q) :
    Q'.eqv (normalizedMoment blocks W p hW)
      (normalizedMoment blocks V q hV) := by
  have hden :
      Q'.eqv (Q'.recipPos (quaternionHaar blocks W) hW)
        (Q'.recipPos (quaternionHaar blocks V) hV) :=
    Q'.recipPos_eqv_congr _ _ hW hV (haar_of_coeff hWV)
  have hnum :
      Q'.eqv (quaternionHaar blocks (polyMul W p))
        (quaternionHaar blocks (polyMul V q)) :=
    haar_of_coeff (hWV.mul hpq)
  unfold normalizedMoment
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hnum)
    (Q'.mul_eqv_congr_left _ _ _ hden)

#print axioms YMGap.Continuum.QuaternionHaarNormalizedMomentCongruence.normalizedMoment_congr

end YMGap.Continuum.QuaternionHaarNormalizedMomentCongruence
