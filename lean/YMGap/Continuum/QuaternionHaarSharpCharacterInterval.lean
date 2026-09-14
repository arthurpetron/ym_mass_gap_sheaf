/-
# Sharp linear SU(2) character bounds from polynomial squares

The conserved Chebyshev energy supplies a unit square bound for each
cosine polynomial. U_(n+2) = U_n + 2*T_(n+2) then constructs both signs
of the sharp interval -(n+1) <= U_n <= n+1. These are certificates on
the original shared-variable Haar carrier, not pointwise assumptions.
-/

import YMGap.Continuum.QuaternionHaarChebyshevEnergy
import YMGap.Continuum.QuaternionHaarPolynomialIntervalProduct

namespace YMGap.Continuum.QuaternionHaarSharpCharacterInterval

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarChebyshevEnergy

private def unitUpper {blocks : Nat} {p : RatPoly} (P : SquareBound blocks p 1) :
    Certificate blocks (polyAdd (cap 1) (polyNeg p)) :=
  .ofCoeff ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.mul_one p).symm))
    (P.cross (.one blocks))

/-- The unit square bound gives the unit interval, without the old factor two. -/
def unitSquareInterval {blocks : Nat} {p : RatPoly} (P : SquareBound blocks p 1) :
    Interval blocks p 1 where
  support := P.support
  nonnegative := Q'.zero_le_one
  upper := unitUpper P
  lower := .ofCoeff ((RatPolyCoeffEqv.refl _).add
    (coeffEvalExpr_eqv_of_normalize_eq (.var 0) (.neg (.neg (.var 0))) (by decide) (fun _ => p)))
    (unitUpper P.neg)

private theorem cap_step (n : Nat) : Q'.eqv (dimQ n + 2*1) (dimQ (n+2)) :=
  Q'.eqv_symm (Q'.ofNat_add_eqv (n+1) 2)

/-- Explicit certificates at the exact representation dimension, for every spin. -/
def sharpCharacterInterval {blocks : Nat} {p : RatPoly} (P : SquareBound blocks p 1) :
    ∀ n : Nat, Interval blocks (characterPolynomial p n) (dimQ n)
  | 0 => .one blocks
  | 1 => Interval.changeCap (by decide) ((unitSquareInterval P).smul 2 (by decide))
  | n+2 => Interval.ofCoeff (character_squareBound P (n+2)).support (character_cosine_step p n)
      (Interval.changeCap (cap_step n)
        ((sharpCharacterInterval P n).add ((unitSquareInterval (cosine_squareBound P n)).smul 2 (by decide))))

theorem character_haar_bound {blocks : Nat} {p : RatPoly} (P : SquareBound blocks p 1) (n : Nat) :
    Q'.abs (quaternionHaar blocks (characterPolynomial p n)) ≤ dimQ n :=
  (sharpCharacterInterval P n).haar_bound

/-- The same sharp factor remains valid against any original positive-certificate background. -/
theorem character_weighted_haar_bound {blocks : Nat} {p r : RatPoly}
    (P : SquareBound blocks p 1) (R : Certificate blocks r) (n : Nat) :
    Q'.abs (quaternionHaar blocks (polyMul r (characterPolynomial p n))) ≤ dimQ n * quaternionHaar blocks r :=
  (sharpCharacterInterval P n).weighted_haar_bound R

end YMGap.Continuum.QuaternionHaarSharpCharacterInterval

#print axioms YMGap.Continuum.QuaternionHaarSharpCharacterInterval.unitSquareInterval
#print axioms YMGap.Continuum.QuaternionHaarSharpCharacterInterval.sharpCharacterInterval
#print axioms YMGap.Continuum.QuaternionHaarSharpCharacterInterval.character_haar_bound
#print axioms YMGap.Continuum.QuaternionHaarSharpCharacterInterval.character_weighted_haar_bound
