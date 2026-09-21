/-
# Original quaternion displacement from the fundamental relative character

The squared four-coordinate chordal distance is 2-chi_1(q*conj(p))
on the original Haar-unit carrier. Both orientations have the same cost.
This exact identity connects kinetic alignment to ordered-word increments;
it is not a spatial variance or spectral estimate.
-/

import YMGap.Continuum.QuaternionHaarWordDifference
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound

namespace YMGap.Continuum.QuaternionHaarChordalDifference

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarWordDifference (difference)

private def env (p q : PolyQuaternion) : Nat → RatPoly
  | 0 => p.scalar | 1 => p.iPart | 2 => p.jPart | 3 => p.kPart
  | 4 => q.scalar | 5 => q.iPart | 6 => q.jPart | _ => q.kPart

private def delta : PolyQuaternionExpr :=
  ⟨.add (.var 0) (.neg (.var 4)), .add (.var 1) (.neg (.var 5)),
    .add (.var 2) (.neg (.var 6)), .add (.var 3) (.neg (.var 7))⟩

/-- Equality under arbitrary insertions; unit radii are not substituted
pointwise into an unrelated measure. -/
theorem norm_difference_character {n : Nat} {p q : PolyQuaternion}
    (hp : HaarCarrierEqv n (polyQuaternionNorm p) polyOne)
    (hq : HaarCarrierEqv n (polyQuaternionNorm q) polyOne) :
    HaarCarrierEqv n (polyQuaternionNorm (difference p q))
      (polyAdd (cap 2) (polyNeg (characterPolynomial
        (PolyQuaternion.mul q (PolyQuaternion.conj p)).scalar 1))) := by
  have he : RatPolyCoeffEqv (polyQuaternionNorm (difference p q))
      (polyAdd (polyAdd (polyQuaternionNorm p) (polyQuaternionNorm q))
        (polyNeg (characterPolynomial (PolyQuaternion.mul q (PolyQuaternion.conj p)).scalar 1))) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (PolyQuaternionExpr.norm delta)
      (.add (.add (PolyQuaternionExpr.norm (.coordinate 0)) (PolyQuaternionExpr.norm (.coordinate 4)))
        (.neg (.mul (.const 2)
          (PolyQuaternionExpr.mul (.coordinate 4) (PolyQuaternionExpr.conj (.coordinate 0))).scalar)))
      (by decide) (env p q)).trans
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (cap_mul_left 2 _)))
  have ht : RatPolyCoeffEqv (polyAdd polyOne polyOne) (cap 2) :=
    coeffEvalExpr_eqv_of_normalize_eq (.add (.const 1) (.const 1)) (.const 2) (by decide)
      (fun _ => polyZero)
  exact HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier he)
    (HaarCarrierEqv.trans (HaarCarrierEqv.add (HaarCarrierEqv.add hp hq) (HaarCarrierEqv.refl n _))
      (RatPolyCoeffEqv.haarCarrier (ht.add (RatPolyCoeffEqv.refl _))))

/-- Reversing both link orientations preserves the literal four-square distance. -/
theorem norm_difference_conj (p q : PolyQuaternion) :
    RatPolyCoeffEqv (polyQuaternionNorm (difference (PolyQuaternion.conj p) (PolyQuaternion.conj q)))
      (polyQuaternionNorm (difference p q)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (PolyQuaternionExpr.norm
      ⟨.add (.var 0) (.neg (.var 4)), .add (.neg (.var 1)) (.neg (.neg (.var 5))),
        .add (.neg (.var 2)) (.neg (.neg (.var 6))), .add (.neg (.var 3)) (.neg (.neg (.var 7)))⟩)
    (PolyQuaternionExpr.norm delta) (by decide) (env p q)

end YMGap.Continuum.QuaternionHaarChordalDifference

#print axioms YMGap.Continuum.QuaternionHaarChordalDifference.norm_difference_character
#print axioms YMGap.Continuum.QuaternionHaarChordalDifference.norm_difference_conj
