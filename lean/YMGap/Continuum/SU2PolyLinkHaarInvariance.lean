/-
# Fixed-element and integrated polynomial Haar invariance

The constructed single-link `quaternionPolyLinkHaar` and two-block
`quaternionPolyLinkHaar2` remain unchanged. The former now has fixed rational
unit-element left/right invariance at EVERY degree on supported one-block
polynomials. No invariance field is assumed in `PolyLinkHaar`.

* `polyLinkHaar_left_fixed_invariant` / `_right_fixed_invariant`: the supplied
  rational unit quaternion is FIXED, not Haar-integrated. The imported producer
  separately pins evaluation to the actual Hamilton action `g*x` / `x*g`.
* `polyLinkHaar2_left_shear_invariant` / `_right_shear_invariant` (**PROVED, all
  degrees, general multiplier**): `h(p(a·u, a)) ≈ h(p(u, a))` and
  `h(p(u·a, a)) ≈ h(p(u, a))` for EVERY `p : RatPoly`, where the multiplier `a` is
  the second (Haar-integrated) block.  This is the Fubini form of left/right
  invariance (from `SU2QuaternionAllDegreeHaarTranslation.translatedHeadPolynomial_haar`).
* `polyLinkHaar2_fixedG_invariant_deg2` (**PROVED, SPECIFIC g only**): for each of
  the three rational unit quaternions `(3+4i)/5`, `(3+4j)/5`, `(1+2i+2j+4k)/5` and
  each of the 15 head monomials of degree ≤ 2, `h(m(g·u)) ≈ h(m(u))` and
  `h(m(u·g)) ≈ h(m(u))` (exact evaluation). These finite regressions are retained
  alongside the general fixed-element single-link theorems above.
* `polyLinkHaar2_square_nonneg` (**PROVED, all degrees**): `0 ≤ h(p·p)` for every
  `p` supported on the 8 coordinates (via
  `quaternionHaar_eq_finiteProductHaar` and `finiteProductHaar_square_nonneg`).
  In particular for `p` of degree ≤ 1.

This is polynomial invariance for rational multipliers, not an extension to
all functions or all completed group points, nor a physical spectral gap.

Axioms: `propext`, `Quot.sound`.
-/

import YMGap.Continuum.SU2PolyLinkHaar
import YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslation
import YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
import YMGap.Continuum.SU2QuaternionFiniteProductHaarPolynomialPositivity
import YMGap.Continuum.SU2QuaternionFixedRationalHaarTranslation

namespace YMGap.Continuum.SU2PolyLinkHaarInvariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2PolyLinkHaar (quaternionPolyLinkHaar quaternionPolyLinkHaar2)
open YMGap.Continuum.SU2QuaternionFixedRationalHaarTranslation (fixedTranslatedPolynomial)

/-- Every-degree invariance under the supplied FIXED rational left multiplier. -/
theorem polyLinkHaar_left_fixed_invariant
    (g : YMGap.RepTheory.RationalQuaternion.UnitNorm)
    (p : RatPoly) (hp : SupportedQuaternionBlocks 1 p) :
    (quaternionPolyLinkHaar.h (fixedTranslatedPolynomial false g p)).eqv
      (quaternionPolyLinkHaar.h p) :=
  YMGap.Continuum.SU2QuaternionFixedRationalHaarTranslation.fixedTranslatedPolynomial_haar
    false g p hp

/-- Every-degree invariance under the supplied FIXED rational right multiplier. -/
theorem polyLinkHaar_right_fixed_invariant
    (g : YMGap.RepTheory.RationalQuaternion.UnitNorm)
    (p : RatPoly) (hp : SupportedQuaternionBlocks 1 p) :
    (quaternionPolyLinkHaar.h (fixedTranslatedPolynomial true g p)).eqv
      (quaternionPolyLinkHaar.h p) :=
  YMGap.Continuum.SU2QuaternionFixedRationalHaarTranslation.fixedTranslatedPolynomial_haar
    true g p hp

/-- Left shear invariance (general multiplier block, all degrees). -/
theorem polyLinkHaar2_left_shear_invariant (p : RatPoly) :
    (quaternionPolyLinkHaar2.h (translatedHeadPolynomial leftTranslatedHeadQuaternion p)).eqv
      (quaternionPolyLinkHaar2.h p) :=
  YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslation.translatedHeadPolynomial_haar
    false 1 (by decide) p

/-- Right shear invariance (general multiplier block, all degrees). -/
theorem polyLinkHaar2_right_shear_invariant (p : RatPoly) :
    (quaternionPolyLinkHaar2.h (translatedHeadPolynomial rightTranslatedHeadQuaternion p)).eqv
      (quaternionPolyLinkHaar2.h p) :=
  YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslation.translatedHeadPolynomial_haar
    true 1 (by decide) p

/-- Positivity on squares (all degrees). -/
theorem polyLinkHaar2_square_nonneg (p : RatPoly) (hs : SupportedQuaternionBlocks 2 p) :
    (0 : Q') ≤ quaternionPolyLinkHaar2.h (polyMul p p) :=
  Q'.le_trans' _ _ _
    (YMGap.Continuum.SU2QuaternionFiniteProductHaarPolynomialPositivity.finiteProductHaar_square_nonneg
      2 p hs)
    (Q'.le_of_eqv (Q'.eqv_symm
      (YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal.quaternionHaar_eq_finiteProductHaar
        2 (polyMul p p))))

/-! ## Fixed rational `g`, degree ≤ 2 (specific `g` only) -/

/-- Constant polynomial quaternion. -/
def constQ (a b c d : Q') : PolyQuaternion := ⟨polyConst a, polyConst b, polyConst c, polyConst d⟩

def leftByG (g : PolyQuaternion) : PolyQuaternion := PolyQuaternion.mul g (PolyQuaternion.coordinateVariable 0)
def rightByG (g : PolyQuaternion) : PolyQuaternion := PolyQuaternion.mul (PolyQuaternion.coordinateVariable 0) g

/-- The 15 head monomials of degree ≤ 2. -/
def deg2Basis : List (List Nat) :=
  [[0,0,0,0], [1,0,0,0], [0,1,0,0], [0,0,1,0], [0,0,0,1],
   [2,0,0,0], [0,2,0,0], [0,0,2,0], [0,0,0,2],
   [1,1,0,0], [1,0,1,0], [1,0,0,1], [0,1,1,0], [0,1,0,1], [0,0,1,1]]

def fixedGCheck (g : PolyQuaternion) : Bool :=
  deg2Basis.all fun m =>
    decide ((quaternionHaar 2 (translatedHeadPolynomial (leftByG g) [(m, 1)])).eqv
        (quaternionHaar 2 [(m, 1)])) &&
    decide ((quaternionHaar 2 (translatedHeadPolynomial (rightByG g) [(m, 1)])).eqv
        (quaternionHaar 2 [(m, 1)]))

def g1 : PolyQuaternion := constQ (Q'.mkPos 3 5 (by decide)) (Q'.mkPos 4 5 (by decide)) 0 0
def g2 : PolyQuaternion := constQ (Q'.mkPos 3 5 (by decide)) 0 (Q'.mkPos 4 5 (by decide)) 0
def g3 : PolyQuaternion :=
  constQ (Q'.mkPos 1 5 (by decide)) (Q'.mkPos 2 5 (by decide)) (Q'.mkPos 2 5 (by decide))
    (Q'.mkPos 4 5 (by decide))

set_option maxRecDepth 100000 in
theorem polyLinkHaar2_fixedG_invariant_deg2 :
    fixedGCheck g1 = true ∧ fixedGCheck g2 = true ∧ fixedGCheck g3 = true := by decide

set_option maxRecDepth 100000 in
/-- Sanity: the check is not trivially true (a non-unit `g = 2` fails). -/
theorem fixedGCheck_nonunit_fails : fixedGCheck (constQ 2 0 0 0) = false := by decide

end YMGap.Continuum.SU2PolyLinkHaarInvariance

#print axioms YMGap.Continuum.SU2PolyLinkHaarInvariance.polyLinkHaar2_left_shear_invariant
#print axioms YMGap.Continuum.SU2PolyLinkHaarInvariance.polyLinkHaar2_right_shear_invariant
#print axioms YMGap.Continuum.SU2PolyLinkHaarInvariance.polyLinkHaar2_square_nonneg
#print axioms YMGap.Continuum.SU2PolyLinkHaarInvariance.polyLinkHaar2_fixedG_invariant_deg2
#print axioms YMGap.Continuum.SU2PolyLinkHaarInvariance.fixedGCheck_nonunit_fails
#print axioms YMGap.Continuum.SU2PolyLinkHaarInvariance.polyLinkHaar_left_fixed_invariant
#print axioms YMGap.Continuum.SU2PolyLinkHaarInvariance.polyLinkHaar_right_fixed_invariant
