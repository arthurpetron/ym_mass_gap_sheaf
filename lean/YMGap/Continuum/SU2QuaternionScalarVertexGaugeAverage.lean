/-
# Scalar-link product under three vertex-gauge integrations

Three normalized SU(2) integrations give 1/64 of the ordered scalar
holonomy, equivalently 1/128 of its fundamental character. All original
link polynomials remain symbolic; no unit-norm or independence hypothesis
on them is required. Only the three auxiliary gauge blocks are integrated.

This local identity does NOT yet identify the completed bulk-scalar test
with a plaquette pairing. That requires a simultaneous vertex change of
variables for the ORIGINAL full action and observable insertion, followed
by compatibility with the existing limits. No transfer-range assertion is
made here.
-/

import YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing
import YMGap.Continuum.SU2QuaternionHaarGaugeCancellation

namespace YMGap.Continuum.SU2QuaternionScalarVertexGaugeAverage

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHeadLinearHaar
open YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing
open YMGap.Continuum.SU2QuaternionHaarGaugeCancellation
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter

local infix:50 " ≈ " => Q'.eqv
local infixl:70 " ⋄ " => PolyQuaternion.mul
local prefix:80 "bar " => PolyQuaternion.conj
local notation "g" => PolyQuaternion.coordinateVariable 0

/-- One auxiliary gauge precedes the retained link/path coefficients. -/
def scalarPair (p q : PolyQuaternion) : RatPoly :=
  polyMul (liftQuaternion p ⋄ g).scalar (bar g ⋄ liftQuaternion q).scalar

/-- Two auxiliary gauges, eliminated in order; original coefficients follow. -/
def twoGauges (p q r : PolyQuaternion) : RatPoly :=
  polyMul (scalarPair (liftQuaternion p) (liftQuaternion q ⋄ g))
    (liftHead (bar g ⋄ liftQuaternion r).scalar)

/-- Three auxiliary gauges, with every remaining factor retained at each step. -/
def threeGauges (p q r s : PolyQuaternion) : RatPoly :=
  polyMul (scalarPair (liftQuaternion (liftQuaternion p))
    (liftQuaternion (liftQuaternion q) ⋄ g))
    (liftHead (polyMul
      (bar g ⋄ liftQuaternion (liftQuaternion r ⋄ g)).scalar
      (liftHead (bar g ⋄ liftQuaternion s).scalar)))

private theorem schur_with_tail (p q : PolyQuaternion) (tail : RatPoly) :
    RatPolyCoeffEqv (partialHaarHead (polyMul (scalarPair p q) (liftHead tail)))
      (polySmul quarter (polyMul (p ⋄ q).scalar tail)) :=
  (partialHaarHead_mul_lift _ _).trans
    (((scalar_schur p q).mul_right tail).trans
      (RatPolyCoeffEqv.polyMul_smul_left _ _ _))

theorem twoGauges_step (p q r : PolyQuaternion) :
    RatPolyCoeffEqv (partialHaarHead (twoGauges p q r))
      (polySmul quarter (scalarPair (p ⋄ q) r)) := by
  refine (schur_with_tail _ _ _).trans ?_
  apply RatPolyCoeffEqv.smul
  apply RatPolyCoeffEqv.mul_right
  rw [lift_mul]
  exact (PolyQuaternionCoeffEqv.mul_assoc (liftQuaternion p) (liftQuaternion q) g).scalar.symm

theorem threeGauges_step (p q r s : PolyQuaternion) :
    RatPolyCoeffEqv (partialHaarHead (threeGauges p q r s))
      (polySmul quarter (twoGauges (p ⋄ q) r s)) := by
  refine (schur_with_tail _ _ _).trans ?_
  apply RatPolyCoeffEqv.smul
  unfold twoGauges scalarPair
  refine (RatPolyCoeffEqv.mul_assoc _ _ _).symm.trans ?_
  apply RatPolyCoeffEqv.mul_right
  apply RatPolyCoeffEqv.mul_right
  rw [lift_mul, lift_mul]
  exact (PolyQuaternionCoeffEqv.mul_assoc
    (liftQuaternion (liftQuaternion p)) (liftQuaternion (liftQuaternion q)) g).scalar.symm

/-- Integrate precisely the three auxiliary gauge variables, not the links. -/
def averageThree (p : RatPoly) : RatPoly :=
  partialHaarHead (partialHaarHead (partialHaarHead p))

theorem threeGauges_average (p q r s : PolyQuaternion) :
    RatPolyCoeffEqv (averageThree (threeGauges p q r s))
      (polySmul (quarter * (quarter * quarter)) (((p ⋄ q) ⋄ r) ⋄ s).scalar) := by
  have h2 := (partialHaarHead_congr (threeGauges_step p q r s)).trans
    ((partial_smul _ _).trans ((twoGauges_step (p ⋄ q) r s).smul quarter))
  refine (partialHaarHead_congr h2).trans ?_
  refine (partial_smul _ _).trans ?_
  refine ((partial_smul _ _).smul quarter).trans ?_
  refine (((scalar_schur ((p ⋄ q) ⋄ r) s).smul quarter).smul quarter).trans ?_
  exact ((RatPolyCoeffEqv.smul_assoc _ _ _).smul quarter).trans
    (RatPolyCoeffEqv.smul_assoc _ _ _)

/-- Original four oriented links; the base vertex gauge is fixed to one. -/
def orientedScalarProduct (a b c d : PolyQuaternion) : RatPoly :=
  threeGauges a b (bar c) (bar d)

/-- Original link coordinates follow all three auxiliary gauge blocks. -/
def liftThree (q : PolyQuaternion) : PolyQuaternion :=
  liftQuaternion (liftQuaternion (liftQuaternion q))

/-- Literal vertex-gauged product, with the original inverse orientations
encoded by the endpoint order of the third and fourth edges. The first
vertex is fixed to one; the other three gauges occupy blocks 0, 1, 2. -/
def gaugedScalarProduct (a b c d : PolyQuaternion) : RatPoly :=
  polyMul (polyMul (polyMul
    (liftThree a ⋄ g).scalar
    (gaugeLink g (liftThree b) (PolyQuaternion.coordinateVariable 1)).scalar)
    (gaugeLink (PolyQuaternion.coordinateVariable 2) (liftThree c)
      (PolyQuaternion.coordinateVariable 1)).scalar)
    (liftThree d ⋄ PolyQuaternion.coordinateVariable 2).scalar

private theorem lift_scalar (q : PolyQuaternion) :
    liftHead q.scalar = (liftQuaternion q).scalar := rfl

/-- Reassociation and reversal of the two inverse edges, without commuting
quaternion factors or imposing an outer-link unit-norm assumption. -/
theorem orientedScalarProduct_pin (a b c d : PolyQuaternion) :
    RatPolyCoeffEqv (orientedScalarProduct a b c d) (gaugedScalarProduct a b c d) := by
  have hb := (PolyQuaternionCoeffEqv.mul_assoc
    (bar g) (liftThree b) (PolyQuaternion.coordinateVariable 1)).scalar.symm
  have hc := (PolyQuaternionCoeffEqv.mul_assoc
    (bar (PolyQuaternion.coordinateVariable 1)) (bar (liftThree c))
      (PolyQuaternion.coordinateVariable 2)).scalar.symm.trans
        (gaugeLink_conj (PolyQuaternion.coordinateVariable 2) (liftThree c)
          (PolyQuaternion.coordinateVariable 1)).scalar.symm
  have hd := (conjugate_product (liftThree d) (PolyQuaternion.coordinateVariable 2)).scalar.symm
  unfold orientedScalarProduct threeGauges scalarPair
  simp only [liftHead_mul, lift_scalar, lift_mul, lift_conj,
    show liftQuaternion g = PolyQuaternion.coordinateVariable 1 from rfl,
    show liftQuaternion (PolyQuaternion.coordinateVariable 1) =
      PolyQuaternion.coordinateVariable 2 from rfl]
  refine (RatPolyCoeffEqv.mul_assoc _ _ _).symm.trans ?_
  exact (((RatPolyCoeffEqv.refl _).mul hb).mul hc).mul hd

def characterFraction : Q' := Q'.mkPos 1 128 (by decide)

/-- Exact retained-link polynomial, before integrating any original link. -/
theorem orientedScalarProduct_average (a b c d : PolyQuaternion) :
    RatPolyCoeffEqv (averageThree (orientedScalarProduct a b c d))
      (polySmul characterFraction (characterPolynomial (plaquetteWord a b c d).scalar 1)) :=
  (threeGauges_average a b (bar c) (bar d)).trans
    ((RatPolyCoeffEqv.smul_coefficient
      (by decide : quarter * (quarter * quarter) ≈ characterFraction * 2) _).trans
        (RatPolyCoeffEqv.smul_assoc _ _ _).symm)

theorem gaugedScalarProduct_average (a b c d : PolyQuaternion) :
    RatPolyCoeffEqv (averageThree (gaugedScalarProduct a b c d))
      (polySmul characterFraction (characterPolynomial (plaquetteWord a b c d).scalar 1)) :=
  (partialHaarHead_congr (partialHaarHead_congr
    (partialHaarHead_congr (orientedScalarProduct_pin a b c d).symm))).trans
      (orientedScalarProduct_average a b c d)

private theorem averageThree_tail (p tail : RatPoly) :
    RatPolyCoeffEqv (averageThree (polyMul p (liftBoundary 3 tail)))
      (polyMul (averageThree p) tail) := by
  have h1 := partialHaarHead_mul_lift p (liftBoundary 2 tail)
  have h2 := (partialHaarHead_congr h1).trans
    (partialHaarHead_mul_lift (partialHaarHead p) (liftBoundary 1 tail))
  exact (partialHaarHead_congr h2).trans
    (partialHaarHead_mul_lift (partialHaarHead (partialHaarHead p)) tail)

/-- Arbitrary dependence on ALL original links survives the gauge average.
The supplied tail must not contain the three auxiliary gauge variables;
this is not a license to discard a gauge-dependent action factor. -/
theorem gaugedScalarProduct_average_with_tail (a b c d : PolyQuaternion) (tail : RatPoly) :
    RatPolyCoeffEqv
      (averageThree (polyMul (gaugedScalarProduct a b c d) (liftBoundary 3 tail)))
      (polySmul characterFraction
        (polyMul (characterPolynomial (plaquetteWord a b c d).scalar 1) tail)) :=
  (averageThree_tail _ _).trans
    (((gaugedScalarProduct_average a b c d).mul_right tail).trans
      (RatPolyCoeffEqv.polyMul_smul_left _ _ _))

end YMGap.Continuum.SU2QuaternionScalarVertexGaugeAverage

#print axioms YMGap.Continuum.SU2QuaternionScalarVertexGaugeAverage.scalarPair
#print axioms YMGap.Continuum.SU2QuaternionScalarVertexGaugeAverage.twoGauges
#print axioms YMGap.Continuum.SU2QuaternionScalarVertexGaugeAverage.threeGauges
#print axioms YMGap.Continuum.SU2QuaternionScalarVertexGaugeAverage.twoGauges_step
#print axioms YMGap.Continuum.SU2QuaternionScalarVertexGaugeAverage.threeGauges_step
#print axioms YMGap.Continuum.SU2QuaternionScalarVertexGaugeAverage.averageThree
#print axioms YMGap.Continuum.SU2QuaternionScalarVertexGaugeAverage.threeGauges_average
#print axioms YMGap.Continuum.SU2QuaternionScalarVertexGaugeAverage.orientedScalarProduct
#print axioms YMGap.Continuum.SU2QuaternionScalarVertexGaugeAverage.liftThree
#print axioms YMGap.Continuum.SU2QuaternionScalarVertexGaugeAverage.gaugedScalarProduct
#print axioms YMGap.Continuum.SU2QuaternionScalarVertexGaugeAverage.orientedScalarProduct_pin
#print axioms YMGap.Continuum.SU2QuaternionScalarVertexGaugeAverage.characterFraction
#print axioms YMGap.Continuum.SU2QuaternionScalarVertexGaugeAverage.orientedScalarProduct_average
#print axioms YMGap.Continuum.SU2QuaternionScalarVertexGaugeAverage.gaugedScalarProduct_average
#print axioms YMGap.Continuum.SU2QuaternionScalarVertexGaugeAverage.gaugedScalarProduct_average_with_tail
