/-
# One relative kinetic factor: an explicit angular derivative certificate

The original relative scalar and every spin of the original heat prefix are
retained. The conservative scalar derivative cap is 32, independent of the
two block indices and ambient carrier size. The heat cap depends explicitly
on the nome, but not the cutoff. This is a one-factor certificate, not an
interacting spectral gap or a nome-uniform continuum estimate.
-/

import YMGap.Continuum.QuaternionHaarHeatAngularDerivative
import YMGap.Continuum.QuaternionHaarAngularProductBounds
import YMGap.Continuum.SU2QuaternionWeightedProductLocalGap

namespace YMGap.Continuum.SU2QuaternionRelativeHeatAngularBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
open YMGap.Continuum.QuaternionHaarCoordinateAngularInterval
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarAngularProductBounds
open YMGap.Continuum.QuaternionHaarHeatAngularDerivative

private def derivativeCoordinateInterval {blocks coordinate : Nat}
    (i : Nat) (hc : coordinate < 4 * blocks) :
    Interval blocks (ratDerivative i (polyVar coordinate)) 2 := by
  refine (polynomialInterval blocks _
    (ratDerivative_supported (coordinateInterval hc).support)).weaken ?_
  change ((Q'.ofNat (exponentAt (varMono coordinate) i) * 1) *
    (Q'.ofNat (exponentAt (varMono coordinate) i) * 1) + 1) + 0 ≤ (2 : Q')
  rw [exponentAt_varMono]
  by_cases h : i = coordinate
  · rw [if_pos h]; decide
  · rw [if_neg h]; decide

private def coordinateBound {blocks i j coordinate : Nat}
    (hi : i < 4 * blocks) (hj : j < 4 * blocks)
    (hc : coordinate < 4 * blocks) :
    AngularBound blocks i j (polyVar coordinate) 1 4 where
  value := coordinateInterval hc
  derivative := by
    have L := (coordinateInterval hi).mul (derivativeCoordinateInterval j hc)
    have R := (coordinateInterval hj).mul (derivativeCoordinateInterval i hc)
    exact (L.add (Interval.ofCoeff (polySmul_supported R.support (-1))
      (neg_smul _).symm (intervalNeg R))).changeCap (by decide)

private def addBound {blocks i j : Nat} {p q : RatPoly} {a b c d : Q'}
    (hi : i < 4 * blocks) (hj : j < 4 * blocks)
    (P : AngularBound blocks i j p a b) (Q : AngularBound blocks i j q c d) :
    AngularBound blocks i j (polyAdd p q) (a+c) (b+d) :=
  ⟨P.value.add Q.value, Interval.ofCoeff
    (angularDerivative_supported_at hi hj (P.value.add Q.value).support)
    (angularDerivative_add i j p q) (P.derivative.add Q.derivative)⟩

private def negBound {blocks i j : Nat} {p : RatPoly} {a b : Q'}
    (hi : i < 4 * blocks) (hj : j < 4 * blocks)
    (P : AngularBound blocks i j p a b) :
    AngularBound blocks i j (polyNeg p) a b :=
  ⟨intervalNeg P.value, Interval.ofCoeff
    (angularDerivative_supported_at hi hj (intervalNeg P.value).support)
    (angularDerivative_neg i j p) (intervalNeg P.derivative)⟩

private def mulBound {blocks i j : Nat} {p q : RatPoly} {a b c d : Q'}
    (hi : i < 4 * blocks) (hj : j < 4 * blocks)
    (P : AngularBound blocks i j p a b) (Q : AngularBound blocks i j q c d) :
    AngularBound blocks i j (polyMul p q) (a*c) (b*c+a*d) :=
  ⟨P.value.mul Q.value, Interval.ofCoeff
    (angularDerivative_supported_at hi hj (P.value.mul Q.value).support)
    (angularDerivative_mul i j p q)
    ((P.derivative.mul Q.value).add (P.value.mul Q.derivative))⟩

/-- Original two-block relative scalar, with an ambient-size-independent
certificate for every supported coordinate rotation. -/
def scalarAngularInterval {blocks a b i j : Nat}
    (ha : a < blocks) (hb : b < blocks)
    (hi : i < 4 * blocks) (hj : j < 4 * blocks) :
    Interval blocks (angularDerivative i j (scalarAt a b)) 32 := by
  let A (k : Fin 4) := coordinateBound hi hj (show 4*a+k.val < 4*blocks by omega)
  let B (k : Fin 4) := coordinateBound hi hj (show 4*b+k.val < 4*blocks by omega)
  have H := addBound hi hj (mulBound hi hj (A 0) (B 0))
    (negBound hi hj (addBound hi hj (mulBound hi hj (A 1) (negBound hi hj (B 1)))
      (addBound hi hj (mulBound hi hj (A 2) (negBound hi hj (B 2)))
        (mulBound hi hj (A 3) (negBound hi hj (B 3))))))
  exact H.derivative.changeCap (by decide)

/-- One kinetic heat factor's actual angular derivative. All cutoff spins
are kept; the only rate dependence is the explicitly named strict nome. -/
def heatAngularInterval {blocks a b i j : Nat}
    (ha : a < blocks) (hb : b < blocks)
    (hi : i < 4 * blocks) (hj : j < 4 * blocks)
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) :
    Interval blocks (angularDerivative i j (heatAt a b w K)) (heatDerivativeCap w 32) := by
  let word := PolyQuaternion.mul (PolyQuaternion.coordinateVariable a)
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable b))
  have hp : Supported blocks word := (Supported.coordinate ha).mul (Supported.coordinate hb).conj
  have hu : HaarCarrierEqv blocks (polyQuaternionNorm word) polyOne :=
    haarNorm_mul (haarNorm_coordinate ha)
      (HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _))
        (haarNorm_coordinate hb))
  rw [heatAt_eq_prefix]
  exact heatPrefixAngularIntervalAt hi hj hw0 hw1 (SquareBound.scalar hp hu)
    (scalarAngularInterval ha hb hi hj) K

end YMGap.Continuum.SU2QuaternionRelativeHeatAngularBound

#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatAngularBound.scalarAngularInterval
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatAngularBound.heatAngularInterval
