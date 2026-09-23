/-
# Mixed angular bounds for the original relative quaternion heat

Two arbitrary supported block rotations may overlap.  The four coordinate
products in the relative scalar nevertheless have an explicit mixed bound on
the original Haar carrier. The actual heat prefix consequently has an
explicit nome-dependent bound independent of cutoff and ambient dimension.
This is a local curvature input, not a normalized joint score or mass gap.
-/

import YMGap.Continuum.SU2QuaternionAngularCoordinate
import YMGap.Continuum.SU2QuaternionRelativeHeatAngularBound
import YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
import YMGap.Continuum.QuaternionHaarHeatSecondAngularDerivative

namespace YMGap.Continuum.SU2QuaternionRelativeHeatSecondAngularBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarCoordinateAngularInterval
open YMGap.Continuum.SU2QuaternionAngularCoordinate
open YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRelativeHeatAngularBound
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarHeatSecondAngularDerivative

private structure MixedJet (blocks oi oj ii ij : Nat) (p : RatPoly)
    (a b c d : Q') : Type where
  value : Interval blocks p a
  inner : Interval blocks (angularDerivative ii ij p) b
  outer : Interval blocks (angularDerivative oi oj p) c
  mixed : Interval blocks (angularDerivative oi oj (angularDerivative ii ij p)) d

private def conditionalCoordinate {blocks r coordinate output : Nat}
    (hout : output < 4 * blocks) :
    Interval blocks (if r = coordinate then polyVar output else polyZero) 1 := by
  by_cases h : r = coordinate
  · rw [if_pos h]
    exact coordinateInterval hout
  · rw [if_neg h]
    exact (Interval.zero blocks).weaken (by decide)

private def coordinateAngular {blocks block i j coordinate : Nat}
    (hb : block < blocks) (hi : i < 4) (hj : j < 4)
    (hc : coordinate < 4 * blocks) :
    Interval blocks
      (angularDerivative (4*block+i) (4*block+j) (polyVar coordinate)) 2 := by
  have hxi : 4*block+i < 4*blocks := by omega
  have hxj : 4*block+j < 4*blocks := by omega
  have R := (conditionalCoordinate (r := 4*block+j) (coordinate := coordinate) hxi).add
    (Interval.ofCoeff
      (polySmul_supported
        (conditionalCoordinate (r := 4*block+i) (coordinate := coordinate) hxj).support (-1))
      (neg_smul _).symm
      (intervalNeg
        (conditionalCoordinate (r := 4*block+i) (coordinate := coordinate) hxj)))
  exact intervalOfCarrier
    (angularDerivative_supported_at hxi hxj (coordinateInterval hc).support)
    (angular_coordinate_carrier hc) R

private def coordinateJet {blocks ob ib oi oj ii ij coordinate : Nat}
    (hob : ob < blocks) (hib : ib < blocks)
    (hoi : oi < 4) (hoj : oj < 4) (hii : ii < 4) (hij : ij < 4)
    (hc : coordinate < 4 * blocks) :
    MixedJet blocks (4*ob+oi) (4*ob+oj) (4*ib+ii) (4*ib+ij)
      (polyVar coordinate) 1 2 2 4 := by
  have hin := angular_coordinate_carrier (blocks := blocks)
    (i := 4*ib+ii) (j := 4*ib+ij) hc
  have hxi : 4*ib+ii < 4*blocks := by omega
  have hxj : 4*ib+ij < 4*blocks := by omega
  have rhsOuter : Interval blocks
      (angularDerivative (4*ob+oi) (4*ob+oj)
        (polyAdd (if 4*ib+ij = coordinate then polyVar (4*ib+ii) else polyZero)
          (polySmul (-1)
            (if 4*ib+ii = coordinate then polyVar (4*ib+ij) else polyZero)))) 4 := by
    have L : Interval blocks
        (angularDerivative (4*ob+oi) (4*ob+oj)
          (if 4*ib+ij = coordinate then polyVar (4*ib+ii) else polyZero)) 2 := by
      by_cases h : 4*ib+ij = coordinate
      · rw [if_pos h]
        exact coordinateAngular hob hoi hoj hxi
      · rw [if_neg h]
        change Interval blocks (angularDerivative (4*ob+oi) (4*ob+oj) polyZero) 2
        rw [show angularDerivative (4*ob+oi) (4*ob+oj) polyZero = polyZero from rfl]
        exact (Interval.zero blocks).weaken (by decide)
    have R : Interval blocks
        (angularDerivative (4*ob+oi) (4*ob+oj)
          (polySmul (-1)
            (if 4*ib+ii = coordinate then polyVar (4*ib+ij) else polyZero))) 2 := by
      by_cases h : 4*ib+ii = coordinate
      · rw [if_pos h]
        exact Interval.ofCoeff
          (angularDerivative_supported_at (by omega) (by omega)
            (polySmul_supported (coordinateInterval hxj).support (-1)))
          (angularDerivative_smul _ _ (-1) _)
          (Interval.ofCoeff
            (polySmul_supported (coordinateAngular hob hoi hoj hxj).support (-1))
            (neg_smul _).symm (intervalNeg (coordinateAngular hob hoi hoj hxj)))
      · rw [if_neg h]
        change Interval blocks
          (angularDerivative (4*ob+oi) (4*ob+oj) (polySmul (-1) polyZero)) 2
        rw [show polySmul (-1) polyZero = polyZero from rfl,
          show angularDerivative (4*ob+oi) (4*ob+oj) polyZero = polyZero from rfl]
        exact (Interval.zero blocks).weaken (by decide)
    exact Interval.ofCoeff
      (angularDerivative_supported_at (by omega) (by omega)
        (supported_add
          (conditionalCoordinate (r := 4*ib+ij) (coordinate := coordinate) hxi).support
          (polySmul_supported
            (conditionalCoordinate (r := 4*ib+ii) (coordinate := coordinate) hxj).support (-1))))
      (angularDerivative_add _ _ _ _) (L.add R)
  exact ⟨coordinateInterval hc,
    coordinateAngular hib hii hij hc,
    coordinateAngular hob hoi hoj hc,
    intervalOfCarrier
      (angularDerivative_supported_at (by omega) (by omega)
        (angularDerivative_supported_at hxi hxj (coordinateInterval hc).support))
      (angularDerivative_carrier_at hob hoi hoj hin) rhsOuter⟩

private def MixedJet.add {blocks oi oj ii ij : Nat} {p q : RatPoly}
    {a b c d e f g h : Q'} (hoi : oi < 4*blocks) (hoj : oj < 4*blocks)
    (hii : ii < 4*blocks) (hij : ij < 4*blocks)
    (P : MixedJet blocks oi oj ii ij p a b c d)
    (Q : MixedJet blocks oi oj ii ij q e f g h) :
    MixedJet blocks oi oj ii ij (polyAdd p q) (a+e) (b+f) (c+g) (d+h) :=
  ⟨P.value.add Q.value,
   Interval.ofCoeff (angularDerivative_supported_at hii hij
      (P.value.add Q.value).support) (angularDerivative_add _ _ _ _) (P.inner.add Q.inner),
   Interval.ofCoeff (angularDerivative_supported_at hoi hoj
      (P.value.add Q.value).support) (angularDerivative_add _ _ _ _) (P.outer.add Q.outer),
   Interval.ofCoeff (angularDerivative_supported_at hoi hoj
      (angularDerivative_supported_at hii hij
        (P.value.add Q.value).support))
      ((angularDerivative_congr _ _ (angularDerivative_add _ _ _ _)).trans
        (angularDerivative_add _ _ _ _)) (P.mixed.add Q.mixed)⟩

private def MixedJet.neg {blocks oi oj ii ij : Nat} {p : RatPoly}
    {a b c d : Q'} (hoi : oi < 4*blocks) (hoj : oj < 4*blocks)
    (hii : ii < 4*blocks) (hij : ij < 4*blocks)
    (P : MixedJet blocks oi oj ii ij p a b c d) :
    MixedJet blocks oi oj ii ij (polyNeg p) a b c d :=
  ⟨intervalNeg P.value,
   Interval.ofCoeff (angularDerivative_supported_at hii hij (intervalNeg P.value).support)
      (angularDerivative_neg _ _ _) (intervalNeg P.inner),
   Interval.ofCoeff (angularDerivative_supported_at hoi hoj (intervalNeg P.value).support)
      (angularDerivative_neg _ _ _) (intervalNeg P.outer),
   Interval.ofCoeff (angularDerivative_supported_at hoi hoj
      (angularDerivative_supported_at hii hij (intervalNeg P.value).support))
      ((angularDerivative_congr _ _ (angularDerivative_neg _ _ _)).trans
        (angularDerivative_neg _ _ _)) (intervalNeg P.mixed)⟩

private def MixedJet.mul {blocks oi oj ii ij : Nat} {p q : RatPoly}
    {a b c d e f g h : Q'} (hoi : oi < 4*blocks) (hoj : oj < 4*blocks)
    (hii : ii < 4*blocks) (hij : ij < 4*blocks)
    (P : MixedJet blocks oi oj ii ij p a b c d)
    (Q : MixedJet blocks oi oj ii ij q e f g h) :
    MixedJet blocks oi oj ii ij (polyMul p q)
      (a*e) (b*e+a*f) (c*e+a*g) ((d*e+b*g)+(c*f+a*h)) := by
  refine ⟨P.value.mul Q.value,
    Interval.ofCoeff (angularDerivative_supported_at hii hij (P.value.mul Q.value).support)
      (angularDerivative_mul _ _ _ _) ((P.inner.mul Q.value).add (P.value.mul Q.inner)),
    Interval.ofCoeff (angularDerivative_supported_at hoi hoj (P.value.mul Q.value).support)
      (angularDerivative_mul _ _ _ _) ((P.outer.mul Q.value).add (P.value.mul Q.outer)), ?_⟩
  exact Interval.ofCoeff
    (angularDerivative_supported_at hoi hoj
      (angularDerivative_supported_at hii hij (P.value.mul Q.value).support))
    ((angularDerivative_congr _ _ (angularDerivative_mul _ _ p q)).trans
      ((angularDerivative_add _ _ _ _).trans
        ((angularDerivative_mul _ _ _ _).add (angularDerivative_mul _ _ _ _))))
    (((P.mixed.mul Q.value).add (P.inner.mul Q.outer)).add
      ((P.outer.mul Q.inner).add (P.value.mul Q.mixed)))

/-- The mixed angular derivative of the actual relative scalar has a uniform
cap `64`, for arbitrary (possibly equal or overlapping) supported rotations. -/
def scalarAt_mixedAngularInterval
    {blocks a b s t i j k l : Nat}
    (ha : a < blocks) (hb : b < blocks) (hs : s < blocks) (ht : t < blocks)
    (hi : i < 4) (hj : j < 4) (hk : k < 4) (hl : l < 4) :
    Interval blocks
      (angularDerivative (4*s+i) (4*s+j)
        (angularDerivative (4*t+k) (4*t+l) (scalarAt a b))) 64 := by
  have hoi : 4*s+i < 4*blocks := by omega
  have hoj : 4*s+j < 4*blocks := by omega
  have hii : 4*t+k < 4*blocks := by omega
  have hij : 4*t+l < 4*blocks := by omega
  let A (r : Fin 4) := coordinateJet hs ht hi hj hk hl
    (show 4*a+r.val < 4*blocks by omega)
  let B (r : Fin 4) := coordinateJet hs ht hi hj hk hl
    (show 4*b+r.val < 4*blocks by omega)
  have H := MixedJet.add hoi hoj hii hij (MixedJet.mul hoi hoj hii hij (A 0) (B 0))
    (MixedJet.neg hoi hoj hii hij
      (MixedJet.add hoi hoj hii hij
        (MixedJet.mul hoi hoj hii hij (A 1) (MixedJet.neg hoi hoj hii hij (B 1)))
        (MixedJet.add hoi hoj hii hij
          (MixedJet.mul hoi hoj hii hij (A 2) (MixedJet.neg hoi hoj hii hij (B 2)))
          (MixedJet.mul hoi hoj hii hij (A 3) (MixedJet.neg hoi hoj hii hij (B 3))))))
  exact H.mixed.changeCap (by decide)

/-- Actual relative heat, every cutoff, and any two supported block planes.
No disjointness, distinct-plane or independent-variable assumption is used. -/
def heatSecondAngularInterval
    {blocks a b s t i j k l : Nat}
    (ha : a < blocks) (hb : b < blocks) (hs : s < blocks) (ht : t < blocks)
    (hi : i < 4) (hj : j < 4) (hk : k < 4) (hl : l < 4)
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) :
    Interval blocks
      (angularDerivative (4*s+i) (4*s+j)
        (angularDerivative (4*t+k) (4*t+l) (heatAt a b w K)))
      (heatSecondDerivativeCap w 32 32 64) := by
  let word := PolyQuaternion.mul (PolyQuaternion.coordinateVariable a)
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable b))
  have hp : Supported blocks word := (Supported.coordinate ha).mul (Supported.coordinate hb).conj
  have hu : HaarCarrierEqv blocks (polyQuaternionNorm word) polyOne :=
    haarNorm_mul (haarNorm_coordinate ha)
      (HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _))
        (haarNorm_coordinate hb))
  rw [heatAt_eq_prefix]
  exact heatPrefixSecondAngularIntervalAt (by omega) (by omega) (by omega) (by omega)
    hw0 hw1 (SquareBound.scalar hp hu)
    (scalarAngularInterval ha hb (by omega) (by omega))
    (scalarAngularInterval ha hb (by omega) (by omega))
    (scalarAt_mixedAngularInterval ha hb hs ht hi hj hk hl) K

end YMGap.Continuum.SU2QuaternionRelativeHeatSecondAngularBound

#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatSecondAngularBound.scalarAt_mixedAngularInterval
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatSecondAngularBound.heatSecondAngularInterval
