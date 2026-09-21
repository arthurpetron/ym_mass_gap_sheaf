/-
# Euler identities after one head derivative

The raw rational derivative retains zero-coefficient monomials, so its
homogeneous degree is exposed through the existing active derivative before
transporting back by coefficient equality.  Summing the four resulting Euler
identities gives the exact falling-factorial coefficient `n (n-1)` needed by
the angular Casimir algebra.  This is finite polynomial algebra only; it adds
no analytic, heat-kernel, or action hypothesis.
-/

import YMGap.Continuum.SU2QuaternionHeadDegreeDifferential

namespace YMGap.Continuum.SU2QuaternionHeadDerivativeEuler

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadDegreeDifferential

/-- The head Euler operator respects coefficient-probe equality. -/
theorem headEuler_congr {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (headEuler p) (headEuler q) := by
  unfold headEuler
  exact ((h.derivative 0).mul_left (polyVar 0)).add
    (((h.derivative 1).mul_left (polyVar 1)).add
      (((h.derivative 2).mul_left (polyVar 2)).add
        ((h.derivative 3).mul_left (polyVar 3))))

/-- Differentiating a head-homogeneous polynomial lowers its Euler
coefficient by one.  The statement is coefficient-sensitive and remains
valid at degree zero through truncated natural subtraction. -/
theorem headEuler_derivative_of_blockDegree {i n : Nat} {p : RatPoly}
    (hi : i < 4) (hp : HasQuaternionBlockDegree 0 n p) :
    RatPolyCoeffEqv (headEuler (ratDerivative i p))
      (polySmul (Q'.ofNat (n - 1)) (ratDerivative i p)) := by
  let d := activeDerivative i p
  have hc : RatPolyCoeffEqv d (ratDerivative i p) := activeDerivative_coeff i p
  have hd : HasQuaternionBlockDegree 0 (n - 1) d := activeDerivative_degree hi hp
  exact (headEuler_congr hc).symm.trans
    ((headEuler_of_blockDegree (n - 1) d hd).trans (hc.smul (Q'.ofNat (n - 1))))

/-- Coordinate-weighted Euler fields of all four first derivatives. -/
def secondEulerSum (p : RatPoly) : RatPoly :=
  polyFour
    (polyMul (polyVar 0) (headEuler (ratDerivative 0 p)))
    (polyMul (polyVar 1) (headEuler (ratDerivative 1 p)))
    (polyMul (polyVar 2) (headEuler (ratDerivative 2 p)))
    (polyMul (polyVar 3) (headEuler (ratDerivative 3 p)))

/-- On head degree `n`, the second Euler sum is multiplication by the exact
falling factorial `(n-1)n`. -/
theorem secondEulerSum_of_blockDegree {n : Nat} {p : RatPoly}
    (hp : HasQuaternionBlockDegree 0 n p) :
    RatPolyCoeffEqv (secondEulerSum p)
      (polySmul (Q'.ofNat (n - 1) * Q'.ofNat n) p) := by
  let a := Q'.ofNat (n - 1)
  have h0 := headEuler_derivative_of_blockDegree (p := p) (i := 0) (n := n) (by decide) hp
  have h1 := headEuler_derivative_of_blockDegree (p := p) (i := 1) (n := n) (by decide) hp
  have h2 := headEuler_derivative_of_blockDegree (p := p) (i := 2) (n := n) (by decide) hp
  have h3 := headEuler_derivative_of_blockDegree (p := p) (i := 3) (n := n) (by decide) hp
  have hderivative : RatPolyCoeffEqv (secondEulerSum p)
      (polyFour
        (polyMul (polyVar 0) (polySmul a (ratDerivative 0 p)))
        (polyMul (polyVar 1) (polySmul a (ratDerivative 1 p)))
        (polyMul (polyVar 2) (polySmul a (ratDerivative 2 p)))
        (polyMul (polyVar 3) (polySmul a (ratDerivative 3 p)))) := by
    unfold secondEulerSum
    exact (h0.mul_left (polyVar 0)).add
      ((h1.mul_left (polyVar 1)).add
        ((h2.mul_left (polyVar 2)).add (h3.mul_left (polyVar 3))))
  have hpull : RatPolyCoeffEqv
      (polyFour
        (polyMul (polyVar 0) (polySmul a (ratDerivative 0 p)))
        (polyMul (polyVar 1) (polySmul a (ratDerivative 1 p)))
        (polyMul (polyVar 2) (polySmul a (ratDerivative 2 p)))
        (polyMul (polyVar 3) (polySmul a (ratDerivative 3 p))))
      (polySmul a (headEuler p)) := by
    change RatPolyCoeffEqv _
      (polySmul a (polyFour
        (polyMul (polyVar 0) (ratDerivative 0 p))
        (polyMul (polyVar 1) (ratDerivative 1 p))
        (polyMul (polyVar 2) (ratDerivative 2 p))
        (polyMul (polyVar 3) (ratDerivative 3 p))))
    exact ((RatPolyCoeffEqv.polyMul_smul_right a (polyVar 0) (ratDerivative 0 p)).add
      ((RatPolyCoeffEqv.polyMul_smul_right a (polyVar 1) (ratDerivative 1 p)).add
        ((RatPolyCoeffEqv.polyMul_smul_right a (polyVar 2) (ratDerivative 2 p)).add
          (RatPolyCoeffEqv.polyMul_smul_right a (polyVar 3) (ratDerivative 3 p))))).trans
      (polyFour_smul a _ _ _ _)
  exact hderivative.trans (hpull.trans
    (((headEuler_of_blockDegree n p hp).smul a).trans
      (RatPolyCoeffEqv.smul_assoc a (Q'.ofNat n) p)))

end YMGap.Continuum.SU2QuaternionHeadDerivativeEuler

#print axioms YMGap.Continuum.SU2QuaternionHeadDerivativeEuler.headEuler_congr
#print axioms YMGap.Continuum.SU2QuaternionHeadDerivativeEuler.headEuler_derivative_of_blockDegree
#print axioms YMGap.Continuum.SU2QuaternionHeadDerivativeEuler.secondEulerSum
#print axioms YMGap.Continuum.SU2QuaternionHeadDerivativeEuler.secondEulerSum_of_blockDegree
