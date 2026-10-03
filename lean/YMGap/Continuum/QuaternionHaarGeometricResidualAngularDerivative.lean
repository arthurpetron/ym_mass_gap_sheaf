/-
# Exact signed derivative of the finite geometric residual

The existing residual is (-R)^k on the ORIGINAL shared polynomial carrier.
Its successor angular derivative is exactly -(k+1)*(-R)^k*D R,
at coefficient equality. Actual intervals therefore retain the factor
(k+1)*rho^k without replacing the source or its derivative by an oracle.
No reciprocal limit, relative filtered-norm estimate or scaling conclusion
is asserted.
-/

import YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse
import YMGap.Continuum.QuaternionHaarAngularCarrier

namespace YMGap.Continuum.QuaternionHaarGeometricResidualAngularDerivative

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse
open YMGap.Continuum.QuaternionHaarAngularCarrier

private theorem negative_successor (k : Nat) :
    Q'.eqv ((-1 : Q') + -(Q'.ofNat (k+1))) (-(Q'.ofNat (k+2))) := by
  have h : Q'.eqv ((1 : Q') + Q'.ofNat (k+1)) (Q'.ofNat (k+2)) :=
    Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _)
      (Q'.eqv_symm (Q'.ofNat_add_eqv (k+1) 1))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))
    (Q'.neg_eqv_congr _ _ h)

/-- The exact finite residual derivative, including the initial successor.
The rotation coordinates are arbitrary: this is raw coefficient algebra. -/
theorem residual_angularDerivative_succ (i j : Nat) (R : RatPoly) : ∀ k : Nat,
    RatPolyCoeffEqv (angularDerivative i j (residual R (k+1)))
      (polySmul (-(Q'.ofNat (k+1)))
        (polyMul (residual R k) (angularDerivative i j R)))
  | 0 => by
      have hleft : RatPolyCoeffEqv
          (angularDerivative i j (residual R 1))
          (polySmul (-1) (angularDerivative i j R)) :=
        (angularDerivative_congr i j (RatPolyCoeffEqv.mul_one (polyNeg R))).trans
          ((angularDerivative_neg i j R).trans (neg_smul _))
      have hright : RatPolyCoeffEqv
          (polySmul (-(Q'.ofNat 1))
            (polyMul (residual R 0) (angularDerivative i j R)))
          (polySmul (-1) (angularDerivative i j R)) :=
        ((RatPolyCoeffEqv.one_mul _).smul (-(Q'.ofNat 1))).trans
          (RatPolyCoeffEqv.smul_coefficient (by decide) _)
      exact hleft.trans hright.symm
  | k+1 => by
      let dR := angularDerivative i j R
      let P := polyMul (residual R (k+1)) dR
      have hneg : RatPolyCoeffEqv (angularDerivative i j (polyNeg R))
          (polySmul (-1) dR) :=
        (angularDerivative_neg i j R).trans (neg_smul _)
      have hfirst : RatPolyCoeffEqv
          (polyMul (angularDerivative i j (polyNeg R)) (residual R (k+1)))
          (polySmul (-1) P) :=
        (hneg.mul_right _).trans
          ((RatPolyCoeffEqv.polyMul_smul_left (-1) dR _).trans
            ((RatPolyCoeffEqv.mul_comm dR _).smul (-1)))
      have hsecond : RatPolyCoeffEqv
          (polyMul (polyNeg R) (angularDerivative i j (residual R (k+1))))
          (polySmul (-(Q'.ofNat (k+1))) P) :=
        ((residual_angularDerivative_succ i j R k).mul_left (polyNeg R)).trans
          ((RatPolyCoeffEqv.polyMul_smul_right (-(Q'.ofNat (k+1)))
            (polyNeg R) (polyMul (residual R k) dR)).trans
              ((RatPolyCoeffEqv.mul_assoc (polyNeg R) (residual R k) dR).symm.smul
                (-(Q'.ofNat (k+1)))))
      exact (angularDerivative_mul i j (polyNeg R) (residual R (k+1))).trans
        ((hfirst.add hsecond).trans
          ((RatPolyCoeffEqv.add_smul_same (-1) (-(Q'.ofNat (k+1))) P).trans
            (RatPolyCoeffEqv.smul_coefficient (negative_successor k) P)))

/-- A constructed derivative interval on the SAME shared Haar coordinates.
The derivative cost remains the supplied actual derivative interval cap. -/
def residualAngularInterval {blocks i j : Nat} {R : RatPoly} {rho c : Q'}
    (hi : i < 4*blocks) (hj : j < 4*blocks)
    (P : Interval blocks R rho)
    (Q : Interval blocks (angularDerivative i j R) c) (k : Nat) :
    Interval blocks (angularDerivative i j (residual R (k+1)))
      (Q'.ofNat (k+1) * (rho^k*c)) := by
  have hn : (0 : Q') ≤ Q'.ofNat (k+1) := by
    rw [Q'.zero_le_iff_num_nonneg]
    exact Int.natCast_nonneg (k+1)
  let I := ((residualInterval P k).mul Q).smul (Q'.ofNat (k+1)) hn
  have h : RatPolyCoeffEqv
      (polySmul (-(Q'.ofNat (k+1)))
        (polyMul (residual R k) (angularDerivative i j R)))
      (polyNeg (polySmul (Q'.ofNat (k+1))
        (polyMul (residual R k) (angularDerivative i j R)))) := by
    let B := polyMul (residual R k) (angularDerivative i j R)
    exact ((neg_smul (polySmul (Q'.ofNat (k+1)) B)).trans
      ((RatPolyCoeffEqv.smul_assoc (-1) (Q'.ofNat (k+1)) B).trans
        (RatPolyCoeffEqv.smul_coefficient
          (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))) B))).symm
  exact Interval.ofCoeff
    (angularDerivative_supported_at hi hj (residualInterval P (k+1)).support)
    ((residual_angularDerivative_succ i j R k).trans h) (intervalNeg I)

end YMGap.Continuum.QuaternionHaarGeometricResidualAngularDerivative

#print axioms YMGap.Continuum.QuaternionHaarGeometricResidualAngularDerivative.residual_angularDerivative_succ
#print axioms YMGap.Continuum.QuaternionHaarGeometricResidualAngularDerivative.residualAngularInterval
