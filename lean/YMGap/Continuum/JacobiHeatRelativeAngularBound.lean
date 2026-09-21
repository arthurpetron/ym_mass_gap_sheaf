/-
# Relative angular estimate for the actual positive Jacobi heat polynomials

The original finite product and its positive Leibniz derivative satisfy the
same relative angular budget. The coefficient-level Jacobi identity then
transports this estimate to the existing weighted character polynomial.
The cost is explicit in the nome and independent of the Jacobi cutoff.

This does NOT identify the weighted polynomial with an unweighted heat
cutoff. Removing those weights after differentiation remains necessary.
-/

import YMGap.Continuum.QuaternionHaarRelativeAngularBound
import YMGap.Continuum.JacobiShiftedRelativeSlope
import YMGap.Continuum.JacobiWeightedHeatPolynomial

namespace YMGap.Continuum.JacobiHeatRelativeAngularBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarRelativeAngularBound
open YMGap.Continuum.QPolyHaarPositiveSubstitution
open YMGap.Continuum.QPolyRatPolySubstitutionAlgebra
open YMGap.Continuum.JTPFullProductDerivativeNormalization
open YMGap.Continuum.SU2PointwiseHeatPositiveCompletion
open YMGap.Continuum.JacobiShiftedPositiveCoefficients
open YMGap.Continuum.JacobiShiftedRelativeSlope

def prefixCost (q d : Q') (N : Nat) : Q' := d * finSum (rate q) N
def relativeCost (q d : Q') : Q' := d * budget q

private theorem cost_succ (q d : Q') (N : Nat) :
    Q'.eqv (prefixCost q d N + d * rate q N) (prefixCost q d (N+1)) := by
  change Q'.eqv (d * finSum (rate q) N + d * rate q N)
    (d * (finSum (rate q) N + rate q N))
  exact poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
    (.mul (.var 0) (.add (.var 1) (.var 2))) (by decide)
    (fun | 0 => d | 1 => finSum (rate q) N | _ => rate q N)

/-- The actual shifted factor, including its Euler factor, receives the
denominator-cleared relative certificate. -/
def factorBound {blocks i j : Nat} {x : RatPoly} {q d : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (X : Certificate blocks x) (DX : Interval blocks (angularDerivative i j x) d)
    (k : Nat) : RelativeBound blocks i j (subst x (factor q k)) (d * rate q k) :=
  .ofCoeff ((RatPolyCoeffEqv.refl _).add
    (((subst_singleton x (gFacDx q k)).mul_left x).trans (RatPolyCoeffEqv.mul_comm _ _)))
    (RelativeBound.affine X DX (Q'.le_of_lt (base_pos hq0 hq1 k))
      (Q'.le_of_lt (slope_pos hq0 hq1 k)) (rate_nonnegative hq0 k)
      (slope_le_rate_mul_base hq0 hq1 k))

/-- Simultaneous positive-product induction: the product and its existing
Leibniz derivative have the same additive relative cost. -/
def productDerivativeBounds {blocks i j : Nat} {x : RatPoly} {q d : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (X : Certificate blocks x) (DX : Interval blocks (angularDerivative i j x) d) :
    (N : Nat) →
      RelativeBound blocks i j (subst x (product q N)) (prefixCost q d N) ×
      RelativeBound blocks i j (subst x (derivative q N)) (prefixCost q d N)
  | 0 => ⟨(RelativeBound.ofCoeff (subst_singleton x 1)
        (RelativeBound.constant blocks i j 1 Q'.zero_le_one)).changeCap
          (Q'.eqv_symm (Q'.mul_zero_eqv d)),
      (RelativeBound.zero blocks i j).changeCap (Q'.eqv_symm (Q'.mul_zero_eqv d))⟩
  | N+1 => by
      let previous := productDerivativeBounds hq0 hq1 X DX N
      let nextFactor := factorBound hq0 hq1 X DX N
      have growth : prefixCost q d N ≤ prefixCost q d (N+1) :=
        Q'.le_trans' _ _ _
          (Q'.add_le_self_of_nonneg _ _ (Q'.mul_nonneg _ _ DX.nonnegative (rate_nonnegative hq0 N)))
          (Q'.le_of_eqv (cost_succ q d N))
      refine ⟨.ofCoeff (subst_pmul x _ _) ((previous.1.mul nextFactor).changeCap (cost_succ q d N)), ?_⟩
      exact .ofCoeff ((subst_padd x _ _).trans
        ((subst_pmul x _ _).add (subst_pscale x (gFacDx q N) _)))
        (((previous.2.mul nextFactor).changeCap (cost_succ q d N)).add
          ((previous.1.smul (gFacDx q N) (Q'.le_of_lt (slope_pos hq0 hq1 N))).weaken growth))

/-- Correct inverse-nome/half normalization is retained. This estimate has
one explicit nome-dependent cost for every finite Jacobi cutoff. -/
def heatBound {blocks i j : Nat} {x : RatPoly} {q d : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (X : Certificate blocks x) (DX : Interval blocks (angularDerivative i j x) d)
    (N : Nat) : RelativeBound blocks i j (subst x (heat q N)) (relativeCost q d) :=
  (RelativeBound.ofCoeff (subst_pscale x _ _)
    (((productDerivativeBounds hq0 hq1 X DX N).2).smul (inverseNome q * HalfPow.half)
      (Q'.mul_nonneg _ _ (inverseNome_nonnegative q) HalfPow.half_nonneg))).weaken
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (prefix_le_budget hq0 hq1 N) DX.nonnegative)

/-- Same original quaternion scalar and coefficient-level weighted heat,
valid with all shared-variable positive Haar insertions. -/
def weightedHeatBound {blocks i j : Nat} {p : PolyQuaternion} {q d : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hi : i < 4*blocks) (hj : j < 4*blocks)
    (hp : Supported blocks p) (hu : HaarCarrierEqv blocks (polyQuaternionNorm p) polyOne)
    (DX : Interval blocks (angularDerivative i j p.scalar) d) (N : Nat) :
    RelativeBound blocks i j (JacobiWeightedHeatPolynomial.weightedPolynomial q N p.scalar)
      (relativeCost q d) := by
  have dt : RatPolyCoeffEqv (angularDerivative i j (polyAdd polyOne p.scalar))
      (angularDerivative i j p.scalar) :=
    (angularDerivative_add i j polyOne p.scalar).trans
      (((angularDerivative_one i j).add (.refl _)).trans (RatPolyCoeffEqv.zero_add _))
  let DT := Interval.ofCoeff
    (angularDerivative_supported_at hi hj (supported_add (supported_one blocks) hp.scalar)) dt DX
  exact .ofCoeff
    (JacobiWeightedHeatPolynomial.shiftedHeat_subst_coeffEqv_weightedPolynomial hq0 hq1 N p.scalar).symm
    (heatBound hq0 hq1 (oneAddScalar_certificate hp hu) DT N)

end YMGap.Continuum.JacobiHeatRelativeAngularBound

#print axioms YMGap.Continuum.JacobiHeatRelativeAngularBound.prefixCost
#print axioms YMGap.Continuum.JacobiHeatRelativeAngularBound.relativeCost
#print axioms YMGap.Continuum.JacobiHeatRelativeAngularBound.factorBound
#print axioms YMGap.Continuum.JacobiHeatRelativeAngularBound.productDerivativeBounds
#print axioms YMGap.Continuum.JacobiHeatRelativeAngularBound.heatBound
#print axioms YMGap.Continuum.JacobiHeatRelativeAngularBound.weightedHeatBound
