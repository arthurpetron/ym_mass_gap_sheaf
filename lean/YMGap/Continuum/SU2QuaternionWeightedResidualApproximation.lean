/-
# Division-free error of an explicitly seeded weighted residual

Let m=P_i(nu), e=1-nu*m*J and q=weightedResidual i nu (J*tau).
For a genuine Haar fluctuation P_i(tau)=0, the exact coefficient identity is

  m*(nu*q-tau) = nu*P_i(e*tau)-m*e*tau.

The seed, residual and defect are all original rational polynomials. The
existing weightedResidual_supported and project_weightedResidual_zero supply
support and exact weighted centering at every finite choice of J. This
identity does not assume positivity or an inverse, and does not assert
approximation convergence, an error budget, or a physical spectral gap.
Its consumer is a finite Haar telescope with explicit polynomial inverse
approximants for nu*P_i(nu).
-/

import YMGap.Continuum.SU2QuaternionWeightedBlockCentering

namespace YMGap.Continuum.SU2QuaternionWeightedResidualApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionWeightedBlockCentering

/-- The actual finite seed has an exact cleared error, with its conditional
projection retained. No support, positivity, division or limit premise is used. -/
theorem weightedResidual_seed_error (block : Nat) (nu J tau : RatPoly)
    (htau : RatPolyCoeffEqv (project block tau) polyZero) :
    let m := project block nu
    let e := polyAdd polyOne (polyNeg (polyMul (polyMul nu m) J))
    let q := weightedResidual block nu (polyMul J tau)
    RatPolyCoeffEqv
      (polyMul m (polyAdd (polyMul nu q) (polyNeg tau)))
      (polyAdd (polyMul nu (project block (polyMul e tau)))
        (polyNeg (polyMul (polyMul m e) tau))) := by
  let m := project block nu
  let e := polyAdd polyOne (polyNeg (polyMul (polyMul nu m) J))
  let p := project block (polyMul nu (polyMul J tau))
  have he : RatPolyCoeffEqv (polyMul e tau)
      (polyAdd tau (polyNeg (polyMul m (polyMul nu (polyMul J tau))))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.const 1) (.neg (.mul (.mul (.var 0) (.var 1)) (.var 2)))) (.var 3))
      (.add (.var 3) (.neg (.mul (.var 1) (.mul (.var 0) (.mul (.var 2) (.var 3))))))
      (by decide) (fun | 0 => nu | 1 => m | 2 => J | _ => tau)
  have hproject : RatPolyCoeffEqv (project block (polyMul e tau))
      (polyNeg (polyMul m p)) := by
    have h := project_congr block he
    rw [project_add] at h
    exact (h.trans ((RatPolyCoeffEqv.refl _).add (project_neg block _))).trans
      ((htau.add (RatPolyCoeffEqv.neg
        (project_mul_of_independent block m (polyMul nu (polyMul J tau))
          (project_independent block nu)))).trans (RatPolyCoeffEqv.zero_add _))
  have hraw : RatPolyCoeffEqv
      (polyMul m (polyAdd
        (polyMul nu (weightedResidual block nu (polyMul J tau))) (polyNeg tau)))
      (polyAdd (polyMul nu (polyNeg (polyMul m p)))
        (polyNeg (polyMul (polyMul m e) tau))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 1)
        (.add (.mul (.var 0)
          (.add (.mul (.var 1) (.mul (.var 2) (.var 3))) (.neg (.var 4))))
          (.neg (.var 3))))
      (.add (.mul (.var 0) (.neg (.mul (.var 1) (.var 4))))
        (.neg (.mul (.mul (.var 1)
          (.add (.const 1) (.neg (.mul (.mul (.var 0) (.var 1)) (.var 2)))))
          (.var 3))))
      (by decide) (fun | 0 => nu | 1 => m | 2 => J | 3 => tau | _ => p)
  exact hraw.trans ((hproject.symm.mul_left nu).add (RatPolyCoeffEqv.refl _))

end YMGap.Continuum.SU2QuaternionWeightedResidualApproximation

#print axioms YMGap.Continuum.SU2QuaternionWeightedResidualApproximation.weightedResidual_seed_error
