/-
# Constant preservation for the selected product heat

The normalized finite product heat fixes constants after testing against every
supported polynomial.  This is the exact `SupportedHaarEqv` statement supplied
by the Haar marginal; it is not a free-polynomial identity and asserts neither
injectivity nor strict positivity.

The accompanying scalar and negation laws are coefficient-level consequences
of the already constructed linear `productMap`.
-/

import YMGap.Continuum.SU2QuaternionProductHeatMarginals
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound

namespace YMGap.Continuum.SU2QuaternionProductHeatConstant

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound

local infix:50 " ≈ " => Q'.eqv

/-- Exact coefficient linearity of the selected product map. -/
theorem productMap_smul (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (c : Q') (f : RatPoly) :
    RatPolyCoeffEqv (productMap n w K ids (polySmul c f))
      (polySmul c (productMap n w K ids f)) :=
  kernelMap_smul n (productHeat n w K ids) c f

private theorem smul_neg (p : RatPoly) :
    RatPolyCoeffEqv (polySmul (-1) p) (polyNeg p) :=
  (cap_mul_left (-1) p).symm.trans
    (coeffEvalExpr_eqv_of_normalize_eq (.mul (.const (-1)) (.var 0))
      (.neg (.var 0)) (by decide) (fun _ => p))

/-- Exact coefficient compatibility with polynomial negation. -/
theorem productMap_neg (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (f : RatPoly) :
    RatPolyCoeffEqv (productMap n w K ids (polyNeg f))
      (polyNeg (productMap n w K ids f)) :=
  (productMap_congr n w K ids (smul_neg f).symm).trans
    ((productMap_smul n w K ids (-1) f).trans (smul_neg _))

/-- The normalized selected product heat fixes one under every supported Haar
test.  Repeated indices are excluded exactly where the product marginal needs
them excluded. -/
theorem productMap_one (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hn : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n) :
    SupportedHaarEqv n (productMap n w K ids polyOne) polyOne := by
  intro p hp
  exact Q'.eqv_trans _ _ _ (productMap_pairing n w K ids polyOne p)
    (Q'.eqv_trans _ _ _
      (haar_of_coeff ((RatPolyCoeffEqv.refl (productHeat n w K ids)).mul
        (RatPolyCoeffEqv.one_mul (liftBoundary n p))))
      (Q'.eqv_trans _ _ _ (productHeat_upper_marginal n w K ids hn hids p hp)
        (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.mul_one p)))))

/-- Every rational scalar constant is fixed in the same tested-Haar sense. -/
theorem productMap_cap (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hn : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n) (c : Q') :
    SupportedHaarEqv n (productMap n w K ids (cap c)) (cap c) :=
  (SupportedHaarEqv.of_carrier
    (RatPolyCoeffEqv.haarCarrier (productMap_smul n w K ids c polyOne))).trans
    ((productMap_one n w K ids hn hids).smul c)

end YMGap.Continuum.SU2QuaternionProductHeatConstant

#print axioms YMGap.Continuum.SU2QuaternionProductHeatConstant.productMap_smul
#print axioms YMGap.Continuum.SU2QuaternionProductHeatConstant.productMap_neg
#print axioms YMGap.Continuum.SU2QuaternionProductHeatConstant.productMap_one
#print axioms YMGap.Continuum.SU2QuaternionProductHeatConstant.productMap_cap
