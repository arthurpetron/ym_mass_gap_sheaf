/-
# Exact mixed moments for the symmetric two-slice source test

The identity keeps the complete supported source under the original product
heat. No source factorization or stationarity is used.
-/

import YMGap.Continuum.SU2QuaternionProductHeatSumTest
import YMGap.Continuum.SU2QuaternionProductHeatDualForm

namespace YMGap.Continuum.SU2QuaternionProductHeatSumGram

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_product)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatSumTest (sumCopy sumTest)
open YMGap.Continuum.SU2QuaternionProductHeatDualForm (kineticPair kineticPair_symm)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
  (weightedPair weighted_add_left)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem pair_one (n : Nat) (W p : RatPoly) :
    weightedPair (n+n) W p polyOne ≈ H (n+n) (polyMul W p) :=
  haar_of_coeff
    (((RatPolyCoeffEqv.mul_one p).mul_right W).trans
      (RatPolyCoeffEqv.mul_comm p W))

/-- Exact mean of the symmetric source test under the unchanged product heat.
Both crossed terms use the same product map by heat symmetry. -/
theorem sumTest_mean (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    {q f : RatPoly} (hq : SupportedQuaternionBlocks n q)
    (hf : SupportedQuaternionBlocks n f) :
    weightedPair (n+n) (productHeat n w K ids) (sumTest n q f) polyOne ≈
      2*(H n (polyMul q f) + H n (polyMul q (productMap n w K ids f))) := by
  let W := productHeat n w K ids
  let a := polyMul q f
  let b := polyMul (liftBoundary n q) (liftBoundary n f)
  let c := polyMul q (liftBoundary n f)
  let d := polyMul f (liftBoundary n q)
  have hs : RatPolyCoeffEqv (sumTest n q f)
      (polyAdd (polyAdd a b) (polyAdd c d)) := by
    unfold sumTest sumCopy a b c d
    exact YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
      (.add (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
        (.add (.mul (.var 0) (.var 3)) (.mul (.var 2) (.var 1))))
      (by decide) (fun | 0 => q | 1 => liftBoundary n q | 2 => f | _ => liftBoundary n f)
  have ha : weightedPair (n+n) W a polyOne ≈ H n (polyMul q f) :=
    Q'.eqv_trans _ _ _ (pair_one n W a)
      (productHeat_lower_marginal n w K ids hnd hids a (supported_polyMul hq hf))
  have hb : weightedPair (n+n) W b polyOne ≈ H n (polyMul q f) := by
    have h : RatPolyCoeffEqv b (liftBoundary n a) := by
      unfold a b
      rw [lift_product]
      exact RatPolyCoeffEqv.refl _
    exact Q'.eqv_trans _ _ _ (pair_one n W b)
      (Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.refl W).mul h))
        (productHeat_upper_marginal n w K ids hnd hids a (supported_polyMul hq hf)))
  have hd : weightedPair (n+n) W d polyOne ≈
      H n (polyMul q (productMap n w K ids f)) := by
    have h : H (n+n) (polyMul W d) ≈
        H (n+n) (polyMul W (polyMul f (liftBoundary n q))) := Q'.eqv_refl _
    exact Q'.eqv_trans _ _ _ (pair_one n W d)
      (Q'.eqv_trans _ _ _ h (Q'.eqv_symm (productMap_pairing n w K ids f q)))
  have hc : weightedPair (n+n) W c polyOne ≈
      H n (polyMul q (productMap n w K ids f)) := by
    have hp : weightedPair (n+n) W c polyOne ≈
        H n (polyMul f (productMap n w K ids q)) :=
      Q'.eqv_trans _ _ _ (pair_one n W c)
        (Q'.eqv_symm (productMap_pairing n w K ids q f))
    exact Q'.eqv_trans _ _ _ hp
      (kineticPair_symm n w K ids hids f q hf hq)
  have hsum : weightedPair (n+n) W (sumTest n q f) polyOne ≈
      (weightedPair (n+n) W a polyOne + weightedPair (n+n) W b polyOne) +
      (weightedPair (n+n) W c polyOne + weightedPair (n+n) W d polyOne) :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff ((hs.mul_right polyOne).mul_right W))
      (by
        change weightedPair (n+n) W (polyAdd (polyAdd a b) (polyAdd c d)) polyOne ≈ _
        exact Q'.eqv_trans _ _ _
          (weighted_add_left (n+n) W (polyAdd a b) (polyAdd c d) polyOne)
          (Q'.add_eqv_congr' (weighted_add_left (n+n) W a b polyOne)
            (weighted_add_left (n+n) W c d polyOne)))
  exact Q'.eqv_trans _ _ _ hsum
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.add_eqv_congr' ha hb) (Q'.add_eqv_congr' hc hd))
      (YMGap.Continuum.RingNormaliser.poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 0)) (.add (.var 1) (.var 1)))
        (.mul (.const 2) (.add (.var 0) (.var 1)))
        (by decide)
        (fun | 0 => H n (polyMul q f) | _ => H n (polyMul q (productMap n w K ids f)))))

#print axioms sumTest_mean

end YMGap.Continuum.SU2QuaternionProductHeatSumGram
