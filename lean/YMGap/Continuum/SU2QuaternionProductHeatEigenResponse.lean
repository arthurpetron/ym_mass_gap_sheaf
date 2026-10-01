/-
# Exact jump response for a tested product-heat eigenobservable

The input eigenpin is a supported Haar equality of the actual finite heat
image. It is not a positivity, stationarity, or interacting-mean premise.
No term of a signed observable is separated before its square is taken.
-/

import YMGap.Continuum.SU2QuaternionProductHeatJumpMean
import YMGap.Continuum.SU2QuaternionProductHeatSourceYoung
import YMGap.Continuum.SU2QuaternionProductHeatContraction

namespace YMGap.Continuum.SU2QuaternionProductHeatEigenResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatContraction
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump jump_supported)
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung (sourceIncrementCost)
open YMGap.Continuum.SU2QuaternionProductHeatJumpMean (jump_mean productHeat_mass_one)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
  (weightedPair weighted_cauchySchwarz)
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_one)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- The ordinary Haar source response of a tested heat eigenobservable. -/
def eigenResponse (n : Nat) (lambda : Q') (q f : RatPoly) : Q' :=
  2*((1 + -lambda)*H n (polyMul q f))

/-- The exact full-product-heat jump mean, with the entire supported
observable retained until after the heat image is pinned. -/
theorem eigen_jump_mean (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    {q f : RatPoly} (hq : SupportedQuaternionBlocks n q)
    (hf : SupportedQuaternionBlocks n f) (lambda : Q')
    (heig : SupportedHaarEqv n (productMap n w K ids f) (polySmul lambda f)) :
    weightedPair (n+n) (productHeat n w K ids)
        (polyMul (jump n q) (jump n f)) polyOne ≈
      eigenResponse n lambda q f := by
  have hp : H n (polyMul q (productMap n w K ids f)) ≈
      lambda * H n (polyMul q f) :=
    Q'.eqv_trans _ _ _ (heig q hq)
      (quaternionHaar_polyMul_smul_right n lambda q f)
  exact Q'.eqv_trans _ _ _ (jump_mean n w K ids hnd hids hq hf)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left 2 _ _
        (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ hp)))
      (poly_identity_of_normal_eq
        (.mul (.const 2) (.add (.var 0) (.neg (.mul (.var 1) (.var 0)))))
        (.mul (.const 2) (.mul (.add (.const 1) (.neg (.var 1))) (.var 0)))
        (by decide) (fun | 0 => H n (polyMul q f) | _ => lambda)))

/-- Weighted Cauchy--Schwarz against one retains the square of the actual
computed eigenresponse in the original source-increment correction. -/
theorem sourceIncrement_ge_eigenResponse_square (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    {q f : RatPoly} (hq : SupportedQuaternionBlocks n q)
    (hf : SupportedQuaternionBlocks n f) (lambda : Q')
    (heig : SupportedHaarEqv n (productMap n w K ids f) (polySmul lambda f)) :
    eigenResponse n lambda q f * eigenResponse n lambda q f ≤
      sourceIncrementCost n w K ids q f := by
  let r := polyMul (jump n q) (jump n f)
  let W := productHeat n w K ids
  have hr : SupportedQuaternionBlocks (n+n) r :=
    supported_polyMul (jump_supported hq) (jump_supported hf)
  have hc := weighted_cauchySchwarz (n+n) W r polyOne
    (productHeatCertificate n hw0 hw1 K hK ids hids) hr (supported_one _)
  have hm := productHeat_mass_one n w K ids hnd hids
  have hj := eigen_jump_mean n w K ids hnd hids hq hf lambda heig
  have hleft := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hj)
    (Q'.mul_eqv_congr_left _ _ _ hj)
  have hright := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hm)
    (Q'.mul_one_eqv (weightedPair (n+n) W r r))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hc (Q'.le_of_eqv hright))

#print axioms eigen_jump_mean
#print axioms sourceIncrement_ge_eigenResponse_square

end YMGap.Continuum.SU2QuaternionProductHeatEigenResponse
