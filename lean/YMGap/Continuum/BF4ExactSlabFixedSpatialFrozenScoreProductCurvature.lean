/-
# Original kinetic factor: additive adaptive score-jet envelope

The product base is the LITERAL original kineticWeight and all coefficients
are the lifted SAME A*Di b-b*Di A, A=T a, b=T c. Local costs add over actual
active factors. Every product cross jet remains; no global loss is repeated
once per active block and no coefficient is differentiated.

The first/second product jets still use frozen Leibniz recursion. Direct
whole-kernel angular differential pins, conditional integration/Gram bounds,
output weighting/normalization and useful scaling are NOT supplied here.
This is not a completed OS norm comparison or a physical mass-gap bound.
-/

import YMGap.Continuum.SU2QuaternionProductHeatFrozenJetCurvature
import YMGap.Continuum.BF4ExactSlabFixedSpatialFrozenScoreCurvature

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFrozenScoreProductCurvature

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_lt kineticWeight_eq_indexedProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFrozenScoreCurvature
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_supported)
open YMGap.Continuum.SU2QuaternionFrozenSixHeatCurvature (sixPlane)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productHeat)
open YMGap.Continuum.SU2QuaternionProductHeatFrozenJetCurvature
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient (conditionalScore)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound (relativeCutoff)
open YMGap.Continuum.QuaternionHaarPolynomialJetCurvature (jetCurvature)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks

private theorem supported_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro term ht
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
  exact hp q hq

/-- The actual adaptive coefficient is supported on the SAME doubled carrier. -/
theorem lastStepScoreCoefficients_supported
    (w : Q') (K width s : Nat) (hs : s ∈ activeBlocks width)
    {a c : RatPoly} (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c) (i : Fin 6) :
    SupportedQuaternionBlocks (N width+N width)
      (lastStepScoreCoefficients w K width s a c i) := by
  have hsN := activeBlocks_lt width s hs
  have hi : 4*s+(sixPlane i).1.val < 4*N width := by have := (sixPlane i).1.isLt; omega
  have hj : 4*s+(sixPlane i).2.val < 4*N width := by have := (sixPlane i).2.isLt; omega
  have hA := transferStep_supported w K width ha
  have hb := transferStep_supported w K width hc
  exact lift_supported
    (supported_add (supported_polyMul hA (angularDerivative_supported_at hi hj hb))
      (supported_neg (supported_polyMul hb (angularDerivative_supported_at hi hj hA)))) (N width)

/-- Additive frozen-JET curvature for the ORIGINAL kinetic product with
its ACTUAL coupled transfer-score coefficients, not an unrelated heat model. -/
def original_kinetic_frozenScoreJet_certificate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : relativeCutoff w 32 ≤ K)
    {a c : RatPoly} (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c) :
    let u := fun s => lastStepScoreCoefficients w K width s a c
    Certificate (N width+N width)
      (jetCurvature (productFrozenCost w hw0 hw1 u (activeBlocks width))
        (kineticWeight w K width)
        (productFrozenFirst (N width) w K u (activeBlocks width))
        (productFrozenSecond (N width) w K u (activeBlocks width))) := by
  dsimp only
  rw [kineticWeight_eq_indexedProduct]
  exact productHeat_frozenJet_curvature_certificate (N width) hw0 hw1 K hK _
    (activeBlocks width) (activeBlocks_lt width)
    (fun s hs i => lastStepScoreCoefficients_supported w K width s hs ha hc i)

end YMGap.Continuum.BF4ExactSlabFixedSpatialFrozenScoreProductCurvature

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFrozenScoreProductCurvature.lastStepScoreCoefficients_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFrozenScoreProductCurvature.original_kinetic_frozenScoreJet_certificate
