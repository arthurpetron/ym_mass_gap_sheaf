/-
# Adaptive local curvature evaluated on the ACTUAL paired output score

The coefficients are the lifted original A*Db-b*DA, with A=T a and b=T c.
Each is an output-only polynomial on the doubled carrier. The lower frozen
six-direction heat curvature retains every ordered mixed entry and BOTH
original transfer outputs. It is not a conditional score bound: whole-product
assembly and the weighted conditional Gram/normalization join remain open.
-/

import YMGap.Continuum.SU2QuaternionFrozenSixHeatCurvature
import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepSourceDerivative

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFrozenScoreCurvature

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient (conditionalScore)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound (relativeCutoff)
open YMGap.Continuum.SU2QuaternionFrozenSixHeatCurvature

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks

private theorem supported_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro term ht
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
  exact hp q hq

private theorem score_supported {blocks s : Nat} (hs : s < blocks) (i : Fin 6)
    {A b : RatPoly} (hA : SupportedQuaternionBlocks blocks A)
    (hb : SupportedQuaternionBlocks blocks b) :
    SupportedQuaternionBlocks blocks
      (conditionalScore (4*s+(sixPlane i).1.val) (4*s+(sixPlane i).2.val) A b) := by
  have hi : 4*s+(sixPlane i).1.val < 4*blocks := by have := (sixPlane i).1.isLt; omega
  have hj : 4*s+(sixPlane i).2.val < 4*blocks := by have := (sixPlane i).2.isLt; omega
  exact supported_add (supported_polyMul hA (angularDerivative_supported_at hi hj hb))
    (supported_neg (supported_polyMul hb (angularDerivative_supported_at hi hj hA)))

/-- The actual coupled score, explicitly lifted to the output slice. -/
def lastStepScoreCoefficients (w : Q') (K width s : Nat) (a c : RatPoly)
    (i : Fin 6) : RatPoly :=
  liftBoundary (N width)
    (conditionalScore (4*s+(sixPlane i).1.val) (4*s+(sixPlane i).2.val)
      (transferStep w K width a) (transferStep w K width c))

/-- Local adaptive curvature input for the SAME original interacting score.
No source/terminal sign, inverse, norm comparison or stationarity is assumed.
The six is local and carries no active-block multiplicity. -/
def lastStep_frozen_six_score_curvature_certificate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width s : Nat) (hK : relativeCutoff w 32 ≤ K) (hs : s ∈ activeBlocks width)
    {a c : RatPoly} (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c) :
    Certificate (N width+N width)
      (frozenSixHeatEnvelope w hw0 hw1 K s (N width+s) (N width+s)
        (lastStepScoreCoefficients w K width s a c)) := by
  have hsN : s < N width := activeBlocks_lt width s hs
  apply heat_frozen_six_curvature_certificate (by omega) (by omega) (by omega)
    hw0 hw1 K hK
  intro i
  exact lift_supported
    (score_supported hsN i (transferStep_supported w K width ha)
      (transferStep_supported w K width hc)) (N width)

end YMGap.Continuum.BF4ExactSlabFixedSpatialFrozenScoreCurvature

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFrozenScoreCurvature.lastStep_frozen_six_score_curvature_certificate
