/-
# Original finite terminal messages preserve the full vertex center sign

The full spatial action is unchanged under its geometric vertex star.
The original product kinetic map intertwines the same lower/upper signs.
Consequently the actual finite messages T^n 1, and their full endpoint
weights V*T^n 1, are invariant coefficientwise. No reduced terminal
sequence, stationary vacuum, gauge-invariant odd state, or gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStar
import YMGap.Continuum.SU2QuaternionProductHeatCenterSign
import YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarTransfer

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_lt kineticWeight_eq_indexedProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStar
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage terminalMessage_supported)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatCenterSign
open YMGap.Continuum.SU2QuaternionHaarKernelBound (kernelMap)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (step iterateStep partialHaarHeads_congr)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight

private theorem transfer_productMap (w : Q') (K width : Nat) (f : RatPoly) :
    transferStep w K width f =
      productMap (N width) w K (activeBlocks width) (polyMul (spatialWeight w K width) f) := by
  simp only [transferStep, step, productMap, kernelMap, productHeat, kineticWeight_eq_indexedProduct]

/-- Original transfer equivariance, on the complete retained slice. -/
theorem transferStep_starSign (w : Q') (K width : Nat) (v : Z4Vertex)
    {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    RatPolyCoeffEqv (starSign width v (transferStep w K width f))
      (transferStep w K width (starSign width v f)) := by
  rw [transfer_productMap, transfer_productMap]
  have h := productMap_centerSign (N width) (blockSelector width v) w K
    (activeBlocks width) (activeBlocks_lt width) (supported_polyMul (spatialWeight_supported w K width) hf)
  exact h.trans (productMap_congr (N width) w K (activeBlocks width)
    ((starSign_mul width v (spatialWeight w K width) f).trans
      ((spatialWeight_starSign w K width v).mul (.refl _))))

private theorem transfer_congr (w : Q') (K width : Nat) {f g : RatPoly}
    (h : RatPolyCoeffEqv f g) : RatPolyCoeffEqv (transferStep w K width f) (transferStep w K width g) :=
  partialHaarHeads_congr (N width) ((h.mul_left (spatialWeight w K width)).mul_left (kineticWeight w K width))

private theorem iterate_front (blocks : Nat) (kernel weight : RatPoly) (n : Nat) (f : RatPoly) :
    iterateStep blocks kernel weight (n+1) f = step blocks kernel weight
      (iterateStep blocks kernel weight n f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => exact ih (step blocks kernel weight f)

/-- The actual finite message, not a newly defined invariant replacement. -/
theorem terminalMessage_starSign (w : Q') (K width : Nat) (v : Z4Vertex) : ∀ n,
    RatPolyCoeffEqv (starSign width v (terminalMessage w K width n)) (terminalMessage w K width n)
  | 0 => by change RatPolyCoeffEqv (starSign width v polyOne) polyOne; rw [starSign_one]; exact .refl _
  | n+1 => by
    have he : terminalMessage w K width (n+1) = transferStep w K width (terminalMessage w K width n) :=
      iterate_front _ _ _ n polyOne
    rw [he]
    exact (transferStep_starSign w K width v (terminalMessage_supported w K width n)).trans
      (transfer_congr w K width (terminalMessage_starSign w K width v n))

/-- All spatial and finite-message factors of the original endpoint weight remain. -/
theorem endpointWeight_starSign (w : Q') (K width : Nat) (v : Z4Vertex) (n : Nat) :
    RatPolyCoeffEqv
      (starSign width v (polyMul (spatialWeight w K width) (terminalMessage w K width n)))
      (polyMul (spatialWeight w K width) (terminalMessage w K width n)) :=
  (starSign_mul width v _ _).trans
    ((spatialWeight_starSign w K width v).mul (terminalMessage_starSign w K width v n))

end YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarTransfer

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarTransfer.transferStep_starSign
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarTransfer.terminalMessage_starSign
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarTransfer.endpointWeight_starSign
