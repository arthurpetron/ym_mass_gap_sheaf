/-
# Weighted continuity of the ORIGINAL finite transfer block

The actual positive upper certificate for T1 and the terminal Schur
estimate give ell[(Tf)^2] <= C^2 ell[f^2], then its finite iterate.
Every step retains the original spatial action. Signed inputs and zero
norms are allowed, including the explicit zero-step case.

C=kineticCap*ell[1] retains its cutoff, nome and width dependence. This
coarse coefficient is only an approximation-continuity tool: it is not
the terminal-relative U^2 coefficient in the sharper Schur estimate,
nor a relative survival estimate or changing-family bound.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSchurTest
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferWeightedBound
import YMGap.Constructive.Geometric

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialBlockWeightedContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
  (weightedMass transferStepUpperCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferWeightedBound
  (transferWeightedCap transferWeightedCap_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (weightedMass_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (iterateStep_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSchurTest
  (original_block_terminal_schur_square_le)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight kineticWeight weightedMass

private theorem transfer_congr (w : Q') (K width : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (transferStep w K width p) (transferStep w K width q) :=
  partialHaarHeads_congr (N width)
    ((h.mul_left (spatialWeight w K width)).mul_left (kineticWeight w K width))

private theorem block_succ (w : Q') (K width d : Nat) (f : RatPoly) :
    originalBlockTransfer w K width (d+1) f =
      transferStep w K width (originalBlockTransfer w K width d f) := by
  simpa only [originalBlockTransfer, iterateStep, transferStep] using
    iterateStep_add (N width) (kineticWeight w K width) (spatialWeight w K width) d 1 f

/-- The actual T1 cap yields continuity in the SAME spatially weighted
square norm, without assuming positivity of the signed input. -/
theorem transferStep_weighted_square_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    weightedMass w K width
        (polyMul (transferStep w K width f) (transferStep w K width f)) ≤
      (transferWeightedCap w K width * transferWeightedCap w K width) *
        weightedMass w K width (polyMul f f) := by
  have PU : Certificate (N width)
      (polyAdd (polySmul (transferWeightedCap w K width) polyOne)
        (polyNeg (originalBlockTransfer w K width 1 polyOne))) := by
    simpa only [transferWeightedCap, cap, originalBlockTransfer, iterateStep,
      transferStep] using
      transferStepUpperCertificate hw0 hw1 K width hK
        (supported_one (N width)) (Certificate.one (N width))
  have hs := original_block_terminal_schur_square_le hw0 hw1 K width hK 1
    (supported_one (N width)) hf (Certificate.one (N width))
    (transferWeightedCap w K width)
    (transferWeightedCap_nonnegative hw0 hw1 K width hK) PU
  have hunit : RatPolyCoeffEqv (polyMul polyOne f) f := RatPolyCoeffEqv.one_mul f
  have hstep : RatPolyCoeffEqv
      (originalBlockTransfer w K width 1 (polyMul polyOne f))
      (transferStep w K width f) := transfer_congr w K width hunit
  have hl := weightedMass_congr w K width (hstep.mul hstep)
  have hr := weightedMass_congr w K width (hunit.mul hunit)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl)
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv
      (Q'.mul_eqv_congr_left
        (transferWeightedCap w K width * transferWeightedCap w K width) _ _ hr)))

/-- Finite iteration of the original weighted continuity estimate. The
zero-step case is identity, and each intermediate support is constructed. -/
theorem originalBlockTransfer_weighted_square_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) (d : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    weightedMass w K width
        (polyMul (originalBlockTransfer w K width d f)
          (originalBlockTransfer w K width d f)) ≤
      (transferWeightedCap w K width * transferWeightedCap w K width)^d *
        weightedMass w K width (polyMul f f) := by
  let C := transferWeightedCap w K width * transferWeightedCap w K width
  have hC : (0 : Q') ≤ C :=
    SumOfSquares.q_mul_self_nonneg (transferWeightedCap w K width)
  change weightedMass w K width
    (polyMul (originalBlockTransfer w K width d f)
      (originalBlockTransfer w K width d f)) ≤ C^d * weightedMass w K width (polyMul f f)
  induction d with
  | zero =>
      change weightedMass w K width (polyMul f f) ≤
        (1 : Q') * weightedMass w K width (polyMul f f)
      exact Q'.ge_of_eqv (Q'.one_mul_eqv _)
  | succ d ih =>
      have hd : SupportedQuaternionBlocks (N width)
          (originalBlockTransfer w K width d f) :=
        iterateStep_supported (kineticWeight_supported w K width)
          (spatialWeight_supported w K width) d hf
      have hs := transferStep_weighted_square_le hw0 hw1 K width hK hd
      have hm := Q'.mul_le_mul_of_nonneg_left _ _ C ih hC
      have he : C*(C^d * weightedMass w K width (polyMul f f)) ≈
          C^(d+1)*weightedMass w K width (polyMul f f) :=
        Q'.eqv_symm (Q'.mul_assoc_eqv C (C^d) _)
      rw [block_succ]
      exact Q'.le_trans' _ _ _ hs
        (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv he))

end YMGap.Continuum.BF4ExactSlabFixedSpatialBlockWeightedContinuity

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBlockWeightedContinuity.transferStep_weighted_square_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBlockWeightedContinuity.originalBlockTransfer_weighted_square_le
