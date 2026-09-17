/-
# One-step quadratic positivity for the ORIGINAL interacting slice transfer

The exact map is T f = P(V f), with the full original spatial weight V.
Its V-weighted quadratic is H[(V f) P(V f)], so the proved positive
semidefinite kinetic kernel applies directly to the supported polynomial
V f. No local-action replacement, fringe independence, normalization,
positive input, or late-cutoff density estimate is used.

This proves the finite original quadratic for all nonnegative nomes and
all cutoffs. It does not supply a positive-definite V-weighted state space
at cutoffs where V has no proved positive density, a strict gap, or a pin
to the CURRENT Wilson completion. Those statements remain separate.
-/

import YMGap.Continuum.SU2QuaternionProductHeatPositive
import YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_lt kineticWeight_eq_indexedProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition (step)
open YMGap.Continuum.SU2QuaternionHaarKernelBound (kernelMap)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productMap)
open YMGap.Continuum.SU2QuaternionProductHeatPositive (productMap_nonnegative)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight activeBlocks

/-- The exact original map, with the complete spatial action inside P. -/
theorem transferStep_eq_productMap (w : Q') (K width : Nat) (f : RatPoly) :
    transferStep w K width f = productMap (N width) w K (activeBlocks width)
      (polyMul (spatialWeight w K width) f) := by
  unfold transferStep step productMap kernelMap
  rw [kineticWeight_eq_indexedProduct]
  rfl

/-- Both sides retain the SAME V, source f, kinetic kernel and Haar measure. -/
theorem original_quadratic_pin (w : Q') (K width : Nat) (f : RatPoly) :
    weightedMass w K width (polyMul f (transferStep w K width f)) ≈
      quaternionHaar (N width)
        (polyMul (polyMul (spatialWeight w K width) f)
          (productMap (N width) w K (activeBlocks width)
            (polyMul (spatialWeight w K width) f))) := by
  rw [transferStep_eq_productMap]
  exact haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _).symm

/-- The original interacting finite one-step quadratic is nonnegative for
every supported signed polynomial, not only fringe-independent states. -/
theorem transferStep_quadratic_nonnegative (w : Q') (hw : (0 : Q') ≤ w)
    (K width : Nat) (f : RatPoly) (hf : SupportedQuaternionBlocks (N width) f) :
    (0 : Q') ≤ weightedMass w K width (polyMul f (transferStep w K width f)) :=
  Q'.le_trans' _ _ _
    (productMap_nonnegative (N width) w hw K (activeBlocks width) (activeBlocks_lt width)
      (polyMul (spatialWeight w K width) f)
      (supported_polyMul (spatialWeight_supported w K width) hf))
    (Q'.ge_of_eqv (original_quadratic_pin w K width f))

end YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive.transferStep_eq_productMap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive.original_quadratic_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive.transferStep_quadratic_nonnegative
