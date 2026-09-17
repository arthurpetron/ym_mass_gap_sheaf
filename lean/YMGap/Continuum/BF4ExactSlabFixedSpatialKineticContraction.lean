/-
# The original complete kinetic layer is Haar-nonexpansive

Both exact marginals of the ORIGINAL kineticWeight and its existing positive
certificate give squared-norm bound one, independent of spatial width, nome,
and late cutoff. The nome-dependent positivity threshold is unchanged.
Unused fringe links remain inside the actual partial Haar integration.

For the actual weighted transfer this proves ||T f||^2 <= H[(V f)^2], with
EVERY original spatial factor retained in V. It removes the previous kinetic
cap penalty but does not bound V uniformly in width, nor supply a strict
full-product centered bound or an interacting OS spectral gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
import YMGap.Continuum.BF4ExactSlabFixedSpatialKineticOrder
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
import YMGap.Continuum.SU2QuaternionHaarMarkovContraction

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialKineticContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.SU2QuaternionHaarMarkovContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

/-- No normalization, link deletion, or replacement kernel. -/
def kineticMap (w : Q') (K width : Nat) (f : RatPoly) : RatPoly :=
  kernelMap (N width) (kineticWeight w K width) f

theorem kineticMap_supported (w : Q') (K width : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    SupportedQuaternionBlocks (N width) (kineticMap w K width f) :=
  kernelMap_supported (kineticWeight_supported w K width) hf

/-- Exact mean preservation at EVERY cutoff, including zero. -/
theorem kineticMap_mean (w : Q') (K width : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    quaternionHaar (N width) (kineticMap w K width f) ≈ quaternionHaar (N width) f :=
  Q'.eqv_trans _ _ _ (quaternionHaar_partialHaarHeads (N width) (N width) _)
    (kineticWeight_lower_marginal w K width f hf)

/-- Bound one for all supported inputs; no temporal-face-count penalty. -/
theorem kineticMap_square_contraction {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    quaternionHaar (N width) (polyMul (kineticMap w K width f) (kineticMap w K width f)) ≤
      quaternionHaar (N width) (polyMul f f) :=
  kernelMap_square_contraction (kineticWeight_lower_marginal w K width)
    (kineticWeight_upper_marginal w K width)
    (kineticCertificate hw0 hw1 K width hK) (kineticWeight_supported w K width) hf

/-- The spatial potential stays inside the SAME original transfer. -/
theorem transferStep_kineticMap (w : Q') (K width : Nat) (f : RatPoly) :
    transferStep w K width f = kineticMap w K width (polyMul (spatialWeight w K width) f) := rfl

/-- Concrete consumer: the kinetic penalty disappears, not the interaction. -/
theorem transferStep_square_le_spatialSquare {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    quaternionHaar (N width) (polyMul (transferStep w K width f) (transferStep w K width f)) ≤
      quaternionHaar (N width) (polyMul (polyMul (spatialWeight w K width) f)
        (polyMul (spatialWeight w K width) f)) :=
  kineticMap_square_contraction hw0 hw1 K width hK
    (supported_polyMul (spatialWeight_supported w K width) hf)

end YMGap.Continuum.BF4ExactSlabFixedSpatialKineticContraction

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticContraction.kineticMap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticContraction.kineticMap_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticContraction.kineticMap_mean
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticContraction.kineticMap_square_contraction
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticContraction.transferStep_kineticMap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticContraction.transferStep_square_le_spatialSquare
