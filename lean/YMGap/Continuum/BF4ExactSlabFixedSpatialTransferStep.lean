/-
# The original swept layer acts on one fixed spatial polynomial carrier

Construct T f by integrating the first N coordinates of K(x,y)V(x)f(x).
The result is again on the SAME N-coordinate carrier. Its weighted pairing
with g equals the original ambient V0*K01*V1 pairing under the exact lower
and upper placements. Both endpoint weights occur once.

This is a finite signed polynomial map and an original swept-action pairing.
It is not a bounded/completed OS transfer, a stationary normalization, or a
contraction estimate. Arbitrary polynomial inputs are not thereby declared
gauge-invariant original observables under a new temporal sweep.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat
import YMGap.Continuum.SU2QuaternionHaarBlockEmbeddingPlacement
import YMGap.Continuum.SU2QuaternionHeadChainComposition

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPairCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_pin spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGluing
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)
local infix:50 " ≈ " => Q'.eqv

/-- Computed original K/V step, before any positivity or completion claim. -/
def transferStep (w : Q') (K width : Nat) (input : RatPoly) : RatPoly :=
  step (N width) (kineticWeight w K width) (spatialWeight w K width) input

theorem transferStep_supported (w : Q') (K width : Nat) {input : RatPoly}
    (hi : SupportedQuaternionBlocks (N width) input) :
    SupportedQuaternionBlocks (N width) (transferStep w K width input) :=
  step_supported (kineticWeight_supported w K width) (spatialWeight_supported w K width) hi

theorem lower_polynomial_pin {width start extent : Nat}
    (hw : width ≤ extent) (ht : start+1 ≤ extent)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (N width) p) :
    (embedding hw ht).polynomial p =
      (BF4ExactSlabFixedSpatialSliceCarrier.embedding hw (show start ≤ extent by omega)).polynomial p :=
  (BF4ExactSlabFixedSpatialSliceCarrier.embedding hw (show start ≤ extent by omega)).polynomial_head_placement
    (embedding hw ht) (by omega) (fun _ hi => lower_block hw ht hi) p hp

theorem upper_polynomial_pin {width start extent : Nat}
    (hw : width ≤ extent) (ht : start+1 ≤ extent)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (N width) p) :
    (embedding hw ht).polynomial (liftBoundary (N width) p) =
      (BF4ExactSlabFixedSpatialSliceCarrier.embedding hw ht).polynomial p :=
  (BF4ExactSlabFixedSpatialSliceCarrier.embedding hw ht).polynomial_liftBoundary
    (embedding hw ht) (N width) (by omega) (fun i _ => upper_block hw ht i) p hp

/-- The original swept V0*K01*V1 pairing, with explicit source support.
The pairing is weighted by V on both ends; the step integrates V only once. -/
theorem swept_step_pairing {width start extent : Nat}
    (hw : width ≤ extent) (ht : start+1 ≤ extent) (w : Q') (K : Nat)
    (f g : RatPoly) (hf : SupportedQuaternionBlocks (N width) f)
    (hg : SupportedQuaternionBlocks (N width) g) :
    quaternionHaar (B extent)
      (polyMul
        (polyMul (kineticHeat w K extent width start)
          (polyMul (spatialHeat w K extent width start)
            ((BF4ExactSlabFixedSpatialSliceCarrier.embedding hw (show start ≤ extent by omega)).polynomial f)))
        (polyMul (spatialHeat w K extent width (start+1))
          ((BF4ExactSlabFixedSpatialSliceCarrier.embedding hw ht).polynomial g))) ≈
      quaternionHaar (N width)
        (polyMul (transferStep w K width f) (polyMul (spatialWeight w K width) g)) := by
  let E := embedding hw ht
  let L := BF4ExactSlabFixedSpatialSliceCarrier.embedding hw (show start ≤ extent by omega)
  let U := BF4ExactSlabFixedSpatialSliceCarrier.embedding hw ht
  let v := spatialWeight w K width
  let k := kineticWeight w K width
  have hv := spatialWeight_supported w K width
  have hvg := supported_polyMul hv hg
  have hleft : PaddedPolynomialCoeffEqv (B extent)
      (E.polynomial (polyMul k (polyMul v f)))
      (polyMul (kineticHeat w K extent width start) (polyMul (spatialHeat w K extent width start) (L.polynomial f))) := by
    simp only [BlockEmbedding.polynomial_mul]
    rw [lower_polynomial_pin hw ht v hv, lower_polynomial_pin hw ht f hf]
    exact (kineticWeight_pin hw ht w K).mul
      ((spatialWeight_pin hw (show start ≤ extent by omega) w K).mul (.refl _ _))
  have hright : PaddedPolynomialCoeffEqv (B extent)
      (E.polynomial (liftBoundary (N width) (polyMul v g)))
      (polyMul (spatialHeat w K extent width (start+1)) (U.polynomial g)) := by
    rw [upper_polynomial_pin hw ht _ hvg, BlockEmbedding.polynomial_mul]
    exact (spatialWeight_pin hw ht w K).mul (.refl _ _)
  have hpin := hleft.mul hright
  rw [← E.polynomial_mul] at hpin
  have hsource : SupportedQuaternionBlocks (N width+N width)
      (polyMul (polyMul k (polyMul v f)) (liftBoundary (N width) (polyMul v g))) :=
    supported_polyMul
      (supported_polyMul (kineticWeight_supported w K width)
        (fun term hm => Nat.le_trans (supported_polyMul hv hf term hm) (by omega)))
      (lift_supported hvg (N width))
  have hambient := supported_polyMul
    (supported_polyMul (kineticHeat_supported w K extent width start)
      (supported_polyMul (heatProduct_supported w K extent (spatialIds extent width start)) (L.polynomial_supported f)))
    (supported_polyMul (heatProduct_supported w K extent (spatialIds extent width (start+1))) (U.polynomial_supported g))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (hpin.haar (E.polynomial_supported _) hambient))
    (Q'.eqv_trans _ _ _ (E.haar _ hsource)
      (step_pairing (N width) (N width) k v f (polyMul v g)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep.transferStep
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep.transferStep_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep.lower_polynomial_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep.upper_polynomial_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep.swept_step_pairing
