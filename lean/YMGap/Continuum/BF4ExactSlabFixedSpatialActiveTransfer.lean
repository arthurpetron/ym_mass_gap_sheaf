/-
# The original transfer on fringe-independent polynomials

The actual kinetic kernel is symmetric in the two fixed slice carriers.
Its adjoint test omits every inactive coordinate. Exact spatial face
peeling can therefore be applied with the full transfer spectator, giving
the ORIGINAL T=K V on the active subspace as K V_A under supported Haar
tests. This is not replacement by an auxiliary heat-bath dynamics.

The identity holds at every rational nome and finite cutoff, without
positivity, division or a spectral estimate. No completed or limiting
operator identification is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSpatialWeight
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialActiveTransfer

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_lt kineticWeight_eq_indexedProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticSymmetry (kineticWeight_swap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry (kernel_pairing_swap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow
  (fringeBlocks fringeBlocks_mem_iff fringeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSpatialWeight
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent quaternionBlockIndependent_polyMul)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (step)
open YMGap.Continuum.SU2QuaternionHaarKernelBound (kernelMap)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
  (productHeat productMap productMap_supported productMap_pairing productMap_independent_of_not_mem)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight kineticWeight activeBlocks

/-- Same kinetic map; only the exactly integrated spatial action is written
in its local active-face form. This definition is meaningful for every input. -/
def activeTransfer (w : Q') (K width : Nat) (f : RatPoly) : RatPoly :=
  productMap (N width) w K (activeBlocks width) (polyMul (activeSpatialWeight w K width) f)

theorem activeTransfer_supported (w : Q') (K width : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    SupportedQuaternionBlocks (N width) (activeTransfer w K width f) :=
  productMap_supported (N width) w K (activeBlocks width) (activeBlocks_lt width)
    (supported_polyMul (activeSpatialWeight_supported w K width) hf)

private theorem transfer_product (w : Q') (K width : Nat) (f : RatPoly) :
    transferStep w K width f = productMap (N width) w K (activeBlocks width)
      (polyMul (spatialWeight w K width) f) := by
  unfold transferStep step productMap kernelMap
  rw [kineticWeight_eq_indexedProduct]
  rfl

/-- Haar symmetry of the literal kinetic part, on the original fixed slice. -/
theorem kineticMap_symmetric (w : Q') (K width : Nat) {f p : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f)
    (hp : SupportedQuaternionBlocks (N width) p) :
    quaternionHaar (N width) (polyMul p (productMap (N width) w K (activeBlocks width) f)) ≈
      quaternionHaar (N width) (polyMul f (productMap (N width) w K (activeBlocks width) p)) := by
  have hs := kernel_pairing_swap (kineticWeight_supported w K width) hf hp (kineticWeight_swap w K width)
  rw [kineticWeight_eq_indexedProduct] at hs
  exact Q'.eqv_trans _ _ _ (productMap_pairing (N width) w K (activeBlocks width) f p)
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _).symm)
      (Q'.eqv_trans _ _ _ hs
        (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _))
          (Q'.eqv_symm (productMap_pairing (N width) w K (activeBlocks width) p f)))))

/-- Exact tested equality with the ORIGINAL transfer on the active subspace.
The test p need not be fringe-independent; its kinetic image is. -/
theorem original_transfer_haar_active (w : Q') (K width : Nat) {f p : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f)
    (hi : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i f)
    (hp : SupportedQuaternionBlocks (N width) p) :
    quaternionHaar (N width) (polyMul p (transferStep w K width f)) ≈
      quaternionHaar (N width) (polyMul p (activeTransfer w K width f)) := by
  let Pp := productMap (N width) w K (activeBlocks width) p
  have hP := productMap_supported (N width) w K (activeBlocks width) (activeBlocks_lt width) hp
  have hPi : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i Pp := fun i h =>
    productMap_independent_of_not_mem (N width) w K (activeBlocks width) (activeBlocks_lt width)
      i (fringeBlocks_lt width i h) ((fringeBlocks_mem_iff width i).mp h).2 p hp
  rw [transfer_product]
  exact Q'.eqv_trans _ _ _
    (kineticMap_symmetric w K width (supported_polyMul (spatialWeight_supported w K width) hf) hp)
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _))
      (Q'.eqv_trans _ _ _
        (spatialWeight_haar_active w K width (polyMul f Pp) (supported_polyMul hf hP)
          (fun i h => quaternionBlockIndependent_polyMul (hi i h) (hPi i h)))
        (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _).symm)
          (Q'.eqv_symm (kineticMap_symmetric w K width
            (supported_polyMul (activeSpatialWeight_supported w K width) hf) hp)))))

end YMGap.Continuum.BF4ExactSlabFixedSpatialActiveTransfer

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActiveTransfer.activeTransfer
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActiveTransfer.activeTransfer_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActiveTransfer.kineticMap_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActiveTransfer.original_transfer_haar_active
