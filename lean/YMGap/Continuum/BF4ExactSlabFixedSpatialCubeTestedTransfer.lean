/-
# Exact tested ORIGINAL cutoff-one cube transfer channels

The literal first-face test is moved through the original kinetic map.
The full original width-two carrier and action are retained. Its multiplier
is w^12, and the already proved action moments then evaluate the channels.
These identities hold at every rational nome; no positivity, head cutoff,
interacting variance, favorable gain, or scaling assertion is made.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentActionMoment
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumActionMoment
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTestedTransfer

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow
  (fringeBlocks fringeBlocks_lt fringeBlocks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSpatialWeight
  (activeSpatialWeight activeSpatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActiveTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentFusion (firstFaceTrace)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentActionMoment
  (tested_bent_action_channel)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumActionMoment
  (tested_vacuum_action_channel)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff supported_one)
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.RingNormaliser (qpow poly_identity_of_normal_eq)

local notation "N" => List.length (baseLinks 2)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks

private theorem firstFace_supported : SupportedQuaternionBlocks N firstFaceTrace :=
  character_supported (plaquette_supported 2 N (Nat.le_refl _) ((0,0,0,0),.p01)).scalar 1

private theorem firstFace_eigen (w : Q') :
    SupportedHaarEqv N
      (SU2QuaternionProductHeatMarginals.productMap N w 1
        (BF4ExactSlabFixedSpatialKineticMarginals.activeBlocks 2) firstFaceTrace)
      (polySmul (qpow w 12) firstFaceTrace) := by
  have hbase := (spatialFaces_mem_iff 1 ((0,0,0,0),.p01)).mpr (by decide)
  have hface := (spatialFaces_mem_iff 2 ((0,0,0,0),.p01)).mpr (by decide)
  exact plaquette_kinetic_eigen 2 ((0,0,0,0),.p01) hface
    (plaquette_active_after_padding (by decide : 1 < 2) _ hbase) w 1 (by decide)

private theorem tested_transfer (w : Q') {f : RatPoly}
    (hf : SupportedQuaternionBlocks N f)
    (hfr : ∀ i, i ∈ fringeBlocks 2 → QuaternionBlockIndependent i f) :
    quaternionHaar N (polyMul firstFaceTrace (transferStep w 1 2 f)) ≈
      qpow w 12 * quaternionHaar N (polyMul (polyMul firstFaceTrace f) (cubeWeight w 1)) := by
  let W := activeSpatialWeight w 1 2
  have hsource : SupportedQuaternionBlocks N (polyMul W f) :=
    supported_polyMul (activeSpatialWeight_supported w 1 2) hf
  have h0 := original_transfer_haar_active w 1 2 hf hfr firstFace_supported
  have h1 := kineticMap_symmetric w 1 2 hsource firstFace_supported
  have h2 := firstFace_eigen w (polyMul W f) hsource
  have h3 := quaternionHaar_polyMul_smul_right N (qpow w 12) (polyMul W f) firstFaceTrace
  have hc : RatPolyCoeffEqv (polyMul (polyMul W f) firstFaceTrace)
      (polyMul (polyMul firstFaceTrace f) (cubeWeight w 1)) :=
    (RatPolyCoeffEqv.mul_comm (polyMul W f) firstFaceTrace).trans
      (((RatPolyCoeffEqv.mul_comm W f).mul_left firstFaceTrace).trans
        ((RatPolyCoeffEqv.mul_assoc firstFaceTrace f W).symm.trans
          ((activeSpatialWeight_cube w 1).mul_left (polyMul firstFaceTrace f))))
  exact Q'.eqv_trans _ _ _ h0 (Q'.eqv_trans _ _ _ h1
    (Q'.eqv_trans _ _ _ h2 (Q'.eqv_trans _ _ _ h3
      (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (blocks := N) hc)))))

/-- The actual ORIGINAL bent transfer, tested against the literal first face. -/
theorem tested_bent_transfer_pin (w : Q') :
    quaternionHaar N (polyMul firstFaceTrace (transferStep w 1 2 bentObservable)) ≈
      qpow w 12 * quaternionHaar N
        (polyMul (polyMul firstFaceTrace bentObservable) (cubeWeight w 1)) :=
  tested_transfer w bentObservable_supported (fun i hi =>
    bentObservable_cube_independent i (fringeBlocks_lt 2 i hi)
      (fun hc => ((fringeBlocks_mem_iff 2 i).mp hi).2 (cubeIndices_active i hc)))

/-- The actual ORIGINAL vacuum message T1, with no positivity guard. -/
theorem tested_vacuum_transfer_pin (w : Q') :
    quaternionHaar N (polyMul firstFaceTrace (transferStep w 1 2 polyOne)) ≈
      qpow w 12 * quaternionHaar N (polyMul firstFaceTrace (cubeWeight w 1)) :=
  Q'.eqv_trans _ _ _
    (tested_transfer w (supported_one N) (fun i _ => quaternionBlockIndependent_polyOne i))
    (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (blocks := N)
      ((RatPolyCoeffEqv.mul_one firstFaceTrace).mul_right (cubeWeight w 1))))

/-- Numerical tested TF channel; alpha is the original cutoff-one coefficient. -/
theorem tested_TF_channel (w : Q') :
    quaternionHaar N (polyMul firstFaceTrace (transferStep w 1 2 bentObservable)) ≈
      qpow w 12 * (coeffW w 1 * HalfPow.half +
        qpow (coeffW w 1) 5 * Q'.mkPos 1 8 (by decide)) :=
  Q'.eqv_trans _ _ _ (tested_bent_transfer_pin w)
    (Q'.mul_eqv_congr_left _ _ _ (tested_bent_action_channel w))

/-- Numerical tested T1 channel, on the same original carrier and action. -/
theorem tested_T1_channel (w : Q') :
    quaternionHaar N (polyMul firstFaceTrace (transferStep w 1 2 polyOne)) ≈
      qpow w 12 * (coeffW w 1 + qpow (coeffW w 1) 5 * Q'.mkPos 1 16 (by decide)) :=
  Q'.eqv_trans _ _ _ (tested_vacuum_transfer_pin w)
    (Q'.mul_eqv_congr_left _ _ _ (tested_vacuum_action_channel w))

/-- Any center is retained literally; no centered-eigenmode assertion is used. -/
theorem tested_centered_channel (w c : Q') :
    quaternionHaar N (polyMul firstFaceTrace
      (polyAdd (transferStep w 1 2 bentObservable)
        (polySmul (-c) (transferStep w 1 2 polyOne)))) ≈
      qpow w 12 * ((coeffW w 1 * HalfPow.half +
        qpow (coeffW w 1) 5 * Q'.mkPos 1 8 (by decide)) -
        c * (coeffW w 1 + qpow (coeffW w 1) 5 * Q'.mkPos 1 16 (by decide))) := by
  have h := Q'.eqv_trans _ _ _
    (quaternionHaar_polyMul_add_right N firstFaceTrace _ _)
    (Q'.add_eqv_congr' (tested_TF_channel w)
      (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right N (-c) firstFaceTrace _)
        (Q'.mul_eqv_congr_left _ _ _ (tested_T1_channel w))))
  exact Q'.eqv_trans _ _ _ h (poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.var 1)) (.mul (.neg (.var 3)) (.mul (.var 0) (.var 2))))
    (.mul (.var 0) (.add (.var 1) (.neg (.mul (.var 3) (.var 2))))) (by decide)
    (fun
      | 0 => qpow w 12
      | 1 => coeffW w 1 * HalfPow.half + qpow (coeffW w 1) 5 * Q'.mkPos 1 8 (by decide)
      | 2 => coeffW w 1 + qpow (coeffW w 1) 5 * Q'.mkPos 1 16 (by decide)
      | _ => c))

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTestedTransfer

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTestedTransfer.tested_bent_transfer_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTestedTransfer.tested_vacuum_transfer_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTestedTransfer.tested_TF_channel
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTestedTransfer.tested_T1_channel
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTestedTransfer.tested_centered_channel
