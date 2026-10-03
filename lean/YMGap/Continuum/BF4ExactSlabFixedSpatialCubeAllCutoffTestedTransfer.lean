/-
# Original cube face projections at every cutoff containing the fundamental

The literal first-face test retains the EXACT kinetic factor w^12 for
every K>=1. Thus an action-prefix remainder is multiplied by w^12;
it is not an unweighted error on the transferred observable. The complete
original width-two action/carrier is retained through tested fringe removal.
The center is arbitrary and is never assigned a centered eigenvalue.

No remainder bound, positivity, OWN-mean estimate, gain sign, completed
response, or changing-family result is asserted in this module.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTestedTransfer

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffTestedTransfer

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

private theorem firstFace_eigen (w : Q') (K : Nat) (hK : 1 ≤ K) :
    SupportedHaarEqv N
      (SU2QuaternionProductHeatMarginals.productMap N w K
        (BF4ExactSlabFixedSpatialKineticMarginals.activeBlocks 2) firstFaceTrace)
      (polySmul (qpow w 12) firstFaceTrace) := by
  have hbase := (spatialFaces_mem_iff 1 ((0,0,0,0),.p01)).mpr (by decide)
  have hface := (spatialFaces_mem_iff 2 ((0,0,0,0),.p01)).mpr (by decide)
  exact plaquette_kinetic_eigen 2 ((0,0,0,0),.p01) hface
    (plaquette_active_after_padding (by decide : 1 < 2) _ hbase) w K hK

private theorem tested_transfer (w : Q') (K : Nat) (hK : 1 ≤ K) {f : RatPoly}
    (hf : SupportedQuaternionBlocks N f)
    (hfr : ∀ i, i ∈ fringeBlocks 2 → QuaternionBlockIndependent i f) :
    quaternionHaar N (polyMul firstFaceTrace (transferStep w K 2 f)) ≈
      qpow w 12 * quaternionHaar N (polyMul (polyMul firstFaceTrace f) (cubeWeight w K)) := by
  let W := activeSpatialWeight w K 2
  have hsource : SupportedQuaternionBlocks N (polyMul W f) :=
    supported_polyMul (activeSpatialWeight_supported w K 2) hf
  have h0 := original_transfer_haar_active w K 2 hf hfr firstFace_supported
  have h1 := kineticMap_symmetric w K 2 hsource firstFace_supported
  have h2 := firstFace_eigen w K hK (polyMul W f) hsource
  have h3 := quaternionHaar_polyMul_smul_right N (qpow w 12) (polyMul W f) firstFaceTrace
  have hc : RatPolyCoeffEqv (polyMul (polyMul W f) firstFaceTrace)
      (polyMul (polyMul firstFaceTrace f) (cubeWeight w K)) :=
    (RatPolyCoeffEqv.mul_comm (polyMul W f) firstFaceTrace).trans
      (((RatPolyCoeffEqv.mul_comm W f).mul_left firstFaceTrace).trans
        ((RatPolyCoeffEqv.mul_assoc firstFaceTrace f W).symm.trans
          ((activeSpatialWeight_cube w K).mul_left (polyMul firstFaceTrace f))))
  exact Q'.eqv_trans _ _ _ h0 (Q'.eqv_trans _ _ _ h1
    (Q'.eqv_trans _ _ _ h2 (Q'.eqv_trans _ _ _ h3
      (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (blocks := N) hc)))))

/-- Exact face-tested original TF, for every original K>=1. -/
theorem tested_bent_transfer_pin (w : Q') (K : Nat) (hK : 1 ≤ K) :
    quaternionHaar N (polyMul firstFaceTrace (transferStep w K 2 bentObservable)) ≈
      qpow w 12 * quaternionHaar N
        (polyMul (polyMul firstFaceTrace bentObservable) (cubeWeight w K)) :=
  tested_transfer w K hK bentObservable_supported (fun i hi =>
    bentObservable_cube_independent i (fringeBlocks_lt 2 i hi)
      (fun hc => ((fringeBlocks_mem_iff 2 i).mp hi).2 (cubeIndices_active i hc)))

/-- Exact face-tested original T1, preserving all K and the full action. -/
theorem tested_vacuum_transfer_pin (w : Q') (K : Nat) (hK : 1 ≤ K) :
    quaternionHaar N (polyMul firstFaceTrace (transferStep w K 2 polyOne)) ≈
      qpow w 12 * quaternionHaar N (polyMul firstFaceTrace (cubeWeight w K)) :=
  Q'.eqv_trans _ _ _
    (tested_transfer w K hK (supported_one N) (fun i _ => quaternionBlockIndependent_polyOne i))
    (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (blocks := N)
      ((RatPolyCoeffEqv.mul_one firstFaceTrace).mul_right (cubeWeight w K))))

/-- Any literal center, with the exact kinetic factor outside BOTH channels. -/
theorem tested_centered_channel (w : Q') (K : Nat) (hK : 1 ≤ K) (c : Q') :
    quaternionHaar N (polyMul firstFaceTrace
      (polyAdd (transferStep w K 2 bentObservable)
        (polySmul (-c) (transferStep w K 2 polyOne)))) ≈
      qpow w 12 * (quaternionHaar N
        (polyMul (polyMul firstFaceTrace bentObservable) (cubeWeight w K)) -
        c*quaternionHaar N (polyMul firstFaceTrace (cubeWeight w K))) := by
  have h := Q'.eqv_trans _ _ _
    (quaternionHaar_polyMul_add_right N firstFaceTrace _ _)
    (Q'.add_eqv_congr' (tested_bent_transfer_pin w K hK)
      (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right N (-c) firstFaceTrace _)
        (Q'.mul_eqv_congr_left _ _ _ (tested_vacuum_transfer_pin w K hK))))
  exact Q'.eqv_trans _ _ _ h (poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.var 1)) (.mul (.neg (.var 3)) (.mul (.var 0) (.var 2))))
    (.mul (.var 0) (.add (.var 1) (.neg (.mul (.var 3) (.var 2))))) (by decide)
    (fun
      | 0 => qpow w 12
      | 1 => quaternionHaar N (polyMul (polyMul firstFaceTrace bentObservable) (cubeWeight w K))
      | 2 => quaternionHaar N (polyMul firstFaceTrace (cubeWeight w K))
      | _ => c))

/-- The actual signed cube-action remainder, not an assumed error constant. -/
def testedActionRemainder (w : Q') (K : Nat) (c : Q') : Q' :=
  quaternionHaar N (polyMul
    (polyMul firstFaceTrace (polyAdd bentObservable (polySmul (-c) polyOne)))
    (polyAdd (cubeWeight w K) (polySmul (-1) (cubeWeight w 1))))

private theorem centered_action (w : Q') (K : Nat) (c : Q') :
    quaternionHaar N (polyMul
      (polyMul firstFaceTrace (polyAdd bentObservable (polySmul (-c) polyOne))) (cubeWeight w K)) ≈
      quaternionHaar N (polyMul (polyMul firstFaceTrace bentObservable) (cubeWeight w K)) -
        c*quaternionHaar N (polyMul firstFaceTrace (cubeWeight w K)) := by
  have hc := (RatPolyCoeffEqv.polyMul_smul_right (-c) firstFaceTrace polyOne).trans
    ((RatPolyCoeffEqv.mul_one firstFaceTrace).smul (-c))
  have hp : RatPolyCoeffEqv
      (polyMul (polyMul firstFaceTrace (polyAdd bentObservable (polySmul (-c) polyOne)))
        (cubeWeight w K))
      (polyAdd (polyMul (polyMul firstFaceTrace bentObservable) (cubeWeight w K))
        (polySmul (-c) (polyMul firstFaceTrace (cubeWeight w K)))) := by
    refine ((RatPolyCoeffEqv.mul_add_right firstFaceTrace bentObservable
      (polySmul (-c) polyOne)).mul_right (cubeWeight w K)).trans ?_
    rw [polyMul_add_left_exact]
    exact (RatPolyCoeffEqv.refl _).add ((hc.mul_right (cubeWeight w K)).trans
      (RatPolyCoeffEqv.polyMul_smul_left (-c) firstFaceTrace (cubeWeight w K)))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N) hp)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append N _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (quaternionHaar_polySmul N (-c) _))
        (poly_identity_of_normal_eq (.add (.var 0) (.mul (.neg (.var 1)) (.var 2)))
          (.add (.var 0) (.neg (.mul (.var 1) (.var 2)))) (by decide)
          (fun
            | 0 => quaternionHaar N (polyMul (polyMul firstFaceTrace bentObservable) (cubeWeight w K))
            | 1 => c
            | _ => quaternionHaar N (polyMul firstFaceTrace (cubeWeight w K))))))

/-- Exact numerical cutoff-one channel plus the literal all-cutoff action
remainder, multiplied by the SAME w^12. No absolute tail is asserted. -/
theorem tested_centered_cutoff_decomposition (w : Q') (K : Nat) (hK : 1 ≤ K) (c : Q') :
    quaternionHaar N (polyMul firstFaceTrace
      (polyAdd (transferStep w K 2 bentObservable)
        (polySmul (-c) (transferStep w K 2 polyOne)))) ≈
      qpow w 12 * (((coeffW w 1 * HalfPow.half +
        qpow (coeffW w 1) 5 * Q'.mkPos 1 8 (by decide)) -
        c*(coeffW w 1 + qpow (coeffW w 1) 5 * Q'.mkPos 1 16 (by decide))) +
        testedActionRemainder w K c) := by
  let x := quaternionHaar N (polyMul (polyMul firstFaceTrace bentObservable) (cubeWeight w K)) -
    c*quaternionHaar N (polyMul firstFaceTrace (cubeWeight w K))
  let base := (coeffW w 1 * HalfPow.half + qpow (coeffW w 1) 5 * Q'.mkPos 1 8 (by decide)) -
    c*(coeffW w 1 + qpow (coeffW w 1) 5 * Q'.mkPos 1 16 (by decide))
  have hb : quaternionHaar N (polyMul
      (polyMul firstFaceTrace (polyAdd bentObservable (polySmul (-c) polyOne)))
      (cubeWeight w 1)) ≈ base :=
    Q'.eqv_trans _ _ _ (centered_action w 1 c)
      (Q'.add_eqv_congr' (tested_bent_action_channel w)
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left c _ _ (tested_vacuum_action_channel w))))
  have hr : testedActionRemainder w K c ≈ x-base :=
    Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right N _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (centered_action w K c)
        (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right N (-1) _ _)
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (-1) _ _ hb)
            (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
              (by decide) (fun _ => base))))) (Q'.eqv_refl _))
  have hx : x ≈ base+testedActionRemainder w K c :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq (.var 0)
        (.add (.var 1) (.add (.var 0) (.neg (.var 1)))) (by decide)
        (fun
          | 0 => x
          | _ => base))
      (Q'.add_eqv_congr' (Q'.eqv_refl base) (Q'.eqv_symm hr))
  exact Q'.eqv_trans _ _ _ (tested_centered_channel w K hK c)
    (Q'.mul_eqv_congr_left (qpow w 12) _ _ hx)

#print axioms tested_bent_transfer_pin
#print axioms tested_vacuum_transfer_pin
#print axioms tested_centered_channel
#print axioms testedActionRemainder
#print axioms tested_centered_cutoff_decomposition

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffTestedTransfer
