/-
# Actual original centered-message square floor from the tested face channel

For arbitrary c, b is literally TF-c*T1 at original width two and cutoff one.
The original spatial insertion is retained until its tested cube transport is
paid. A half-floor for the actual cube action and the original first-face norm
then bound the original weighted square by half the tested projection squared.
No OWN mean, positivity of the transfer kernel, head cutoff, or gain sign is
assumed or inferred here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTestedTransfer
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeFundamentalInterval
import YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder
import YMGap.Continuum.SU2QuaternionHaarCertificateReindex
import YMGap.Continuum.SU2QuaternionAngularSupport
import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredSquareProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow
  (fringeBlocks_mem_iff fringeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSpatialWeight (spatialWeight_haar_active)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentFusion (firstFaceTrace)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentComplement (first_face_square_haar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeFundamentalInterval
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTestedTransfer (tested_centered_channel)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported)
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex (carrier_of_supported)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder (haar_order)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.RingNormaliser (qpow)

local notation "N" => List.length (baseLinks 2)
local notation "half" => HalfPow.half
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks transferStep cubeWeight cubeTransfer

/-- Arbitrary-center actual ORIGINAL message; c is never replaced by an eigenpin. -/
def centeredBentMessage (w c : Q') : RatPoly :=
  polyAdd (transferStep w 1 2 bentObservable) (polySmul (-c) (transferStep w 1 2 polyOne))

private def cubeMessage (w c : Q') : RatPoly :=
  polyAdd (cubeTransfer w 1 bentObservable) (polySmul (-c) (cubeTransfer w 1 polyOne))

private theorem original_supported (w c : Q') : SupportedQuaternionBlocks N (centeredBentMessage w c) :=
  supported_add (transferStep_supported w 1 2 bentObservable_supported)
    (polySmul_supported (transferStep_supported w 1 2 (supported_one N)) (-c))

private theorem cube_supported (w c : Q') : SupportedQuaternionBlocks N (cubeMessage w c) :=
  supported_add (cubeTransfer_supported w 1 bentObservable_supported)
    (polySmul_supported (cubeTransfer_supported w 1 (supported_one N)) (-c))

private theorem message_pin (w c : Q') :
    SupportedHaarEqv N (centeredBentMessage w c) (cubeMessage w c) :=
  (original_bent_message_cube w 1).add ((original_vacuum_message_cube w 1).smul (-c))

private theorem square_pin (w c : Q') :
    SupportedHaarEqv N (polyMul (centeredBentMessage w c) (centeredBentMessage w c))
      (polyMul (cubeMessage w c) (cubeMessage w c)) :=
  (message_pin w c).mul (message_pin w c) (original_supported w c) (cube_supported w c)

private theorem cube_independent (w c : Q') (i : Nat) (hi : i < N) (hn : i ∉ cubeIndices) :
    QuaternionBlockIndependent i (cubeMessage w c) :=
  quaternionBlockIndependent_polyAdd
    (cubeTransfer_independent w 1 i hi hn bentObservable_supported)
    (quaternionBlockIndependent_polySmul (-c)
      (cubeTransfer_independent w 1 i hi hn (supported_one N)))

/-- Paid ORIGINAL weighted-square source equality, before a cube floor is used. -/
theorem centered_square_cube_pin (w c : Q') :
    weightedMass w 1 2 (polyMul (centeredBentMessage w c) (centeredBentMessage w c)) ≈
      quaternionHaar N (polyMul (cubeWeight w 1) (polyMul (cubeMessage w c) (cubeMessage w c))) := by
  have h0 := square_pin w c (spatialWeight w 1 2) (spatialWeight_supported w 1 2)
  have hs := supported_polyMul (cube_supported w c) (cube_supported w c)
  have h1 := spatialWeight_haar_active w 1 2 _ hs (fun i hi => by
    have hn : i ∉ cubeIndices :=
      fun hc => ((fringeBlocks_mem_iff 2 i).mp hi).2 (cubeIndices_active i hc)
    have hind := cube_independent w c i (fringeBlocks_lt 2 i hi) hn
    exact quaternionBlockIndependent_polyMul hind hind)
  exact Q'.eqv_trans _ _ _ h0 (Q'.eqv_trans _ _ _ h1
    (haar_of_coeff (blocks := N) ((activeSpatialWeight_cube w 1).mul_right _)))

private theorem raw_square_pin (w c : Q') :
    quaternionHaar N (polyMul (centeredBentMessage w c) (centeredBentMessage w c)) ≈
      quaternionHaar N (polyMul (cubeMessage w c) (cubeMessage w c)) :=
  haar_of_carrier (carrier_of_supported
    (supported_polyMul (original_supported w c) (original_supported w c))
    (supported_polyMul (cube_supported w c) (cube_supported w c)) (square_pin w c))

private theorem projection_square_le_raw (w c : Q') :
    quaternionHaar N (polyMul firstFaceTrace (centeredBentMessage w c)) *
      quaternionHaar N (polyMul firstFaceTrace (centeredBentMessage w c)) ≤
      quaternionHaar N (polyMul (centeredBentMessage w c) (centeredBentMessage w c)) := by
  have hp : SupportedQuaternionBlocks N firstFaceTrace :=
    character_supported (plaquette_supported 2 N (Nat.le_refl _) ((0,0,0,0),.p01)).scalar 1
  have h := weighted_cauchySchwarz N polyOne firstFaceTrace (centeredBentMessage w c)
    (Certificate.one N) hp (original_supported w c)
  have hx : weightedPair N polyOne firstFaceTrace (centeredBentMessage w c) ≈
      quaternionHaar N (polyMul firstFaceTrace (centeredBentMessage w c)) :=
    haar_of_coeff (blocks := N) (RatPolyCoeffEqv.mul_one _)
  have hy : weightedPair N polyOne firstFaceTrace firstFaceTrace ≈ 1 :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N) (RatPolyCoeffEqv.mul_one _)) first_face_square_haar
  have hz : weightedPair N polyOne (centeredBentMessage w c) (centeredBentMessage w c) ≈
      quaternionHaar N (polyMul (centeredBentMessage w c) (centeredBentMessage w c)) :=
    haar_of_coeff (blocks := N) (RatPolyCoeffEqv.mul_one _)
  have hl := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hx)
    (Q'.mul_eqv_congr_left _ _ _ hx)
  have hr := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hy)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl) (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hr))

/-- Actual original C2, bounded below by the literal tested face projection. -/
theorem centeredSquare_projection_lower (w c : Q') (ha : (0 : Q') ≤ coeffW w 1)
    (hdelta : cubeFundamentalDelta w ≤ half) :
    half * (quaternionHaar N (polyMul firstFaceTrace (centeredBentMessage w c)) *
      quaternionHaar N (polyMul firstFaceTrace (centeredBentMessage w c))) ≤
      weightedMass w 1 2 (polyMul (centeredBentMessage w c) (centeredBentMessage w c)) := by
  have hraw := Q'.mul_le_mul_of_nonneg_left _ _ half (projection_square_le_raw w c)
    HalfPow.half_nonneg
  have hfloor := haar_order (cubeFundamentalHalfCertificate w ha hdelta)
    (Certificate.square (cubeMessage w c) (cube_supported w c))
  have hcap : quaternionHaar N (polyMul (cap half) (polyMul (cubeMessage w c) (cubeMessage w c))) ≈
      half * quaternionHaar N (polyMul (cubeMessage w c) (cubeMessage w c)) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N) (cap_mul_left half _))
      (quaternionHaar_polySmul N half _)
  exact Q'.le_trans' _ _ _ hraw
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (raw_square_pin w c)))
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcap)
        (Q'.le_trans' _ _ _ hfloor (Q'.ge_of_eqv (centered_square_cube_pin w c)))))

/-- The original computed channel supplies the floor without an assumed projection pin. -/
theorem centeredSquare_channel_lower (w c : Q') (ha : (0 : Q') ≤ coeffW w 1)
    (hdelta : cubeFundamentalDelta w ≤ half) :
    let d := qpow w 12 * ((coeffW w 1 * half + qpow (coeffW w 1) 5 * Q'.mkPos 1 8 (by decide)) -
      c * (coeffW w 1 + qpow (coeffW w 1) 5 * Q'.mkPos 1 16 (by decide)))
    half * (d*d) ≤ weightedMass w 1 2
      (polyMul (centeredBentMessage w c) (centeredBentMessage w c)) := by
  dsimp only
  have hd := tested_centered_channel w c
  have hdd := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hd)
    (Q'.mul_eqv_congr_left _ _ _ hd)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_eqv_congr_left half _ _ hdd))
    (centeredSquare_projection_lower w c ha hdelta)

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredSquareProjection

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredSquareProjection.centeredBentMessage
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredSquareProjection.centered_square_cube_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredSquareProjection.centeredSquare_projection_lower
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredSquareProjection.centeredSquare_channel_lower
