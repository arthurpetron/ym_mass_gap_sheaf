/-
# ORIGINAL interacting amplitudes with the local collar explicitly restored

Both tests are pinned to their positive spectator-background presentations.
The unit test inserts upper(e)*Cupper. The scalar test inserts
upper(e)*Supper*Cupper against the background that already contains Slower^2,
and retains the four original fundamental heat weights outside the integral.
No determinant estimate is assumed in these identities.
-/

import YMGap.Continuum.BF4ExactSlabBulkProbeLocalIntervals
import YMGap.Continuum.BF4ExactSlabBulkProbeScalarBackground
import YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval

namespace YMGap.Continuum.BF4ExactSlabBulkProbeCollarAmplitudePin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabBulkProbeInterface
open YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests
open YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization
open YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReference
open YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground
open YMGap.Continuum.BF4ExactSlabBulkProbeScalarBackground
open YMGap.Continuum.BF4ExactSlabBulkProbeLocalIntervals
open YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval
open YMGap.Continuum.BF4ExactSlabPartialInterfaceTests
open YMGap.Continuum.BF4ExactSlabPartialInterfaceHaarForm (reflected_coeff)
open YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels (channelWeightPower)
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabPolynomialReflectionInvariance
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

def upperCollarHeat (w : Q') (K half : Nat) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K (centralExtent half)) (reflectedCollarIds half)

theorem upperCollarHeat_supported (w : Q') (K half : Nat) :
    SupportedQuaternionBlocks (blocks half) (upperCollarHeat w K half) := heatProduct_supported w K _ _

private theorem reflected_product (w : Q') (K extent : Nat) : ∀ ids : List Nat,
    (∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) →
    ReflectionImage extent (polynomialProduct (faceHeatPolynomial w K extent) ids)
      (polynomialProduct (fun id => faceHeatPolynomial w K extent (slabFaceReflectId extent id)) ids)
  | [], _ => ReflectionImage.one extent
  | id :: ids, hi => (faceHeat_reflection w K (hi id List.mem_cons_self)).mul
      (reflected_product w K extent ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))

theorem upperCollarHeat_image (w : Q') (K half : Nat) :
    ReflectionImage (centralExtent half) (collarHeat w K half) (upperCollarHeat w K half) := by
  simpa only [collarHeat, upperCollarHeat, reflectedCollarIds, polynomialProduct, List.foldr_map] using
    (reflected_product w K (centralExtent half) (lowerCollar half) (fun _ hi => lowerCollar_physical hi))

private def env6 (a b c d e f : RatPoly) : Nat → RatPoly
  | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | _ => f

private theorem unit_reorder (u U L I : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul (polyMul u U) L) I) (polyMul (polyMul (polyMul U L) I) u) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
    (.mul (.mul (.mul (.var 1) (.var 2)) (.var 3)) (.var 0)) (by decide) (env6 u U L I polyZero polyZero)

private theorem scalar_reorder (u U L S R I : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul (polyMul u U) (polyMul S L)) (polyMul (polyMul R S) I))
      (polyMul (polyMul (polyMul (polyMul U L) I) (polyMul S S)) (polyMul u R)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 3) (.var 2))) (.mul (.mul (.var 4) (.var 3)) (.var 5)))
    (.mul (.mul (.mul (.mul (.var 1) (.var 2)) (.var 5)) (.mul (.var 3) (.var 3))) (.mul (.var 0) (.var 4)))
    (by decide) (env6 u U L S R I)

variable {w : Q'} (hw : (0 : Q') ≤ w)
include hw

/-- The reference's arbitrary local factor may already contain the original collar. -/
theorem unitReference_presentation (K half : Nat) (p u : RatPoly)
    (h : ReflectionImage (centralExtent half) p u) (hu : SupportedQuaternionBlocks (blocks half) u) :
    unitAmplitudeReference w K half p ≈ quaternionHaar (blocks half) (polyMul (positiveBackground w K half) u) := by
  have hL := spectatorHeat_supported w K half
  have hU := upperSpectatorHeat_supported w K half
  have hI := (spectatorExpansion hw K half).polynomialSupported
  have he := PaddedPolynomialCoeffEqv.mul
    (PaddedPolynomialCoeffEqv.mul (h.mul (upperSpectatorHeat_image w K half))
      (PaddedPolynomialCoeffEqv.refl (blocks half) (spectatorHeat w K half)))
    (PaddedPolynomialCoeffEqv.refl (blocks half) (spectatorInterface w K half))
  have hv := he.haar
    (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hL) hI)
    (supported_polyMul (supported_polyMul (supported_polyMul hu hU) hL) hI)
  exact Q'.eqv_trans _ _ _ (spectatorPair_coeff w K half (RatPolyCoeffEqv.refl _)
    (RatPolyCoeffEqv.one_mul (spectatorHeat w K half)))
    (Q'.eqv_trans _ _ _ hv (haar_of_coeff (unit_reorder _ _ _ _)))

theorem scalarReference_presentation (K half : Nat) (p u : RatPoly)
    (h : ReflectionImage (centralExtent half) p u) (hu : SupportedQuaternionBlocks (blocks half) u) :
    scalarAmplitudeReference w K half p ≈ channelWeightPower w 4 *
      quaternionHaar (blocks half) (polyMul (scalarBackground w K half) (polyMul u (upperScalar half))) := by
  have hL := spectatorHeat_supported w K half
  have hU := upperSpectatorHeat_supported w K half
  have hS := bulkScalar_supported half
  have hR := (upperScalarInterval half).support
  have hI := (spectatorExpansion hw K half).polynomialSupported
  have he := PaddedPolynomialCoeffEqv.mul
    (PaddedPolynomialCoeffEqv.mul (h.mul (upperSpectatorHeat_image w K half))
      (PaddedPolynomialCoeffEqv.refl (blocks half) (polyMul (bulkScalar half) (spectatorHeat w K half))))
    (PaddedPolynomialCoeffEqv.mul (PaddedPolynomialCoeffEqv.mul (upperScalar_image half)
      (PaddedPolynomialCoeffEqv.refl (blocks half) (bulkScalar half)))
      (PaddedPolynomialCoeffEqv.refl (blocks half) (spectatorInterface w K half)))
  have hv := he.haar
    (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) (supported_polyMul hS hL))
      (supported_polyMul (supported_polyMul (reflectCorrectedSlabPolynomial_support _ _) hS) hI))
    (supported_polyMul (supported_polyMul (supported_polyMul hu hU) (supported_polyMul hS hL))
      (supported_polyMul (supported_polyMul hR hS) hI))
  exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ hv (haar_of_coeff (scalar_reorder _ _ _ _ _ _)))

omit hw in
theorem dressedLower_collar (w : Q') (K : Nat) {half : Nat} (e : PlaquetteExpression half) :
    RatPolyCoeffEqv (dressedLower w K e)
      (polyMul (polyMul (lower e) (collarHeat w K half)) (spectatorHeat w K half)) :=
  ((RatPolyCoeffEqv.refl (lower e)).mul
    ((lowerObservable_one w K half).trans (lowerHeat_split w K half))).trans
    ((RatPolyCoeffEqv.mul_assoc (lower e) (collarHeat w K half) (spectatorHeat w K half)).symm)

omit hw in
theorem scalarPair_coeff (w : Q') (K half : Nat) {p p' q q' : RatPoly}
    (hp : RatPolyCoeffEqv p p') (hq : RatPolyCoeffEqv q q') :
    scalarSpectatorPair w K half p q ≈ scalarSpectatorPair w K half p' q' :=
  haar_of_coeff (((reflected_coeff _ hp).mul hq).mul_right _)

theorem unitAmplitude_collar_pin (K : Nat) (hK : 1 ≤ K) {half : Nat} (e : PlaquetteExpression half) :
    testAmplitude hw K hK half (localChoice half none) (spectatorHeat w K half) e ≈
      quaternionHaar (blocks half) (polyMul (positiveBackground w K half) (polyMul (upper e) (upperCollarHeat w K half))) := by
  have hc := spectatorPair_coeff w K half (dressedLower_collar w K e)
    (RatPolyCoeffEqv.one_mul (spectatorHeat w K half)).symm
  exact Q'.eqv_trans _ _ _ (unitAmplitude_pin hw K hK half e) (Q'.eqv_trans _ _ _ hc
    (unitReference_presentation hw K half _ _ ((lower_reflection e).mul (upperCollarHeat_image w K half))
      (supported_polyMul (upper_supported e) (upperCollarHeat_supported w K half))))

theorem scalarAmplitude_collar_pin (K : Nat) (hK : 1 ≤ K) {half : Nat} (e : PlaquetteExpression half) :
    testAmplitude hw K hK half (localChoice half (some (false,false))) (scalarTest w K half) e ≈
      channelWeightPower w 4 * quaternionHaar (blocks half)
        (polyMul (scalarBackground w K half) (polyMul (polyMul (upper e) (upperScalar half)) (upperCollarHeat w K half))) := by
  have hc := Q'.mul_eqv_congr_left (channelWeightPower w 4) _ _
    (scalarPair_coeff w K half (dressedLower_collar w K e) (RatPolyCoeffEqv.refl (scalarTest w K half)))
  have hr := scalarReference_presentation hw K half _ _
    ((lower_reflection e).mul (upperCollarHeat_image w K half))
    (supported_polyMul (upper_supported e) (upperCollarHeat_supported w K half))
  have hs : RatPolyCoeffEqv
      (polyMul (polyMul (upper e) (upperCollarHeat w K half)) (upperScalar half))
      (polyMul (polyMul (upper e) (upperScalar half)) (upperCollarHeat w K half)) :=
    (RatPolyCoeffEqv.mul_assoc _ _ _).trans (((RatPolyCoeffEqv.mul_comm _ _).mul_left _).trans
      (RatPolyCoeffEqv.mul_assoc _ _ _).symm)
  exact Q'.eqv_trans _ _ _ (scalarAmplitude_pin hw K hK half e) (Q'.eqv_trans _ _ _ hc
    (Q'.eqv_trans _ _ _ hr (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (hs.mul_left _)))))

end YMGap.Continuum.BF4ExactSlabBulkProbeCollarAmplitudePin

#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeCollarAmplitudePin.upperCollarHeat
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeCollarAmplitudePin.upperCollarHeat_supported
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeCollarAmplitudePin.upperCollarHeat_image
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeCollarAmplitudePin.unitReference_presentation
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeCollarAmplitudePin.scalarReference_presentation
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeCollarAmplitudePin.dressedLower_collar
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeCollarAmplitudePin.scalarPair_coeff
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeCollarAmplitudePin.unitAmplitude_collar_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeCollarAmplitudePin.scalarAmplitude_collar_pin
