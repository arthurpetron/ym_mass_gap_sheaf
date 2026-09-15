/-
# The ORIGINAL crossing profile equals its same-channel Gram form

Every physical crossing face may have its own nome and finite cutoff.
The old temporal ledger transports the full original expression and all
crossing factors together. Original plaquette observables, including any
bulk heat product encoded in that algebra, retain their original images.
The resulting Haar form is the previous profileForm, on the SAME lower p.

This finite identity licenses the existing per-face weight comparison.
It does not provide cutoff/volume-uniform OS coercivity, transfer range,
time-zero continuity, a physical Hamiltonian or continuum/Clay closure.
-/

import YMGap.Continuum.BF4ExactSlabProfileInterfaceComparison
import YMGap.Continuum.BF4ExactSlabLocalBulkSelection
import YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity

namespace YMGap.Continuum.BF4ExactSlabProfileOriginalInterface

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalImages
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces
open YMGap.Continuum.BF4ExactSlabTemporalGaugeHaarForm
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity (reflectedInsertion)
open YMGap.Continuum.BF4ExactSlabProfileInterfaceComparison
open YMGap.Continuum.BF4ExactSlabLocalBulkSelection (profileHeat profileHeat_supported)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

def temporalProfile (w : Nat → Q') (cutoff : Nat → Nat) (half : Nat) : RatPoly :=
  polynomialProduct (fun id => temporalFaceHeatPolynomial (w id) (cutoff id) half id) (centralFixedFaceIds half)

private theorem image_product (w : Nat → Q') (cutoff : Nat → Nat) (half : Nat) :
    ∀ ids : List Nat, (∀ id,id ∈ ids → id ∈ slabPhysicalFaceEdges (centralExtent half)) →
      TemporalImage half (profileHeat w cutoff (centralExtent half) ids)
        (polynomialProduct (fun id => temporalFaceHeatPolynomial (w id) (cutoff id) half id) ids)
  | [], _ => TemporalImage.one half
  | id::ids, h => TemporalImage.mul (faceHeat_image (w id) (cutoff id) half (h id List.mem_cons_self))
      (image_product w cutoff half ids (fun j hj => h j (List.mem_cons_of_mem id hj)))

theorem profile_image (w : Nat → Q') (cutoff : Nat → Nat) (half : Nat) :
    TemporalImage half (profileHeat w cutoff (centralExtent half) (centralFixedFaceIds half))
      (temporalProfile w cutoff half) :=
  image_product w cutoff half _ (fun _ hi => (mem_centralFixedFaceIds.mp hi).1)

private theorem sum_support {A : Type} {count : Nat} (f : A → RatPoly)
    (h : ∀ a,SupportedQuaternionBlocks count (f a)) :
    ∀ xs : List A, SupportedQuaternionBlocks count (finitePolySum f xs)
  | [] => fun _ ht => False.elim (List.not_mem_nil ht)
  | a::xs => supported_add (h a) (sum_support f h xs)

private theorem product_support {A : Type} {count : Nat} (f : A → RatPoly)
    (h : ∀ a,SupportedQuaternionBlocks count (f a)) :
    ∀ xs : List A, SupportedQuaternionBlocks count (polynomialProduct f xs)
  | [] => supported_one _
  | a::xs => supported_polyMul (h a) (product_support f h xs)

theorem temporalProfile_supported (w : Nat → Q') (cutoff : Nat → Nat) (half : Nat) :
    SupportedQuaternionBlocks (blocks half) (temporalProfile w cutoff half) :=
  product_support _ (fun _ => sum_support _
    (fun spin => supported_smul (temporal_character_support _ _ _ spin) _) _) _

private theorem sum_row {A : Type} {count : Nat} (f g : A → RatPoly) :
    ∀ xs : List A, (∀ a,a ∈ xs → HaarCarrierEqv count (f a) (g a)) →
      HaarCarrierEqv count (finitePolySum f xs) (finitePolySum g xs)
  | [], _ => HaarCarrierEqv.refl _ _
  | a::xs, h => HaarCarrierEqv.add (h a List.mem_cons_self)
      (sum_row f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem product_row {A : Type} {count : Nat} (f g : A → RatPoly) :
    ∀ xs : List A, (∀ a,a ∈ xs → HaarCarrierEqv count (f a) (g a)) →
      HaarCarrierEqv count (polynomialProduct f xs) (polynomialProduct g xs)
  | [], _ => HaarCarrierEqv.refl _ _
  | a::xs, h => HaarCarrierEqv.mul (h a List.mem_cons_self)
      (product_row f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

theorem temporalProfile_gram (w : Nat → Q') (cutoff : Nat → Nat) (half : Nat) :
    HaarCarrierEqv (blocks half) (temporalProfile w cutoff half) (profilePolynomial w cutoff half) := by
  apply product_row
  intro id hi
  apply sum_row
  intro spin _
  exact HaarCarrierEqv.smul _ ((crossing_face_reflected_gram half _ (mem_centralFixedFaceIds.mp hi).2 spin).1)

/-- Both original observable factors and every crossing heat factor are transported. -/
theorem upper_gram (w : Nat → Q') (cutoff : Nat → Nat) {half : Nat} (e : PlaquetteExpression half) :
    quaternionHaar (blocks half) (polyMul (polyMul (upper e) (lower e))
      (profileHeat w cutoff (centralExtent half) (centralFixedFaceIds half))) ≈
    quaternionHaar (blocks half) (polyMul (polyMul (upper e) (lower e)) (profilePolynomial w cutoff half)) := by
  have hi := ((upper_image e).mul (lower_image e)).mul (profile_image w cutoff half)
  have hs := supported_polyMul (supported_polyMul (upper_supported e) (lower_supported e))
    (profileHeat_supported w cutoff (centralExtent half) (centralFixedFaceIds half))
  have ht := supported_polyMul (supported_polyMul (temporalUpper_supported e) (temporalLower_supported e))
    (temporalProfile_supported w cutoff half)
  have h := Q'.eqv_trans _ _ _ (Q'.eqv_symm (applyTemporalTranslationLedger_haar _ _ _ hs))
    (hi.haar (applyTemporalTranslationLedger_supported _ _ _ hs) ht)
  exact Q'.eqv_trans _ _ _ h (QuaternionHaarSquareCertificate.haar_of_carrier
    (HaarCarrierEqv.mul (HaarCarrierEqv.mul (temporalUpper_original e) (temporalLower_original e))
      (temporalProfile_gram w cutoff half)))

def originalForm (w : Nat → Q') (cutoff : Nat → Nat) {half : Nat} (e : PlaquetteExpression half) : Q' :=
  quaternionHaar (blocks half) (polyMul (reflectedInsertion e)
    (profileHeat w cutoff (centralExtent half) (centralFixedFaceIds half)))

theorem originalForm_pin (w : Nat → Q') (hw : ∀ id,(0 : Q') ≤ w id)
    (cutoff : Nat → Nat) {half : Nat} (e : PlaquetteExpression half) :
    originalForm w cutoff e ≈ profileForm w cutoff half (lower e) := by
  let R := PaddedPolynomialCoeffEqv.mul (lower_reflection e) (PaddedPolynomialCoeffEqv.refl (blocks half) (lower e))
  have hs := supported_polyMul (reflectCorrectedSlabPolynomial_support (centralExtent half) (lower e)) (lower_supported e)
  have ht := supported_polyMul (upper_supported e) (lower_supported e)
  have hI := profileHeat_supported w cutoff (centralExtent half) (centralFixedFaceIds half)
  have hG := (profileExpansion w hw cutoff half).polynomialSupported
  have hleft := (R.mul (PaddedPolynomialCoeffEqv.refl _ _)).haar (supported_polyMul hs hI) (supported_polyMul ht hI)
  have hright := (R.mul (PaddedPolynomialCoeffEqv.refl _ _)).haar (supported_polyMul hs hG) (supported_polyMul ht hG)
  exact Q'.eqv_trans _ _ _ hleft (Q'.eqv_trans _ _ _ (upper_gram w cutoff e) (Q'.eqv_symm hright))

theorem originalForm_nonnegative (w : Nat → Q') (hw : ∀ id,(0 : Q') ≤ w id)
    (cutoff : Nat → Nat) {half : Nat} (e : PlaquetteExpression half) : (0 : Q') ≤ originalForm w cutoff e :=
  Q'.le_trans' _ _ _ (profileForm_nonnegative w hw cutoff half (lower e) (lower_supported e) (lower_local e))
    (Q'.ge_of_eqv (originalForm_pin w hw cutoff e))

/-- The previous per-face comparison now concerns ORIGINAL crossing plaquettes. -/
theorem originalForm_comparison (a b c : Nat → Q') (ha : ∀ id,(0 : Q') ≤ a id)
    (hb : ∀ id,(0 : Q') ≤ b id) (hc : ∀ id,(0 : Q') ≤ c id)
    (cutoff : Nat → Nat) {half : Nat} (e : PlaquetteExpression half)
    (hcoeff : ∀ id,id ∈ centralFixedFaceIds half → ∀ s,s ≤ cutoff id → c id * coeffW (a id) s ≤ coeffW (b id) s) :
    factorProduct c (centralFixedFaceIds half) * originalForm a cutoff e ≤ originalForm b cutoff e :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (originalForm_pin a ha cutoff e)))
    (Q'.le_trans' _ _ _ (profile_form_comparison a b c ha hb hc cutoff half (lower e)
      (lower_supported e) (lower_local e) hcoeff) (Q'.ge_of_eqv (originalForm_pin b hb cutoff e)))

end YMGap.Continuum.BF4ExactSlabProfileOriginalInterface

#print axioms YMGap.Continuum.BF4ExactSlabProfileOriginalInterface.temporalProfile
#print axioms YMGap.Continuum.BF4ExactSlabProfileOriginalInterface.profile_image
#print axioms YMGap.Continuum.BF4ExactSlabProfileOriginalInterface.temporalProfile_supported
#print axioms YMGap.Continuum.BF4ExactSlabProfileOriginalInterface.temporalProfile_gram
#print axioms YMGap.Continuum.BF4ExactSlabProfileOriginalInterface.upper_gram
#print axioms YMGap.Continuum.BF4ExactSlabProfileOriginalInterface.originalForm
#print axioms YMGap.Continuum.BF4ExactSlabProfileOriginalInterface.originalForm_pin
#print axioms YMGap.Continuum.BF4ExactSlabProfileOriginalInterface.originalForm_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabProfileOriginalInterface.originalForm_comparison
