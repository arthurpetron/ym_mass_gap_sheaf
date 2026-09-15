/-
# Independent crossing cutoff, with the ORIGINAL bulk dressing retained

The bulk nome/cutoff b,B and crossing nome/cutoff v,K are independent.
The same temporal change of variables identifies the ORIGINAL crossing
pairing against the fixed bulk-dressed insertion with the spatial Gram
interface form. Setting b=v and B=K recovers the original full-action
reflected numerator. No change of observable or independent-link law.

This finite pin licenses fixed-insertion interface selection. It does not
control growing bulk cutoffs, thermodynamic limits or completed transfer
injectivity, and does not close the continuum/Clay frontier.
-/

import YMGap.Continuum.BF4ExactSlabOriginalInterfaceCoercivity
import YMGap.Continuum.BF4ExactSlabAllExtentInterfaceCutoffLimit

namespace YMGap.Continuum.BF4ExactSlabMixedInterfacePin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalImages
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabAllExtentInterfaceCutoffLimit
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabOriginalInterfaceCoercivity
open YMGap.Continuum.BF4ExactSlabFiniteInterfaceCoercivity
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private theorem sum_supported {A : Type} {blocks : Nat} (f : A → RatPoly)
    (h : ∀ a, SupportedQuaternionBlocks blocks (f a)) :
    ∀ xs : List A, SupportedQuaternionBlocks blocks (finitePolySum f xs)
  | [] => fun _ ht => False.elim (List.not_mem_nil ht)
  | a :: xs => supported_add (h a) (sum_supported f h xs)

private theorem product_supported {A : Type} {blocks : Nat} (f : A → RatPoly)
    (h : ∀ a, SupportedQuaternionBlocks blocks (f a)) :
    ∀ xs : List A, SupportedQuaternionBlocks blocks (polynomialProduct f xs)
  | [] => supported_one blocks
  | a :: xs => supported_polyMul (h a) (product_supported f h xs)

private theorem temporal_lower_supported (b : Q') (B half : Nat) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length
      (temporalLowerObservable b B half (fun _ => 1)) :=
  sum_supported _ (fun _ => supported_smul (product_supported _
    (fun _ => supported_smul (temporal_character_support _ _ _ _) _) _) _) _

private theorem temporal_upper_supported (b : Q') (B half : Nat) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length
      (temporalUpperObservable b B half (fun _ => 1)) :=
  sum_supported _ (fun _ => supported_smul (product_supported _
    (fun _ => supported_smul (temporal_character_support _ _ _ _) _) _) _) _

private theorem temporal_interface_supported (v : Q') (K half : Nat) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length
      (temporalInterfacePolynomial v K half) :=
  product_supported _ (fun _ => sum_supported _
    (fun _ => supported_smul (temporal_character_support _ _ _ _) _) _) _

private theorem haar_temporal {half : Nat} {p q : RatPoly} (h : TemporalImage half p q)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length q) :
    quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length p ≈
      quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length q :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (applyTemporalTranslationLedger_haar _ _ _ hp))
    (PaddedPolynomialCoeffEqv.haar h (applyTemporalTranslationLedger_supported _ _ _ hp) hq)

variable (b v : Q') (B K : Nat) {half : Nat} (e : PlaquetteExpression half)

local notation "blocks" => List.length (boundaryCompleteSlabLinks (centralExtent half))
local notation "p" => dressedLower b B e
local notation "u" => dressedUpper b B e
local notation "I" => interfaceHeatProduct v K half
local notation "G" => interfacePolynomial v K half
local notation "tp" => polyMul (temporalLower e) (temporalLowerObservable b B half (fun _ => 1))
local notation "tu" => polyMul (temporalUpper e) (temporalUpperObservable b B half (fun _ => 1))
local notation "tI" => temporalInterfacePolynomial v K half

/-- This insertion is independent of the crossing nome and cutoff. -/
def mixedInsertion : RatPoly := polyMul p u

theorem mixedInsertion_supported : SupportedQuaternionBlocks blocks (mixedInsertion b B e) :=
  supported_polyMul (dressedLower_supported b B e) (dressedUpper_supported b B e)

/-- ORIGINAL crossing plaquettes, not the already-transformed Gram interface. -/
def mixedQuadratic : Q' := interfacePairing v K half (mixedInsertion b B e)

theorem mixed_product_pin :
    mixedQuadratic b v B K e ≈ quaternionHaar blocks (polyMul p (polyMul I u)) :=
  haar_of_coeff_eqv blocks
    (((interfaceHeatInsertion_eq_product v K half).mul_left _).trans
      ((RatPolyCoeffEqv.mul_assoc p u I).trans ((RatPolyCoeffEqv.mul_comm u I).mul_left p)))

/-- The same temporal ledger with separately specified bulk and crossing data. -/
theorem mixed_spatialGram_pin :
    mixedQuadratic b v B K e ≈ quaternionHaar blocks (polyMul p (polyMul G u)) := by
  have hp : TemporalImage half p tp :=
    (lower_image e).mul (lowerObservable_image b B half (fun _ => 1))
  have hu : TemporalImage half u tu :=
    (upper_image e).mul (upperObservable_image b B half (fun _ => 1))
  have hi : TemporalImage half I tI := interfaceHeatProduct_image v K half
  have ht := haar_temporal (hp.mul (hi.mul hu))
    (supported_polyMul (dressedLower_supported b B e)
      (supported_polyMul (interfaceHeatProduct_support v K half) (dressedUpper_supported b B e)))
    (supported_polyMul (supported_polyMul (temporalLower_supported e) (temporal_lower_supported b B half))
      (supported_polyMul (temporal_interface_supported v K half)
        (supported_polyMul (temporalUpper_supported e) (temporal_upper_supported b B half))))
  have hg : HaarCarrierEqv blocks (polyMul tp (polyMul tI tu)) (polyMul p (polyMul G u)) :=
    HaarCarrierEqv.mul
      (HaarCarrierEqv.mul (temporalLower_original e) (temporalLower_haar_original b B half (fun _ => 1)))
      (HaarCarrierEqv.mul (temporalInterface_haar_gram v K half)
        (HaarCarrierEqv.mul (temporalUpper_original e) (temporalUpper_haar_original b B half (fun _ => 1))))
  exact Q'.eqv_trans _ _ _ (mixed_product_pin b v B K e)
    (Q'.eqv_trans _ _ _ ht (QuaternionHaarSquareCertificate.haar_of_carrier hg))

/-- The actual original mixed-cutoff form equals Q_v of the SAME dressed lower polynomial. -/
theorem mixed_interface_pin (hv : (0 : Q') ≤ v) :
    mixedQuadratic b v B K e ≈ interfaceForm v K half p := by
  have hG := (interfaceExpansion hv K half).polynomialSupported
  have hd := dressedLower_supported b B e
  have ht := reflectCorrectedSlabPolynomial_support (centralExtent half) p
  have hr := ((PaddedPolynomialCoeffEqv.refl blocks p).mul
    ((PaddedPolynomialCoeffEqv.refl blocks G).mul (dressed_reflection b B e))).haar
      (supported_polyMul hd (supported_polyMul hG ht))
      (supported_polyMul hd (supported_polyMul hG (dressedUpper_supported b B e)))
  have horder : RatPolyCoeffEqv
      (polyMul p (polyMul G (reflectCorrectedSlabPolynomial (centralExtent half) p)))
      (reflectedInterfacePolynomial v K half p) :=
    ((RatPolyCoeffEqv.mul_comm _ _).mul_left _).trans
      ((RatPolyCoeffEqv.mul_assoc _ _ _).symm.trans ((RatPolyCoeffEqv.mul_comm _ _).mul_right _))
  exact Q'.eqv_trans _ _ _ (mixed_spatialGram_pin b v B K e)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hr) (haar_of_coeff_eqv blocks horder))

/-- On the diagonal, this is the pre-existing ORIGINAL complete action. -/
theorem mixed_original_diagonal (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    {half : Nat} (e : PlaquetteExpression half) :
    mixedQuadratic w w K K e ≈ originalQuadratic w K e :=
  Q'.eqv_trans _ _ _ (mixed_interface_pin w w K K e hw)
    (Q'.eqv_symm (original_interface_pin w hw K e))

end YMGap.Continuum.BF4ExactSlabMixedInterfacePin

#print axioms YMGap.Continuum.BF4ExactSlabMixedInterfacePin.mixedInsertion
#print axioms YMGap.Continuum.BF4ExactSlabMixedInterfacePin.mixedInsertion_supported
#print axioms YMGap.Continuum.BF4ExactSlabMixedInterfacePin.mixedQuadratic
#print axioms YMGap.Continuum.BF4ExactSlabMixedInterfacePin.mixed_product_pin
#print axioms YMGap.Continuum.BF4ExactSlabMixedInterfacePin.mixed_spatialGram_pin
#print axioms YMGap.Continuum.BF4ExactSlabMixedInterfacePin.mixed_interface_pin
#print axioms YMGap.Continuum.BF4ExactSlabMixedInterfacePin.mixed_original_diagonal
