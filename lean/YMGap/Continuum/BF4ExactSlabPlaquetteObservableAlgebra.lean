/-
# A concrete lower-half plaquette observable algebra

Expressions are finite sums, products and rational multiples of actual
lower-half SU(2) plaquette characters. The original and temporal-gauge
evaluations are independently defined on the same link coordinates.
Support, lower locality, literal reflection and the temporal Haar pins
are proved structurally, at every odd slab extent and every character degree.

This is the plaquette-generated algebra, not a claim that all Wilson loops
or all positive-time gauge observables have been represented.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentReflectionPositivity
import YMGap.Continuum.QuaternionHaarSquareCertificate

namespace YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentPlaquetteReflection
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.BF4ExactSlabTemporalGaugeObservableImages
open YMGap.Continuum.BF4ExactSlabLowerHaarFactorization
open YMGap.Continuum.BF4ExactSlabLowerChannelLocality
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

inductive PlaquetteExpression (half : Nat) : Type where
  | unit : PlaquetteExpression half
  | character (id : Nat) (physical : id ∈ centralLowerFaceIds half) (spin : Nat) : PlaquetteExpression half
  | add : PlaquetteExpression half → PlaquetteExpression half → PlaquetteExpression half
  | mul : PlaquetteExpression half → PlaquetteExpression half → PlaquetteExpression half
  | smul : Q' → PlaquetteExpression half → PlaquetteExpression half

def evaluate {half : Nat} (f : Nat → Nat → RatPoly) : PlaquetteExpression half → RatPoly
  | .unit => polyOne
  | .character id _ spin => f id spin
  | .add p q => polyAdd (evaluate f p) (evaluate f q)
  | .mul p q => polyMul (evaluate f p) (evaluate f q)
  | .smul c p => polySmul c (evaluate f p)

def lower {half : Nat} : PlaquetteExpression half → RatPoly :=
  evaluate (fun id spin => characterPolynomial
    (correctedSlabPlaquettePolynomial (centralExtent half) (slabPlaquetteAt (centralExtent half) id)).scalar spin)

def upper {half : Nat} : PlaquetteExpression half → RatPoly :=
  evaluate (fun id spin => characterPolynomial (correctedSlabPlaquettePolynomial (centralExtent half)
    (slabPlaquetteAt (centralExtent half) (slabFaceReflectId (centralExtent half) id))).scalar spin)

def temporalLower {half : Nat} : PlaquetteExpression half → RatPoly :=
  evaluate (fun id spin => temporalCharacter (centralExtent half) half (slabPlaquetteAt (centralExtent half) id) spin)

def temporalUpper {half : Nat} : PlaquetteExpression half → RatPoly :=
  evaluate (fun id spin => temporalCharacter (centralExtent half) half
    (slabPlaquetteAt (centralExtent half) (slabFaceReflectId (centralExtent half) id)) spin)

theorem upper_id {half id : Nat} (hi : id ∈ centralLowerFaceIds half) :
    slabFaceReflectId (centralExtent half) id ∈ centralUpperFaceIds half := by
  refine mem_centralUpperFaceIds.mpr ⟨slabFaceReflectId_physical (mem_centralLowerFaceIds.mp hi).1, ?_⟩
  rw [slabFaceReflectId_side (mem_centralLowerFaceIds.mp hi).1, (mem_centralLowerFaceIds.mp hi).2]
  rfl

theorem supported_smul {blocks : Nat} {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem evaluate_supported {half blocks : Nat} (f : Nat → Nat → RatPoly)
    (hf : ∀ id, id ∈ centralLowerFaceIds half → ∀ spin, SupportedQuaternionBlocks blocks (f id spin)) :
    ∀ e : PlaquetteExpression half, SupportedQuaternionBlocks blocks (evaluate f e)
  | .unit => supported_one blocks
  | .character id hi spin => hf id hi spin
  | .add p q => supported_add (evaluate_supported f hf p) (evaluate_supported f hf q)
  | .mul p q => supported_polyMul (evaluate_supported f hf p) (evaluate_supported f hf q)
  | .smul c p => supported_smul (evaluate_supported f hf p) c

theorem lower_supported {half : Nat} (e : PlaquetteExpression half) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length (lower e) :=
  evaluate_supported _ (fun _ _ _ => original_character_support _ _ _) e

theorem upper_supported {half : Nat} (e : PlaquetteExpression half) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length (upper e) :=
  evaluate_supported _ (fun _ _ _ => original_character_support _ _ _) e

theorem temporalLower_supported {half : Nat} (e : PlaquetteExpression half) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length (temporalLower e) :=
  evaluate_supported _ (fun _ _ _ => temporal_character_support _ _ _ _) e

theorem temporalUpper_supported {half : Nat} (e : PlaquetteExpression half) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length (temporalUpper e) :=
  evaluate_supported _ (fun _ _ _ => temporal_character_support _ _ _ _) e

theorem lower_local {half : Nat} : ∀ e : PlaquetteExpression half, LowerLocal half (lower e)
  | .unit => BlockLocal.one _ _
  | .character _ hi spin => lower_plaquette_character_local (slabPlaquetteAt_mem (mem_centralLowerFaceIds.mp hi).1)
      (mem_centralLowerFaceIds.mp hi).2 spin
  | .add p q => (lower_local p).add (lower_local q)
  | .mul p q => (lower_local p).mul (lower_local q)
  | .smul c p => (lower_local p).smul c

theorem lower_reflection {half : Nat} : ∀ e : PlaquetteExpression half,
    ReflectionImage (centralExtent half) (lower e) (upper e)
  | .unit => ReflectionImage.one _
  | .character id hi spin => by
      change ReflectionImage _ _ (characterPolynomial (correctedSlabPlaquettePolynomial _ _).scalar spin)
      rw [slabPlaquetteAt_slabFaceReflectId (mem_centralLowerFaceIds.mp hi).1]
      exact plaquette_character_reflection (slabPlaquetteAt_mem (mem_centralLowerFaceIds.mp hi).1) spin
  | .add p q => (lower_reflection p).add (lower_reflection q)
  | .mul p q => (lower_reflection p).mul (lower_reflection q)
  | .smul c p => (lower_reflection p).smul c

def TemporalImage (half : Nat) (p q : RatPoly) : Prop :=
  PaddedPolynomialCoeffEqv (boundaryCompleteSlabLinks (centralExtent half)).length
    (applyTemporalTranslationLedger (centralExtent half) half p) q

namespace TemporalImage

theorem one (half : Nat) : TemporalImage half polyOne polyOne := by
  have h := applySteps_character (temporalTailBlocks_pos (centralExtent half))
    (temporalTranslationSteps (centralExtent half) half) polyOne 0
  rw [temporalTotalBlocks_eq] at h
  exact h

theorem add {half : Nat} {p p' q q' : RatPoly} (hp : TemporalImage half p p') (hq : TemporalImage half q q') :
    TemporalImage half (polyAdd p q) (polyAdd p' q') := by
  unfold TemporalImage applyTemporalTranslationLedger
  rw [applySelectedTranslationSteps_add]
  exact PaddedPolynomialCoeffEqv.add hp hq

theorem mul {half : Nat} {p p' q q' : RatPoly} (hp : TemporalImage half p p') (hq : TemporalImage half q q') :
    TemporalImage half (polyMul p q) (polyMul p' q') :=
  (PaddedPolynomialCoeffEqv.of_coeff (applySelectedTranslationSteps_mul (temporalTailBlocks_pos (centralExtent half)) _ p q)).trans
    (PaddedPolynomialCoeffEqv.mul hp hq)

theorem smul {half : Nat} {p q : RatPoly} (h : TemporalImage half p q) (c : Q') :
    TemporalImage half (polySmul c p) (polySmul c q) :=
  (PaddedPolynomialCoeffEqv.of_coeff (applySelectedTranslationSteps_smul (temporalTailBlocks_pos (centralExtent half)) _ c p)).trans
    (PaddedPolynomialCoeffEqv.smul h c)

end TemporalImage

theorem evaluate_image {half : Nat} (f g : Nat → Nat → RatPoly)
    (h : ∀ id, id ∈ centralLowerFaceIds half → ∀ spin, TemporalImage half (f id spin) (g id spin)) :
    ∀ e : PlaquetteExpression half, TemporalImage half (evaluate f e) (evaluate g e)
  | .unit => TemporalImage.one half
  | .character id hi spin => h id hi spin
  | .add p q => (evaluate_image f g h p).add (evaluate_image f g h q)
  | .mul p q => (evaluate_image f g h p).mul (evaluate_image f g h q)
  | .smul c p => (evaluate_image f g h p).smul c

theorem lower_image {half : Nat} (e : PlaquetteExpression half) : TemporalImage half (lower e) (temporalLower e) :=
  evaluate_image _ _ (fun _ hi spin => temporalLedger_character (half := half)
    (slabPlaquetteAt_mem (mem_centralLowerFaceIds.mp hi).1) spin) e

theorem upper_image {half : Nat} (e : PlaquetteExpression half) : TemporalImage half (upper e) (temporalUpper e) :=
  evaluate_image _ _ (fun _ hi spin => temporalLedger_character (half := half)
    (slabPlaquetteAt_mem (mem_centralUpperFaceIds.mp (upper_id hi)).1) spin) e

theorem evaluate_haar_congr {half blocks : Nat} (f g : Nat → Nat → RatPoly)
    (h : ∀ id, id ∈ centralLowerFaceIds half → ∀ spin, HaarCarrierEqv blocks (f id spin) (g id spin)) :
    ∀ e : PlaquetteExpression half, HaarCarrierEqv blocks (evaluate f e) (evaluate g e)
  | .unit => HaarCarrierEqv.refl _ _
  | .character id hi spin => h id hi spin
  | .add p q => HaarCarrierEqv.add (evaluate_haar_congr f g h p) (evaluate_haar_congr f g h q)
  | .mul p q => HaarCarrierEqv.mul (evaluate_haar_congr f g h p) (evaluate_haar_congr f g h q)
  | .smul c p => HaarCarrierEqv.smul c (evaluate_haar_congr f g h p)

theorem temporalLower_original {half : Nat} (e : PlaquetteExpression half) :
    HaarCarrierEqv (boundaryCompleteSlabLinks (centralExtent half)).length (temporalLower e) (lower e) :=
  evaluate_haar_congr _ _ (fun _ hi spin => RatPolyCoeffEqv.haarCarrier (characterPolynomial_coeffEqv
    (lower_face_unchanged (centralExtent half) half _ (mem_centralLowerFaceIds.mp hi).2).scalar spin)) e

theorem temporalUpper_original {half : Nat} (e : PlaquetteExpression half) :
    HaarCarrierEqv (boundaryCompleteSlabLinks (centralExtent half)).length (temporalUpper e) (upper e) :=
  evaluate_haar_congr _ _ (fun _ hi spin => upper_face_character (centralExtent half) half _
    (mem_centralUpperFaceIds.mp (upper_id hi)).2 spin) e

end YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra.PlaquetteExpression
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra.evaluate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra.lower
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra.upper
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra.temporalLower
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra.temporalUpper
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra.upper_id
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra.supported_smul
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra.evaluate_supported
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra.lower_supported
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra.upper_supported
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra.temporalLower_supported
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra.temporalUpper_supported
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra.lower_local
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra.lower_reflection
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra.TemporalImage
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra.TemporalImage.one
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra.TemporalImage.add
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra.TemporalImage.mul
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra.TemporalImage.smul
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra.evaluate_image
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra.lower_image
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra.upper_image
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra.evaluate_haar_congr
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra.temporalLower_original
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra.temporalUpper_original
