/-
# Full original signed observable under the all-extent temporal ledger

The original lower, crossing and reflected-upper polynomials are transported
by the same already constructed Haar-preserving ledger. Their independently
defined targets use temporalFaceWord, retaining every original heat weight,
label and signed observable coefficient. This coefficient pin is not yet its
Haar consequence: full support is checked by the following consumer.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm

namespace YMGap.Continuum.BF4ExactSlabAllExtentTemporalImages

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

private abbrev Image (half : Nat) (p q : RatPoly) :=
  PaddedPolynomialCoeffEqv (boundaryCompleteSlabLinks (centralExtent half)).length
    (applyTemporalTranslationLedger (centralExtent half) half p) q

def temporalWeightedFacePolynomial (w : Q') (K half : Nat) (state : EdgeLabelling) (id : Nat) : RatPoly :=
  polySmul (coeffAt (heatKernelPacket K w) (state id))
    (characterPolynomial (temporalFaceWord (centralExtent half) half
      (slabPlaquetteAt (centralExtent half) id)).scalar (state id))

def temporalFaceProduct (w : Q') (K half : Nat) (state : EdgeLabelling) (ids : List Nat) : RatPoly :=
  polynomialProduct (temporalWeightedFacePolynomial w K half state) ids

def temporalLowerObservable (w : Q') (K half : Nat) (c : EdgeLabelling → Q') : RatPoly :=
  finitePolySum (fun s => polySmul (c s) (temporalFaceProduct w K half s (centralLowerFaceIds half)))
    (centralHalfStates K half)

def temporalUpperObservable (w : Q') (K half : Nat) (c : EdgeLabelling → Q') : RatPoly :=
  finitePolySum (fun s => polySmul (c s) (temporalFaceProduct w K half
    (fun id => s (slabFaceReflectId (centralExtent half) id)) (centralUpperFaceIds half))) (centralHalfStates K half)

def temporalObservableIntegrand (w : Q') (K half : Nat) (left right : EdgeLabelling → Q') : RatPoly :=
  polyMul (temporalLowerObservable w K half left)
    (polyMul (temporalInterfacePolynomial w K half) (temporalUpperObservable w K half right))

private theorem image_mul (half : Nat) (p q : RatPoly) :
    Image half (polyMul p q) (polyMul (applyTemporalTranslationLedger (centralExtent half) half p)
      (applyTemporalTranslationLedger (centralExtent half) half q)) :=
  .of_coeff (applySelectedTranslationSteps_mul (temporalTailBlocks_pos (centralExtent half)) _ p q)

private theorem image_smul (half : Nat) (a : Q') (p : RatPoly) :
    Image half (polySmul a p) (polySmul a (applyTemporalTranslationLedger (centralExtent half) half p)) :=
  .of_coeff (applySelectedTranslationSteps_smul (temporalTailBlocks_pos (centralExtent half)) _ a p)

private theorem image_sum {A : Type} (half : Nat) (f g : A → RatPoly) (xs : List A)
    (h : ∀ a, a ∈ xs → Image half (f a) (g a)) :
    Image half (finitePolySum f xs) (finitePolySum g xs) := by
  have hh := applySteps_sum_image (temporalTailBlocks_pos (centralExtent half))
    (temporalTranslationSteps (centralExtent half) half) f g xs
  rw [temporalTotalBlocks_eq] at hh
  exact hh h

private theorem image_fold {A : Type} (half : Nat) (f g : A → RatPoly) (xs : List A)
    (h : ∀ a, a ∈ xs → Image half (f a) (g a)) :
    Image half (polynomialProduct f xs) (polynomialProduct g xs) := by
  have hh := applySteps_fold_image (temporalTailBlocks_pos (centralExtent half))
    (temporalTranslationSteps (centralExtent half) half) f g xs
  rw [temporalTotalBlocks_eq] at hh
  exact hh h

theorem weightedFace_image (w : Q') (K half : Nat) (s : EdgeLabelling) {id : Nat}
    (hi : id ∈ slabPhysicalFaceEdges (centralExtent half)) :
    Image half (weightedFacePolynomial w K (centralExtent half) s id) (temporalWeightedFacePolynomial w K half s id) :=
  (image_smul half _ _).trans
    ((BF4ExactSlabTemporalGaugeObservableImages.temporalLedger_character (half := half) (slabPlaquetteAt_mem hi) (s id)).smul _)

theorem lowerPolynomial_image (w : Q') (K half : Nat) (s : EdgeLabelling) :
    Image half (lowerPolynomial w K half s) (temporalFaceProduct w K half s (centralLowerFaceIds half)) :=
  image_fold half _ _ _ (fun _ hi => weightedFace_image w K half s (mem_centralLowerFaceIds.mp hi).1)

theorem upperPolynomial_image (w : Q') (K half : Nat) (s : EdgeLabelling) :
    Image half (upperPolynomial w K half s) (temporalFaceProduct w K half
      (fun id => s (slabFaceReflectId (centralExtent half) id)) (centralUpperFaceIds half)) :=
  image_fold half _ _ _ (fun _ hi => weightedFace_image w K half _ (mem_centralUpperFaceIds.mp hi).1)

theorem lowerObservable_image (w : Q') (K half : Nat) (c : EdgeLabelling → Q') :
    Image half (lowerObservable w K half c) (temporalLowerObservable w K half c) :=
  image_sum half _ _ _ (fun s _ => (image_smul half _ _).trans ((lowerPolynomial_image w K half s).smul _))

theorem upperObservable_image (w : Q') (K half : Nat) (c : EdgeLabelling → Q') :
    Image half (upperObservable w K half c) (temporalUpperObservable w K half c) :=
  image_sum half _ _ _ (fun s _ => (image_smul half _ _).trans ((upperPolynomial_image w K half s).smul _))

theorem faceHeat_image (w : Q') (K half : Nat) {id : Nat} (hi : id ∈ slabPhysicalFaceEdges (centralExtent half)) :
    Image half (BF4ExactSlabAllExtentObservableHaarForm.faceHeatPolynomial w K (centralExtent half) id)
      (temporalFaceHeatPolynomial w K half id) :=
  image_sum half _ _ _ (fun spin _ => (image_smul half _ _).trans
    ((BF4ExactSlabTemporalGaugeObservableImages.temporalLedger_character (half := half) (slabPlaquetteAt_mem hi) spin).smul _))

theorem interfaceHeatProduct_image (w : Q') (K half : Nat) :
    Image half (interfaceHeatProduct w K half) (temporalInterfacePolynomial w K half) :=
  image_fold half _ _ _ (fun _ hi => faceHeat_image w K half (mem_centralFixedFaceIds.mp hi).1)

/-- Complete original signed observable image at every odd extent. The
target was independently defined using the physical temporal link assignment. -/
theorem observableProduct_image (w : Q') (K half : Nat) (left right : EdgeLabelling → Q') :
    Image half (polyMul (lowerObservable w K half left)
      (polyMul (interfaceHeatProduct w K half) (upperObservable w K half right)))
      (temporalObservableIntegrand w K half left right) :=
  (image_mul half _ _).trans ((lowerObservable_image w K half left).mul
    ((image_mul half _ _).trans ((interfaceHeatProduct_image w K half).mul (upperObservable_image w K half right))))

end YMGap.Continuum.BF4ExactSlabAllExtentTemporalImages

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentTemporalImages.temporalWeightedFacePolynomial
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentTemporalImages.temporalFaceProduct
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentTemporalImages.temporalLowerObservable
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentTemporalImages.temporalUpperObservable
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentTemporalImages.temporalObservableIntegrand
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentTemporalImages.weightedFace_image
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentTemporalImages.lowerPolynomial_image
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentTemporalImages.upperPolynomial_image
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentTemporalImages.lowerObservable_image
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentTemporalImages.upperObservable_image
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentTemporalImages.faceHeat_image
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentTemporalImages.interfaceHeatProduct_image
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentTemporalImages.observableProduct_image
