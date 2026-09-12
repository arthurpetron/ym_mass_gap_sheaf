/-
# The same signed slab observable under the common temporal assignment

The full original ledger's plaquette-word image extends to every character
and then to the ORIGINAL finite signed boundary sums and heat products.
The target polynomials evaluate the previously defined temporalFaceWord;
they are not defined by applying the ledger. The final theorem identifies
the original observableIntegrand with these independently specified images.

All original heat coefficients, face IDs, reflected labels and signed
observable coefficients are retained. This is a coefficient identity, not
reflection positivity, a physical gap or a continuum result.
-/

import YMGap.Continuum.BF4ExactSlabTemporalGaugeUpperCoordinates
import YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
import YMGap.Continuum.BF4ExactSlabReflectedObservableHaarForm

namespace YMGap.Continuum.BF4ExactSlabTemporalGaugeObservableImages

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.BF4ExactSlabTemporalGaugeUpperCoordinates
open YMGap.Continuum.BF4ExactSlabWeightedFaceFactorization
open YMGap.Continuum.BF4ExactSlabObservableHaarForm
open YMGap.Continuum.BF4ExactSlabInterfaceHeatProduct
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.ClusterCount4DProgress
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

private theorem slab_blocks : temporalTailBlocks 1 + 1 = 116 :=
  (temporalTotalBlocks_eq 1).trans correctedSlabLinks_extent_one_length

def temporalCharacter (extent half : Nat) (face : Z4Plaq) (spin : Nat) : RatPoly :=
  characterPolynomial (temporalFaceWord extent half face).scalar spin

/-- All spins and all physical faces at arbitrary extent/half-plane. -/
theorem temporalLedger_character {extent half : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) (spin : Nat) :
    PaddedPolynomialCoeffEqv (boundaryCompleteSlabLinks extent).length
      (applyTemporalTranslationLedger extent half
        (characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin))
      (temporalCharacter extent half face spin) := by
  have hw : PaddedPolynomialCoeffEqv (boundaryCompleteSlabLinks extent).length
      (applyTemporalTranslationLedger extent half (correctedSlabPlaquettePolynomial extent face).scalar)
      (temporalFaceWord extent half face).scalar := (temporalLedger_plaquette_word (half := half) hf).scalar
  have h := applySteps_character (temporalTailBlocks_pos extent) (temporalTranslationSteps extent half)
    (correctedSlabPlaquettePolynomial extent face).scalar spin
  rw [temporalTotalBlocks_eq] at h
  exact h.trans (hw.character spin)

def temporalWeightedFacePolynomial (w : Q') (K : Nat) (state : EdgeLabelling) (id : Nat) : RatPoly :=
  polySmul (coeffAt (heatKernelPacket K w) (state id))
    (temporalCharacter 1 0 (slabPlaquetteAt 1 id) (state id))

def temporalFaceProduct (w : Q') (K : Nat) (state : EdgeLabelling) (ids : List Nat) : RatPoly :=
  ids.foldr (fun id p => polyMul (temporalWeightedFacePolynomial w K state id) p) polyOne

def temporalLowerObservable (w : Q') (K : Nat) (c : EdgeLabelling → Q') : RatPoly :=
  finitePolySum (fun state => polySmul (c state) (temporalFaceProduct w K state (centralLowerFaceIds 0)))
    (centralHalfStates K 0)

def temporalUpperObservable (w : Q') (K : Nat) (c : EdgeLabelling → Q') : RatPoly :=
  finitePolySum (fun state => polySmul (c state)
    (temporalFaceProduct w K (fun id => state (slabFaceReflectId 1 id)) (centralUpperFaceIds 0)))
    (centralHalfStates K 0)

def temporalFaceHeatPolynomial (w : Q') (K id : Nat) : RatPoly :=
  finitePolySum (fun spin => polySmul (coeffAt (heatKernelPacket K w) spin)
    (temporalCharacter 1 0 (slabPlaquetteAt 1 id) spin)) (List.range (K + 1))

def temporalInterfaceHeatProduct (w : Q') (K : Nat) : RatPoly :=
  (centralFixedFaceIds 0).foldr (fun id p => polyMul (temporalFaceHeatPolynomial w K id) p) polyOne

def temporalObservableIntegrand (w : Q') (K : Nat) (left right : EdgeLabelling → Q') : RatPoly :=
  polyMul (temporalLowerObservable w K left)
    (polyMul (temporalInterfaceHeatProduct w K) (temporalUpperObservable w K right))

private theorem image_mul (p q : RatPoly) : PaddedPolynomialCoeffEqv 116
    (applyTemporalTranslationLedger 1 0 (polyMul p q))
    (polyMul (applyTemporalTranslationLedger 1 0 p) (applyTemporalTranslationLedger 1 0 q)) :=
  .of_coeff (applySelectedTranslationSteps_mul (temporalTailBlocks_pos 1) _ p q)

private theorem image_smul (a : Q') (p : RatPoly) : PaddedPolynomialCoeffEqv 116
    (applyTemporalTranslationLedger 1 0 (polySmul a p))
    (polySmul a (applyTemporalTranslationLedger 1 0 p)) :=
  .of_coeff (applySelectedTranslationSteps_smul (temporalTailBlocks_pos 1) _ a p)

private theorem image_sum {A : Type} (f g : A → RatPoly) (xs : List A)
    (h : ∀ a, a ∈ xs → PaddedPolynomialCoeffEqv 116 (applyTemporalTranslationLedger 1 0 (f a)) (g a)) :
    PaddedPolynomialCoeffEqv 116 (applyTemporalTranslationLedger 1 0 (finitePolySum f xs)) (finitePolySum g xs) := by
  have hh := applySteps_sum_image (temporalTailBlocks_pos 1) (temporalTranslationSteps 1 0) f g xs
  rw [slab_blocks] at hh
  exact hh h

private theorem image_fold {A : Type} (f g : A → RatPoly) (xs : List A)
    (h : ∀ a, a ∈ xs → PaddedPolynomialCoeffEqv 116 (applyTemporalTranslationLedger 1 0 (f a)) (g a)) :
    PaddedPolynomialCoeffEqv 116
      (applyTemporalTranslationLedger 1 0 (xs.foldr (fun a p => polyMul (f a) p) polyOne))
      (xs.foldr (fun a p => polyMul (g a) p) polyOne) := by
  have hh := applySteps_fold_image (temporalTailBlocks_pos 1) (temporalTranslationSteps 1 0) f g xs
  rw [slab_blocks] at hh
  exact hh h

theorem weightedFacePolynomial_image (w : Q') (K : Nat) (state : EdgeLabelling) {id : Nat}
    (hi : id ∈ slabPhysicalFaceEdges 1) : PaddedPolynomialCoeffEqv 116
      (applyTemporalTranslationLedger 1 0 (weightedFacePolynomial w K state id))
      (temporalWeightedFacePolynomial w K state id) := by
  have h := temporalLedger_character (half := 0) (slabPlaquetteAt_mem hi) (state id)
  rw [correctedSlabLinks_extent_one_length] at h
  exact (image_smul _ _).trans (h.smul _)

theorem lowerPolynomial_image (w : Q') (K : Nat) (state : EdgeLabelling) :
    PaddedPolynomialCoeffEqv 116 (applyTemporalTranslationLedger 1 0 (lowerPolynomial w K state))
      (temporalFaceProduct w K state (centralLowerFaceIds 0)) := by
  rw [lowerPolynomial_eq_fold]
  exact image_fold _ _ _ (fun id hi => weightedFacePolynomial_image w K state (mem_centralLowerFaceIds.mp hi).1)

theorem upperPolynomial_image (w : Q') (K : Nat) (state : EdgeLabelling) :
    PaddedPolynomialCoeffEqv 116 (applyTemporalTranslationLedger 1 0 (upperPolynomial w K state))
      (temporalFaceProduct w K (fun id => state (slabFaceReflectId 1 id)) (centralUpperFaceIds 0)) := by
  rw [upperPolynomial_eq_fold]
  exact image_fold _ _ _ (fun id hi => weightedFacePolynomial_image w K _ (mem_centralUpperFaceIds.mp hi).1)

theorem lowerObservable_image (w : Q') (K : Nat) (c : EdgeLabelling → Q') :
    PaddedPolynomialCoeffEqv 116 (applyTemporalTranslationLedger 1 0 (lowerObservable w K c))
      (temporalLowerObservable w K c) :=
  image_sum _ _ _ (fun state _ => (image_smul _ _).trans ((lowerPolynomial_image w K state).smul _))

theorem upperObservable_image (w : Q') (K : Nat) (c : EdgeLabelling → Q') :
    PaddedPolynomialCoeffEqv 116 (applyTemporalTranslationLedger 1 0 (upperObservable w K c))
      (temporalUpperObservable w K c) :=
  image_sum _ _ _ (fun state _ => (image_smul _ _).trans ((upperPolynomial_image w K state).smul _))

theorem faceHeatPolynomial_image (w : Q') (K : Nat) {id : Nat} (hi : id ∈ slabPhysicalFaceEdges 1) :
    PaddedPolynomialCoeffEqv 116 (applyTemporalTranslationLedger 1 0 (faceHeatPolynomial w K id))
      (temporalFaceHeatPolynomial w K id) := by
  apply image_sum
  intro spin _
  have h := temporalLedger_character (half := 0) (slabPlaquetteAt_mem hi) spin
  rw [correctedSlabLinks_extent_one_length] at h
  exact (image_smul _ _).trans (h.smul _)

theorem interfaceHeatProduct_image (w : Q') (K : Nat) : PaddedPolynomialCoeffEqv 116
    (applyTemporalTranslationLedger 1 0 (interfaceHeatProduct w K)) (temporalInterfaceHeatProduct w K) :=
  image_fold _ _ _ (fun _ hi => faceHeatPolynomial_image w K (mem_centralFixedFaceIds.mp hi).1)

theorem observableProduct_image (w : Q') (K : Nat) (left right : EdgeLabelling → Q') :
    PaddedPolynomialCoeffEqv 116
      (applyTemporalTranslationLedger 1 0 (polyMul (lowerObservable w K left)
        (polyMul (interfaceHeatProduct w K) (upperObservable w K right))))
      (temporalObservableIntegrand w K left right) :=
  (image_mul _ _).trans ((lowerObservable_image w K left).mul
    ((image_mul _ _).trans ((interfaceHeatProduct_image w K).mul (upperObservable_image w K right))))

/-- Full original signed observable, not merely one coordinate or character.
The heat product target uses the same heat packet and physical face carrier. -/
theorem observableIntegrand_image (w : Q') (K : Nat) (left right : EdgeLabelling → Q') :
    PaddedPolynomialCoeffEqv 116 (applyTemporalTranslationLedger 1 0 (observableIntegrand w K left right))
      (temporalObservableIntegrand w K left right) := by
  have hs : PaddedPolynomialCoeffEqv 116 (applyTemporalTranslationLedger 1 0 (observableIntegrand w K left right))
      (applyTemporalTranslationLedger 1 0 (polyMul (lowerObservable w K left)
        (polyMul (interfaceHeatProduct w K) (upperObservable w K right)))) :=
    .of_coeff (applySelectedTranslationSteps_coeffEqv (temporalTailBlocks_pos 1) _
      (observableIntegrand_eq_product w K left right))
  exact hs.trans (observableProduct_image w K left right)

end YMGap.Continuum.BF4ExactSlabTemporalGaugeObservableImages

#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeObservableImages.temporalCharacter
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeObservableImages.temporalLedger_character
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeObservableImages.temporalWeightedFacePolynomial
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeObservableImages.temporalFaceProduct
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeObservableImages.temporalLowerObservable
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeObservableImages.temporalUpperObservable
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeObservableImages.temporalFaceHeatPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeObservableImages.temporalInterfaceHeatProduct
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeObservableImages.temporalObservableIntegrand
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeObservableImages.weightedFacePolynomial_image
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeObservableImages.lowerPolynomial_image
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeObservableImages.upperPolynomial_image
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeObservableImages.lowerObservable_image
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeObservableImages.upperObservable_image
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeObservableImages.faceHeatPolynomial_image
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeObservableImages.interfaceHeatProduct_image
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeObservableImages.observableProduct_image
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeObservableImages.observableIntegrand_image
