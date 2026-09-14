/-
# A common temporal gauge sweep for the ORIGINAL full finite action

Every stage uses one existing Haar-preserving ledger on the entire product.
Induction sweeps arbitrary numbers of cuts. The factor data retain arbitrary
signed character coefficients, repeated faces and shared link variables.
The full heat action is pinned to its existing definition, at every cutoff.

This is an exact change of variables. It does not assert a lower bound for
an interacting correlation or suppress any spatial or nonfundamental term.
-/

import YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters
import YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit

namespace YMGap.Continuum.BF4ExactSlabTemporalSweep

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.SU2CharacterVacuumHaar

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" extent => List.length (boundaryCompleteSlabLinks extent)

/-- Finite syntax for one original face factor; coefficients may be signed. -/
abbrev FaceFactor := Z4Plaq × List (Nat × Q')

def factor (characters : Z4Plaq → Nat → RatPoly) (f : FaceFactor) : RatPoly :=
  finitePolySum (fun term => polySmul term.2 (characters f.1 term.1)) f.2

def product (characters : Z4Plaq → Nat → RatPoly) (fs : List FaceFactor) : RatPoly :=
  polynomialProduct (factor characters) fs

def sweptProduct (extent cut : Nat) (fs : List FaceFactor) : RatPoly :=
  product (sweptCharacter extent cut) fs

def stepProduct (extent cut : Nat) (fs : List FaceFactor) : RatPoly :=
  product (stepCharacter extent cut) fs

private theorem sum_supported {A : Type} {b : Nat} (f : A → RatPoly)
    (h : ∀ a, SupportedQuaternionBlocks b (f a)) :
    ∀ xs : List A, SupportedQuaternionBlocks b (finitePolySum f xs)
  | [] => fun _ ht => False.elim (List.not_mem_nil ht)
  | a::xs => supported_add (h a) (sum_supported f h xs)

theorem product_supported {extent : Nat} (characters : Z4Plaq → Nat → RatPoly)
    (h : ∀ face spin, SupportedQuaternionBlocks (blocks extent) (characters face spin)) :
    ∀ fs, SupportedQuaternionBlocks (blocks extent) (product characters fs)
  | [] => supported_one _
  | f::fs => supported_polyMul (sum_supported _ (fun term : Nat × Q' => supported_smul (h f.1 term.1) term.2) f.2)
      (product_supported characters h fs)

private theorem factor_image {extent cut : Nat} (f : FaceFactor)
    (hf : f.1 ∈ boundaryCompleteSlabPlaquettes extent) :
    PaddedPolynomialCoeffEqv (blocks extent)
      (applyTemporalTranslationLedger extent cut (factor (sweptCharacter extent cut) f))
      (factor (stepCharacter extent cut) f) := by
  have h := applySteps_sum_image (temporalTailBlocks_pos extent) (temporalTranslationSteps extent cut)
    (fun term : Nat × Q' => polySmul term.2 (sweptCharacter extent cut f.1 term.1))
    (fun term : Nat × Q' => polySmul term.2 (stepCharacter extent cut f.1 term.1)) f.2
  rw [temporalTotalBlocks_eq] at h
  apply h
  intro term _
  exact (PaddedPolynomialCoeffEqv.of_coeff (applySelectedTranslationSteps_smul
    (temporalTailBlocks_pos extent) (temporalTranslationSteps extent cut) _ _)).trans
      ((swept_ledger_image (cut := cut) hf term.1).smul term.2)

theorem product_image {extent cut : Nat} (fs : List FaceFactor)
    (hf : ∀ f, f ∈ fs → f.1 ∈ boundaryCompleteSlabPlaquettes extent) :
    PaddedPolynomialCoeffEqv (blocks extent)
      (applyTemporalTranslationLedger extent cut (sweptProduct extent cut fs))
      (stepProduct extent cut fs) := by
  have h := applySteps_fold_image (temporalTailBlocks_pos extent) (temporalTranslationSteps extent cut)
    (factor (sweptCharacter extent cut)) (factor (stepCharacter extent cut)) fs
  rw [temporalTotalBlocks_eq] at h
  exact h (fun f hmem => factor_image f (hf f hmem))

private theorem sum_carrier {A : Type} {b : Nat} (f g : A → RatPoly)
    (h : ∀ a, HaarCarrierEqv b (f a) (g a)) :
    ∀ xs, HaarCarrierEqv b (finitePolySum f xs) (finitePolySum g xs)
  | [] => .refl _ _
  | a::xs => HaarCarrierEqv.add (h a) (sum_carrier f g h xs)

theorem product_carrier (extent cut : Nat) : ∀ fs : List FaceFactor,
    HaarCarrierEqv (blocks extent) (stepProduct extent cut fs) (sweptProduct extent (cut+1) fs)
  | [] => .refl _ _
  | f::fs => HaarCarrierEqv.mul
      (sum_carrier _ _ (fun term : Nat × Q' => HaarCarrierEqv.smul term.2
        (step_character_carrier extent cut f.1 term.1)) f.2)
      (product_carrier extent cut fs)

/-- ONE change of variables applied to the entire signed finite product. -/
theorem step_haar {extent cut : Nat} (fs : List FaceFactor)
    (hf : ∀ f, f ∈ fs → f.1 ∈ boundaryCompleteSlabPlaquettes extent) :
    quaternionHaar (blocks extent) (sweptProduct extent cut fs) ≈
      quaternionHaar (blocks extent) (sweptProduct extent (cut+1) fs) := by
  have hp := product_supported _ (swept_character_supported extent cut) fs
  have hq := product_supported _ (step_character_supported extent cut) fs
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (applyTemporalTranslationLedger_haar extent cut _ hp))
    (Q'.eqv_trans _ _ _ ((product_image fs hf).haar (applyTemporalTranslationLedger_supported extent cut _ hp) hq)
      (BF4ExactSlabAllExtentTemporalHaarForm.haar_of_carrier (product_carrier extent cut fs)))

/-- Common ascending sweep, not independent gauges for individual faces. -/
theorem sweep_haar (extent stop : Nat) (fs : List FaceFactor)
    (hf : ∀ f, f ∈ fs → f.1 ∈ boundaryCompleteSlabPlaquettes extent) :
    quaternionHaar (blocks extent) (sweptProduct extent 0 fs) ≈
      quaternionHaar (blocks extent) (sweptProduct extent stop fs) := by
  induction stop with
  | zero => exact Q'.eqv_refl _
  | succ stop ih => exact Q'.eqv_trans _ _ _ ih (step_haar (cut := stop) fs hf)

theorem swept_zero (extent : Nat) (fs : List FaceFactor) :
    sweptProduct extent 0 fs = product
      (fun face spin => characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin) fs := by
  have h : sweptCharacter extent 0 = fun face spin =>
      characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin := by
    funext face spin
    exact if_neg (not_swept_zero face)
  unfold sweptProduct
  rw [h]

def heatWeights (w : Q') (K : Nat) : List (Nat × Q') :=
  (List.range (K+1)).map (fun spin => (spin, coeffAt (heatKernelPacket K w) spin))

def actionFactors (w : Q') (K extent : Nat) : List FaceFactor :=
  (slabPhysicalFaceEdges extent).map (fun id => (slabPlaquetteAt extent id, heatWeights w K))

theorem actionFactors_physical (w : Q') (K extent : Nat) :
    ∀ f, f ∈ actionFactors w K extent → f.1 ∈ boundaryCompleteSlabPlaquettes extent := by
  intro f hf
  obtain ⟨id,hi,rfl⟩ := List.mem_map.mp hf
  exact slabPlaquetteAt_mem hi

private theorem finiteSum_map {A B : Type} (f : B → RatPoly) (g : A → B) : ∀ xs : List A,
    finitePolySum f (xs.map g) = finitePolySum (fun a => f (g a)) xs
  | [] => rfl
  | a::xs => by simp only [List.map_cons, finitePolySum, finiteSum_map f g xs]

private theorem action_zero (w : Q') (K extent : Nat) : ∀ ids : List Nat,
    sweptProduct extent 0 (ids.map (fun id => (slabPlaquetteAt extent id, heatWeights w K))) =
      polynomialProduct (faceHeatPolynomial w K extent) ids
  | [] => rfl
  | id::ids => by
    change polyMul _ (sweptProduct extent 0 (ids.map _)) = polyMul _ (polynomialProduct _ ids)
    rw [action_zero w K extent ids]
    congr 1
    simp only [factor, heatWeights, finiteSum_map, sweptCharacter, if_neg (not_swept_zero _)]
    rfl

/-- Literal equality with the pre-existing full ORIGINAL heat action. -/
theorem full_action_zero (w : Q') (K half : Nat) :
    sweptProduct (centralExtent half) 0 (actionFactors w K (centralExtent half)) = fullHeatProduct w K half :=
  action_zero w K (centralExtent half) _

/-- All original heat terms and shared variables survive the sweep. -/
theorem full_action_sweep (w : Q') (K half stop : Nat) :
    quaternionHaar (blocks (centralExtent half)) (fullHeatProduct w K half) ≈
      quaternionHaar (blocks (centralExtent half))
        (sweptProduct (centralExtent half) stop (actionFactors w K (centralExtent half))) := by
  rw [← full_action_zero]
  exact sweep_haar _ _ _ (actionFactors_physical w K _)

end YMGap.Continuum.BF4ExactSlabTemporalSweep

#print axioms YMGap.Continuum.BF4ExactSlabTemporalSweep.factor
#print axioms YMGap.Continuum.BF4ExactSlabTemporalSweep.product
#print axioms YMGap.Continuum.BF4ExactSlabTemporalSweep.sweptProduct
#print axioms YMGap.Continuum.BF4ExactSlabTemporalSweep.stepProduct
#print axioms YMGap.Continuum.BF4ExactSlabTemporalSweep.product_supported
#print axioms YMGap.Continuum.BF4ExactSlabTemporalSweep.product_image
#print axioms YMGap.Continuum.BF4ExactSlabTemporalSweep.product_carrier
#print axioms YMGap.Continuum.BF4ExactSlabTemporalSweep.step_haar
#print axioms YMGap.Continuum.BF4ExactSlabTemporalSweep.sweep_haar
#print axioms YMGap.Continuum.BF4ExactSlabTemporalSweep.swept_zero
#print axioms YMGap.Continuum.BF4ExactSlabTemporalSweep.heatWeights
#print axioms YMGap.Continuum.BF4ExactSlabTemporalSweep.actionFactors
#print axioms YMGap.Continuum.BF4ExactSlabTemporalSweep.actionFactors_physical
#print axioms YMGap.Continuum.BF4ExactSlabTemporalSweep.full_action_zero
#print axioms YMGap.Continuum.BF4ExactSlabTemporalSweep.full_action_sweep
