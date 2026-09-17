/-
# Preserve an original invariant observable through the common action sweep

The observable and EVERY action factor undergo one common temporal ledger.
Only after this change of variables is the observable returned to its original
value, under the transformed action as a supported spectator insertion.
No link independence, absolute-value replacement, or new partition is used.

The finite algebra below consumes supported-insertion invariance, not a claim
that a source coordinate polynomial is a physical observable. Actual closed
spatial Wilson words supply this input in the companion physical-word module.
This is not an embedding into the face-generated union, an OS multiplier
bound, a change of cutoff/volume limits, or a physical mass-gap theorem.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialChainAction

namespace YMGap.Continuum.BF4ExactSlabTemporalInvariantSweep

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm (haar_of_carrier)
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters
open YMGap.Continuum.BF4ExactSlabSpatialSliceFactors
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainAction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

/-- One ledger acts on the observable AND action. Invariance is used with
the complete transformed action as insertion, never with an empty spectator. -/
theorem invariant_step_haar {extent cut : Nat} (p : RatPoly)
    (hp : SupportedQuaternionBlocks (B extent) p)
    (hinv : ∀ r : RatPoly, SupportedQuaternionBlocks (B extent) r →
      quaternionHaar (B extent) (polyMul r (applyTemporalTranslationLedger extent cut p)) ≈
        quaternionHaar (B extent) (polyMul r p))
    (fs : List FaceFactor)
    (hf : ∀ f, f ∈ fs → f.1 ∈ boundaryCompleteSlabPlaquettes extent) :
    quaternionHaar (B extent) (polyMul p (sweptProduct extent cut fs)) ≈
      quaternionHaar (B extent) (polyMul p (sweptProduct extent (cut+1) fs)) := by
  have hs := product_supported _ (swept_character_supported extent cut) fs
  have ht := product_supported _ (step_character_supported extent cut) fs
  have hi : PaddedPolynomialCoeffEqv (B extent)
      (applyTemporalTranslationLedger extent cut (polyMul p (sweptProduct extent cut fs)))
      (polyMul (applyTemporalTranslationLedger extent cut p) (stepProduct extent cut fs)) :=
    (PaddedPolynomialCoeffEqv.of_coeff
      (applySelectedTranslationSteps_mul (temporalTailBlocks_pos extent) _ _ _)).trans
        ((PaddedPolynomialCoeffEqv.refl _ _).mul (product_image fs hf))
  have hchange := Q'.eqv_trans _ _ _
    (Q'.eqv_symm (applyTemporalTranslationLedger_haar extent cut _ (supported_polyMul hp hs)))
    (hi.haar (applyTemporalTranslationLedger_supported extent cut _ (supported_polyMul hp hs))
      (supported_polyMul (applyTemporalTranslationLedger_supported extent cut p hp) ht))
  have hreturn := Q'.eqv_trans _ _ _
    (quaternionHaar_polyMul_comm (B extent) _ _)
    (Q'.eqv_trans _ _ _ (hinv (stepProduct extent cut fs) ht)
      (quaternionHaar_polyMul_comm (B extent) _ _))
  exact Q'.eqv_trans _ _ _ hchange
    (Q'.eqv_trans _ _ _ hreturn (product_carrier extent cut fs p))

/-- Arbitrary ascending sweep, retaining the SAME original observable. -/
theorem invariant_sweep_haar (extent stop : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (B extent) p)
    (hinv : ∀ cut, ∀ r : RatPoly, SupportedQuaternionBlocks (B extent) r →
      quaternionHaar (B extent) (polyMul r (applyTemporalTranslationLedger extent cut p)) ≈
        quaternionHaar (B extent) (polyMul r p))
    (fs : List FaceFactor)
    (hf : ∀ f, f ∈ fs → f.1 ∈ boundaryCompleteSlabPlaquettes extent) :
    quaternionHaar (B extent) (polyMul p (sweptProduct extent 0 fs)) ≈
      quaternionHaar (B extent) (polyMul p (sweptProduct extent stop fs)) := by
  induction stop with
  | zero => exact Q'.eqv_refl _
  | succ stop ih => exact Q'.eqv_trans _ _ _ ih (invariant_step_haar p hp (hinv stop) fs hf)

/-- The exact selected original action becomes its existing chronological
factorization, with no change to the invariant physical observable. -/
theorem invariant_original_chain_pairing (w : Q') (K extent width start steps : Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (B extent) p)
    (hinv : ∀ cut, ∀ r : RatPoly, SupportedQuaternionBlocks (B extent) r →
      quaternionHaar (B extent) (polyMul r (applyTemporalTranslationLedger extent cut p)) ≈
        quaternionHaar (B extent) (polyMul r p)) :
    quaternionHaar (B extent) (polyMul p (originalChainAction w K extent width start steps)) ≈
      quaternionHaar (B extent) (polyMul p (ambientChain w K extent width start steps)) := by
  have ha : ∀ f, f ∈ heatFactors w K extent (chainIds extent width start steps) →
      f.1 ∈ boundaryCompleteSlabPlaquettes extent := by
    intro f hf
    obtain ⟨id, hi, rfl⟩ := List.mem_map.mp hf
    exact slabPlaquetteAt_mem (chainIds_physical hi)
  have h := invariant_sweep_haar extent (start+steps) p hp hinv
    (heatFactors w K extent (chainIds extent width start steps)) ha
  rw [heatFactors_zero] at h
  exact Q'.eqv_trans _ _ _ h (haar_of_coeff_eqv (B extent)
    ((swept_chain_factorization w K extent width start steps (start+steps)
      (Nat.le_refl _)).mul_left p))

end YMGap.Continuum.BF4ExactSlabTemporalInvariantSweep

#print axioms YMGap.Continuum.BF4ExactSlabTemporalInvariantSweep.invariant_step_haar
#print axioms YMGap.Continuum.BF4ExactSlabTemporalInvariantSweep.invariant_sweep_haar
#print axioms YMGap.Continuum.BF4ExactSlabTemporalInvariantSweep.invariant_original_chain_pairing
