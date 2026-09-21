/-
# All-label harmonic transmission through an actual selected kinetic factor

Expose two distinct original blocks, substitute the retained link, restore the
empty head, and undo the explicit swaps. The resulting polynomial stays on the
same carrier. Harmonicity is stated in the explicit selected-pair chart; degree
is stated at the original selected block. The product-kernel consumer keeps
every unselected factor and arbitrary supported upper test in its boundary.

This is not a decomposition of the interacting weighted source or an energy
estimate. In particular it does not assert that V*g*f is a harmonic mode.
-/

import YMGap.Continuum.SU2QuaternionHarmonicHeatInsertion
import YMGap.Continuum.SU2QuaternionBlockSwapChainInverse
import YMGap.Continuum.SU2QuaternionProductHeatMarginals

namespace YMGap.Continuum.SU2QuaternionSelectedHarmonicHeatTransmission

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionFourBlockSelection
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.SU2QuaternionHarmonicHeatInsertion
open YMGap.Continuum.SU2QuaternionBlockSwapChainInverse
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.RGTransport (qpow)

local infix:50 " ≈ " => Q'.eqv

/-- Computed substitution output in the ORIGINAL coordinate order. -/
def transmittedImage {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) (p : RatPoly) : RatPoly :=
  applyQuaternionBlockSwapChain steps.reverse
    (retainedImage (applyQuaternionBlockSwapChain steps p))

theorem transmittedImage_supported (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (steps : List (QuaternionBlockInvolution (tailBlocks+1)))
    {p : RatPoly} (hp : SupportedQuaternionBlocks (tailBlocks+1) p) :
    SupportedQuaternionBlocks (tailBlocks+1) (transmittedImage steps p) :=
  reverse_chain_supported steps _ (retainedImage_supported tailBlocks hb
    (applyQuaternionBlockSwapChain_supported steps p hp))

/-- Same original carrier, arbitrary distinct pair, arbitrary independent
insertion, and the full cutoff-explicit all-label multiplier. -/
theorem selected_pair_harmonic (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (a b : Fin (tailBlocks+1)) (hab : a.val ≠ b.val)
    (w : Q') (K degree : Nat) (p r : RatPoly)
    (hp : SupportedQuaternionBlocks (tailBlocks+1) p)
    (hd : HasQuaternionBlockDegree a.val degree p)
    (hh : RatPolyCoeffEqv (headLaplacian
      (applyQuaternionBlockSwapChain (pairSteps (by omega) a b) p)) polyZero)
    (hr : SupportedQuaternionBlocks (tailBlocks+1) r)
    (hdr : HasQuaternionBlockDegree a.val 0 r) :
    quaternionHaar (tailBlocks+1)
      (polyMul (polyMul (heatAt a.val b.val w K) p) r) ≈
      if degree ≤ K then qpow w (degree*(degree+2)) *
        quaternionHaar (tailBlocks+1)
          (polyMul (transmittedImage (pairSteps (by omega) a b) p) r) else 0 := by
  let steps := pairSteps (show 1 < tailBlocks+1 by omega) a b
  let tp := applyQuaternionBlockSwapChain steps p
  let tr := applyQuaternionBlockSwapChain steps r
  have htp := applyQuaternionBlockSwapChain_supported steps p hp
  have htr := applyQuaternionBlockSwapChain_supported steps r hr
  have hdeg : HasQuaternionBlockDegree 0 degree tp := by
    apply chain_degree steps (by omega)
    rw [pair_zero (by omega) a b hab]
    exact hd
  have hrdeg : HasQuaternionBlockDegree 0 0 tr := by
    apply chain_degree steps (by omega)
    rw [pair_zero (by omega) a b hab]
    exact hdr
  have hk := heat_supported a.isLt b.isLt w K
  have hrelative := heat_supported (show 0 < tailBlocks+1 by omega)
    (show 1 < tailBlocks+1 by omega) w K
  have hleft := quaternionHaar_applyQuaternionBlockSwapChain steps _
    (supported_polyMul (supported_polyMul hk hp) hr)
  rw [chain_mul, chain_mul] at hleft
  have hpin := (((heat_exposed (by omega) a b hab w K).mul
      (PaddedPolynomialCoeffEqv.refl (tailBlocks+1) tp)).mul
        (PaddedPolynomialCoeffEqv.refl (tailBlocks+1) tr)).haar
    (supported_polyMul (supported_polyMul
      (applyQuaternionBlockSwapChain_supported steps _ hk) htp) htr)
    (supported_polyMul (supported_polyMul hrelative htp) htr)
  have hresult := Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft)
    (Q'.eqv_trans _ _ _ hpin
      (harmonic_transmission_same_carrier tailBlocks hb w K degree tp tr hdeg hh hrdeg))
  have hq := transmittedImage_supported tailBlocks hb steps hp
  have hright := quaternionHaar_applyQuaternionBlockSwapChain steps _ (supported_polyMul hq hr)
  rw [chain_mul] at hright
  have hrightPin := quaternionHaar_prefixPolynomialEqv (tailBlocks+1)
    ((apply_reverse_inverse_prefix steps (retainedImage tp)).mul
      (QuaternionPrefixPolynomialEqv.refl (tailBlocks+1) tr))
    (supported_polyMul (applyQuaternionBlockSwapChain_supported steps _ hq) htr)
    (supported_polyMul (retainedImage_supported tailBlocks hb htp) htr)
  by_cases hK : degree ≤ K
  · rw [if_pos hK] at hresult ⊢
    exact Q'.eqv_trans _ _ _ hresult
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ (Q'.eqv_symm hrightPin) hright))
  · rw [if_neg hK] at hresult ⊢
    exact hresult

/-- Arbitrary block count, avoiding dependent casts through a chosen
predecessor when this identity is used on a doubled product carrier. -/
theorem selected_pair_harmonic_at {blocks : Nat} (hb : 1 < blocks)
    (a b : Fin blocks) (hab : a.val ≠ b.val)
    (w : Q') (K degree : Nat) (p r : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p)
    (hd : HasQuaternionBlockDegree a.val degree p)
    (hh : RatPolyCoeffEqv (headLaplacian
      (applyQuaternionBlockSwapChain (pairSteps hb a b) p)) polyZero)
    (hr : SupportedQuaternionBlocks blocks r)
    (hdr : HasQuaternionBlockDegree a.val 0 r) :
    quaternionHaar blocks (polyMul (polyMul (heatAt a.val b.val w K) p) r) ≈
      if degree ≤ K then qpow w (degree*(degree+2)) * quaternionHaar blocks
        (polyMul (transmittedImage (pairSteps hb a b) p) r) else 0 := by
  cases blocks with
  | zero => omega
  | succ tailBlocks =>
      exact selected_pair_harmonic tailBlocks (by omega) a b hab w K degree p r hp hd hh hr hdr

/-- Explicit chart of the actual lower/upper kinetic pair. -/
def kineticPairSteps {n : Nat} (i : Fin n) : List (QuaternionBlockInvolution (n+n)) :=
  pairSteps (by have := i.isLt; omega)
    ⟨i.val, by have := i.isLt; omega⟩ ⟨n+i.val, by have := i.isLt; omega⟩

/-- Remove exactly one actual selected kinetic factor, preserving all other
kernel factors and the original arbitrary upper test. Harmonicity is checked
on the explicit chart of p, never supplied as a propagation identity. -/
theorem productHeat_selected_harmonic {n : Nat} (i : Fin n)
    (w : Q') (K degree : Nat) (ids : List Nat)
    (hnot : i.val ∉ ids) (hids : ∀ j, j ∈ ids → j < n)
    (p g : RatPoly) (hp : SupportedQuaternionBlocks (n+n) p)
    (hd : HasQuaternionBlockDegree i.val degree p)
    (hh : RatPolyCoeffEqv
      (headLaplacian (applyQuaternionBlockSwapChain (kineticPairSteps i) p)) polyZero)
    (hg : SupportedQuaternionBlocks n g) :
    quaternionHaar (n+n)
      (polyMul (productHeat n w K (i.val::ids)) (polyMul p (liftBoundary n g))) ≈
      if degree ≤ K then qpow w (degree*(degree+2)) * quaternionHaar (n+n)
        (polyMul (productHeat n w K ids)
          (polyMul (transmittedImage (kineticPairSteps i) p) (liftBoundary n g))) else 0 := by
  have hn := i.isLt
  let a : Fin (n+n) := ⟨i.val, by omega⟩
  let b : Fin (n+n) := ⟨n+i.val, by omega⟩
  have hs := supported_polyMul (productHeat_supported n w K ids hids) (lift_supported hg n)
  have hz := (independent_has_degree_zero
      (productHeat_independent_lower n w K ids hids i.val i.isLt hnot)).mul
    (independent_has_degree_zero (lift_lower_independent n g i.val i.isLt))
  have h := selected_pair_harmonic_at (by omega) a b (by change i.val ≠ n+i.val; omega)
    w K degree p (polyMul (productHeat n w K ids) (liftBoundary n g))
    hp hd hh hs hz
  have rearrange (s : RatPoly) : RatPolyCoeffEqv
      (polyMul (productHeat n w K ids) (polyMul s (liftBoundary n g)))
      (polyMul s (polyMul (productHeat n w K ids) (liftBoundary n g))) :=
    coeffEvalExpr_eqv_of_normalize_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => productHeat n w K ids | 1 => s | _ => liftBoundary n g)
  have hleft := haar_of_coeff (blocks := n+n)
    (((RatPolyCoeffEqv.mul_assoc _ _ _).trans
      ((rearrange p).mul_left (heatAt i.val (n+i.val) w K))).trans
      (RatPolyCoeffEqv.mul_assoc _ _ _).symm)
  by_cases hK : degree ≤ K
  · rw [if_pos hK] at h ⊢
    exact Q'.eqv_trans _ _ _ hleft
      (Q'.eqv_trans _ _ _ h
        (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (rearrange _).symm)))
  · rw [if_neg hK] at h ⊢
    exact Q'.eqv_trans _ _ _ hleft h

/-- The selected-factor result consumed by the ACTUAL product kinetic map.
The remaining mixed lower/upper polynomial is kept in its original doubled
integral; it is not falsely repackaged as a lower-only source. -/
theorem productMap_selected_harmonic {n : Nat} (i : Fin n)
    (w : Q') (K degree : Nat) (ids : List Nat)
    (hnot : i.val ∉ ids) (hids : ∀ j, j ∈ ids → j < n)
    (p g : RatPoly) (hp : SupportedQuaternionBlocks n p)
    (hd : HasQuaternionBlockDegree i.val degree p)
    (hh : RatPolyCoeffEqv
      (headLaplacian (applyQuaternionBlockSwapChain (kineticPairSteps i) p)) polyZero)
    (hg : SupportedQuaternionBlocks n g) :
    quaternionHaar n (polyMul g (productMap n w K (i.val::ids) p)) ≈
      if degree ≤ K then qpow w (degree*(degree+2)) * quaternionHaar (n+n)
        (polyMul (productHeat n w K ids)
          (polyMul (transmittedImage (kineticPairSteps i) p) (liftBoundary n g))) else 0 := by
  have hp2 : SupportedQuaternionBlocks (n+n) p := fun t ht =>
    Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 (by omega))
  exact Q'.eqv_trans _ _ _ (productMap_pairing n w K (i.val::ids) p g)
    (productHeat_selected_harmonic i w K degree ids hnot hids p g hp2 hd hh hg)

end YMGap.Continuum.SU2QuaternionSelectedHarmonicHeatTransmission

#print axioms YMGap.Continuum.SU2QuaternionSelectedHarmonicHeatTransmission.transmittedImage_supported
#print axioms YMGap.Continuum.SU2QuaternionSelectedHarmonicHeatTransmission.selected_pair_harmonic
#print axioms YMGap.Continuum.SU2QuaternionSelectedHarmonicHeatTransmission.selected_pair_harmonic_at
#print axioms YMGap.Continuum.SU2QuaternionSelectedHarmonicHeatTransmission.productHeat_selected_harmonic
#print axioms YMGap.Continuum.SU2QuaternionSelectedHarmonicHeatTransmission.productMap_selected_harmonic
