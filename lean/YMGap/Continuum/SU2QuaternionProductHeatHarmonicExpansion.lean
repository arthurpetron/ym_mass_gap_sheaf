/-
# Harmonic expansion through one actual product-heat factor

Expose one selected lower/upper pair, apply the computed finite harmonic
expansion to the arbitrary signed lower input, and retain every remaining
kernel factor in the exposed insertion.  The output is deliberately left in
the selected chart on the same full carrier.  This is an exact finite signed
formula, not a uniform estimate or a simultaneous diagonalization of repeated
product factors.
-/

import YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion

namespace YMGap.Continuum.SU2QuaternionProductHeatHarmonicExpansion

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
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionSelectedHarmonicHeatTransmission
open YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion

local infix:50 " ≈ " => Q'.eqv

/-- The arbitrary selected-pair input, in the chart where the chosen lower
block is the head and its upper partner is the retained block. -/
def exposedInput {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) (p : RatPoly) : RatPoly :=
  applyQuaternionBlockSwapChain steps p

/-- The complete remaining insertion in the same selected-pair chart. -/
def exposedInsertion {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) (r : RatPoly) : RatPoly :=
  applyQuaternionBlockSwapChain steps r

/-- One selected heat factor acting on an arbitrary supported signed input.
The finite harmonic modes are computed from the exposed input; no degree or
harmonicity premise is supplied by the caller. -/
theorem selected_pair_expansion (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (a b : Fin (tailBlocks+1)) (hab : a.val ≠ b.val)
    (w : Q') (K : Nat) (p r : RatPoly)
    (hp : SupportedQuaternionBlocks (tailBlocks+1) p)
    (hr : SupportedQuaternionBlocks (tailBlocks+1) r)
    (hdr : HasQuaternionBlockDegree a.val 0 r) :
    quaternionHaar (tailBlocks+1)
      (polyMul (polyMul (heatAt a.val b.val w K) p) r) ≈
      qListSum
        ((modes (tailBlocks+1) (by omega)
          (exposedInput (pairSteps (by omega) a b) p)).map
            (heatContribution w K
              (exposedInsertion (pairSteps (by omega) a b) r))) := by
  let steps := pairSteps (show 1 < tailBlocks+1 by omega) a b
  let tp := exposedInput steps p
  let tr := exposedInsertion steps r
  have htp : SupportedQuaternionBlocks (tailBlocks+1) tp :=
    applyQuaternionBlockSwapChain_supported steps p hp
  have htr : SupportedQuaternionBlocks (tailBlocks+1) tr :=
    applyQuaternionBlockSwapChain_supported steps r hr
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
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft)
    (Q'.eqv_trans _ _ _ hpin
      (polynomial_heat_pairing tailBlocks hb w K tp tr htp hrdeg))

/-- Arbitrary block count form, avoiding arithmetic casts in doubled carriers. -/
theorem selected_pair_expansion_at {blocks : Nat} (hb : 1 < blocks)
    (a b : Fin blocks) (hab : a.val ≠ b.val)
    (w : Q') (K : Nat) (p r : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p)
    (hr : SupportedQuaternionBlocks blocks r)
    (hdr : HasQuaternionBlockDegree a.val 0 r) :
    quaternionHaar blocks (polyMul (polyMul (heatAt a.val b.val w K) p) r) ≈
      qListSum
        ((modes blocks (by omega)
          (exposedInput (pairSteps hb a b) p)).map
            (heatContribution w K
              (exposedInsertion (pairSteps hb a b) r))) := by
  cases blocks with
  | zero => omega
  | succ tailBlocks =>
      exact selected_pair_expansion tailBlocks (by omega) a b hab w K p r hp hr hdr

/-- Remove one actual product-heat factor and expand its arbitrary lower input.
All other product factors and the arbitrary supported upper polynomial remain
inside the exposed insertion on the original doubled carrier. -/
theorem productHeat_selected_expansion {n : Nat} (i : Fin n)
    (w : Q') (K : Nat) (ids : List Nat)
    (hnot : i.val ∉ ids) (hids : ∀ j, j ∈ ids → j < n)
    (p g : RatPoly) (hp : SupportedQuaternionBlocks (n+n) p)
    (hg : SupportedQuaternionBlocks n g) :
    quaternionHaar (n+n)
      (polyMul (productHeat n w K (i.val::ids))
        (polyMul p (liftBoundary n g))) ≈
      qListSum
        ((modes (n+n) (by have := i.isLt; omega)
          (exposedInput (kineticPairSteps i) p)).map
            (heatContribution w K
              (exposedInsertion (kineticPairSteps i)
                (polyMul (productHeat n w K ids) (liftBoundary n g))))) := by
  have hn := i.isLt
  let a : Fin (n+n) := ⟨i.val, by omega⟩
  let b : Fin (n+n) := ⟨n+i.val, by omega⟩
  have hs := supported_polyMul (productHeat_supported n w K ids hids)
    (lift_supported hg n)
  have hz := (independent_has_degree_zero
      (productHeat_independent_lower n w K ids hids i.val i.isLt hnot)).mul
    (independent_has_degree_zero (lift_lower_independent n g i.val i.isLt))
  have h := selected_pair_expansion_at (by omega) a b
    (by change i.val ≠ n+i.val; omega) w K p
    (polyMul (productHeat n w K ids) (liftBoundary n g)) hp hs hz
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
  exact Q'.eqv_trans _ _ _ hleft h

/-- The same one-factor expansion for the actual lower product map.  The
remaining expression stays a doubled-carrier signed sum. -/
theorem productMap_selected_expansion {n : Nat} (i : Fin n)
    (w : Q') (K : Nat) (ids : List Nat)
    (hnot : i.val ∉ ids) (hids : ∀ j, j ∈ ids → j < n)
    (p g : RatPoly) (hp : SupportedQuaternionBlocks n p)
    (hg : SupportedQuaternionBlocks n g) :
    quaternionHaar n (polyMul g (productMap n w K (i.val::ids) p)) ≈
      qListSum
        ((modes (n+n) (by have := i.isLt; omega)
          (exposedInput (kineticPairSteps i) p)).map
            (heatContribution w K
              (exposedInsertion (kineticPairSteps i)
                (polyMul (productHeat n w K ids) (liftBoundary n g))))) := by
  have hp2 : SupportedQuaternionBlocks (n+n) p := fun term hterm =>
    Nat.le_trans (hp term hterm) (Nat.mul_le_mul_left 4 (by omega))
  exact Q'.eqv_trans _ _ _ (productMap_pairing n w K (i.val::ids) p g)
    (productHeat_selected_expansion i w K ids hnot hids p g hp2 hg)

end YMGap.Continuum.SU2QuaternionProductHeatHarmonicExpansion

#print axioms YMGap.Continuum.SU2QuaternionProductHeatHarmonicExpansion.selected_pair_expansion
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHarmonicExpansion.selected_pair_expansion_at
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHarmonicExpansion.productHeat_selected_expansion
#print axioms YMGap.Continuum.SU2QuaternionProductHeatHarmonicExpansion.productMap_selected_expansion
