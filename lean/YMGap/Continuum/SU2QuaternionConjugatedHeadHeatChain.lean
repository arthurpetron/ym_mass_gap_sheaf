/-
# Conjugated head heat along a finite block-swap chain

The selected-pair exposure uses two block involutions, so a single
involution-conjugation is not the right operator shape.  This module defines
the inverse-chain conjugate of the literal head update and proves its finite
Haar defect bound.  It is an algebraic carrier theorem: it does not identify
the operator with the interacting selected-link kernel or supply a telescope.
-/

import YMGap.Continuum.SU2QuaternionConjugatedHeadHeat
import YMGap.Continuum.SU2QuaternionBlockSwapChainInverse
import YMGap.Continuum.SU2QuaternionFourBlockSelection
import YMGap.Continuum.SU2QuaternionAngularReindex
import YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry

namespace YMGap.Continuum.SU2QuaternionConjugatedHeadHeatChain

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionBlockSwapChainInverse
open YMGap.Continuum.SU2QuaternionConjugatedHeadHeat
open YMGap.Continuum.SU2QuaternionFourBlockSelection
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionHeadHeatDiagonal
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.SU2HeatCutoffCasimirBound

local infix:50 " ≈ " => Q'.eqv

/-- Apply the literal head update in the exposed chart and transport it back
through the inverse of the exposing block-swap chain. -/
def chainConjugatedHeadMap
    {tail : Nat}
    (steps : List (QuaternionBlockInvolution (tail + 1)))
    (w : Q') (K : Nat) (polynomial : RatPoly) : RatPoly :=
  applyQuaternionBlockSwapChain steps.reverse
    (headMap w K (applyQuaternionBlockSwapChain steps polynomial))

theorem chainConjugatedHeadMap_supported
    {tail : Nat}
    (steps : List (QuaternionBlockInvolution (tail + 1)))
    (w : Q') (K : Nat) {polynomial : RatPoly}
    (hpolynomial : SupportedQuaternionBlocks (tail + 1) polynomial) :
    SupportedQuaternionBlocks (tail + 1)
      (chainConjugatedHeadMap steps w K polynomial) := by
  apply applyQuaternionBlockSwapChain_supported
  exact headMap_supported tail w K
    (applyQuaternionBlockSwapChain_supported steps polynomial hpolynomial)

/-- The inverse-chain conjugate has the same Haar pairing as the head update
in the exposed chart.  The proof uses only finite reindexing and the checked
reverse-chain cancellation theorem. -/
theorem chainConjugatedHeadMap_pairing
    (tail : Nat) (w : Q') (K : Nat)
    (steps : List (QuaternionBlockInvolution (tail + 1)))
    (polynomial : RatPoly)
    (hpolynomial : SupportedQuaternionBlocks (tail + 1) polynomial) :
    quaternionHaar (tail + 1)
        (polyMul polynomial (chainConjugatedHeadMap steps w K polynomial)) ≈
      quaternionHaar (tail + 1)
        (polyMul (applyQuaternionBlockSwapChain steps polynomial)
          (headMap w K (applyQuaternionBlockSwapChain steps polynomial))) := by
  let recoded := applyQuaternionBlockSwapChain steps polynomial
  let head := headMap w K recoded
  have hrecoded : SupportedQuaternionBlocks (tail + 1) recoded :=
    applyQuaternionBlockSwapChain_supported steps polynomial hpolynomial
  have hhead : SupportedQuaternionBlocks (tail + 1) head := by
    exact headMap_supported tail w K hrecoded
  have hinv : SupportedQuaternionBlocks (tail + 1)
      (applyQuaternionBlockSwapChain steps.reverse head) :=
    reverse_chain_supported steps head hhead
  have hproduct : SupportedQuaternionBlocks (tail + 1)
      (polyMul polynomial (applyQuaternionBlockSwapChain steps.reverse head)) :=
    supported_polyMul hpolynomial hinv
  have hforward := quaternionHaar_applyQuaternionBlockSwapChain steps
    (polyMul polynomial (applyQuaternionBlockSwapChain steps.reverse head))
    hproduct
  rw [chain_mul] at hforward
  have hcancel := apply_reverse_inverse_haar steps head recoded hhead hrecoded
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hforward)
    (by simpa [recoded, head] using hcancel)

/-- Finite local defect bound for an arbitrary exposing chain.  The energy is
left in the exposed chart, where the existing angular theorem applies without
assuming that differentiation commutes with a multi-step recoding. -/
theorem chainConjugatedHeadMap_defect_le_angular
    (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K)
    (steps : List (QuaternionBlockInvolution (tail + 1)))
    (polynomial : RatPoly)
    (hpolynomial : SupportedQuaternionBlocks (tail + 1) polynomial) :
    quaternionHaar (tail + 1) (polyMul polynomial polynomial) -
        quaternionHaar (tail + 1)
          (polyMul polynomial (chainConjugatedHeadMap steps w K polynomial)) ≤
      ((1 : Q') - w) *
        quaternionHaar (tail + 1)
          (angularSquare (applyQuaternionBlockSwapChain steps polynomial)) := by
  let recoded := applyQuaternionBlockSwapChain steps polynomial
  let head := headMap w K recoded
  have hrecoded : SupportedQuaternionBlocks (tail + 1) recoded :=
    applyQuaternionBlockSwapChain_supported steps polynomial hpolynomial
  have hnorm :
      quaternionHaar (tail + 1) (polyMul polynomial polynomial) ≈
        quaternionHaar (tail + 1) (polyMul recoded recoded) := by
    have hchange := quaternionHaar_applyQuaternionBlockSwapChain steps
      (polyMul polynomial polynomial)
      (supported_polyMul hpolynomial hpolynomial)
    rw [chain_mul] at hchange
    exact Q'.eqv_symm hchange
  have hcross :
      quaternionHaar (tail + 1)
          (polyMul polynomial (chainConjugatedHeadMap steps w K polynomial)) ≈
        quaternionHaar (tail + 1) (polyMul recoded head) := by
    exact chainConjugatedHeadMap_pairing tail w K steps polynomial hpolynomial
  have hleft :
      quaternionHaar (tail + 1) (polyMul polynomial polynomial) -
          quaternionHaar (tail + 1)
            (polyMul polynomial (chainConjugatedHeadMap steps w K polynomial)) ≈
        quaternionHaar (tail + 1) (polyMul recoded recoded) -
          quaternionHaar (tail + 1) (polyMul recoded head) := by
    exact Q'.add_eqv_congr' hnorm (Q'.neg_eqv_congr _ _ hcross)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hleft)
    (headMap_defect_le_angular tail hw0 hw1 K hK recoded hrecoded)

/-- The exposed-chart angular energy can be transported back to the original
source block of an arbitrary swap chain.  The source map is the same
contravariant map used by the finite exposure certificates. -/
theorem chain_blockAngularSquare_haar
    {tail : Nat} :
    ∀ (steps : List (QuaternionBlockInvolution (tail + 1)))
      (block : Nat), block < tail + 1 → ∀ (polynomial : RatPoly),
      SupportedQuaternionBlocks (tail + 1) polynomial →
      quaternionHaar (tail + 1)
          (blockAngularSquare block
            (applyQuaternionBlockSwapChain steps polynomial)) ≈
        quaternionHaar (tail + 1)
          (blockAngularSquare
            (quaternionBlockSwapChainSource steps block) polynomial)
  | [], block, hblock, polynomial, hpolynomial => Q'.eqv_refl _
  | swap :: rest, block, hblock, polynomial, hpolynomial => by
      let recoded := reindexQuaternionPolynomial swap polynomial
      have hsourceRest :
          quaternionBlockSwapChainSource rest block < tail + 1 := by
        exact quaternionBlockSwapChainSource_lt rest hblock
      have hrecoded : SupportedQuaternionBlocks (tail + 1) recoded :=
        reindex_supported swap polynomial
      have hrest := chain_blockAngularSquare_haar rest block hblock recoded hrecoded
      have hone := reindex_blockAngularSquare_haar swap hsourceRest polynomial
      have hdrop := quaternionHaar_reindex swap
        (blockAngularSquare
          (swap.map (quaternionBlockSwapChainSource rest block)) polynomial)
        (blockAngularSquare_supported
          (swap.map_lt _ hsourceRest) hpolynomial)
      exact Q'.eqv_trans _ _ _ hrest
        (Q'.eqv_trans _ _ _ (Q'.eqv_symm hone) hdrop)

/-- Specialize the chain estimate to the explicit selected/multiplier
exposure.  The result is already expressed in the original selected-block
energy; identifying this recoded map with the independently defined
interacting selected-link update remains a separate bridge. -/
theorem translationPair_chain_defect_le_selected_block_energy
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (polynomial : RatPoly)
    (hpolynomial : SupportedQuaternionBlocks (tailBlocks + 1) polynomial) :
    quaternionHaar (tailBlocks + 1) (polyMul polynomial polynomial) -
        quaternionHaar (tailBlocks + 1)
          (polyMul polynomial
            (chainConjugatedHeadMap
              (pairSteps (by omega)
                ⟨selected, hselected⟩ ⟨multiplier, hmultiplier⟩)
              w K polynomial)) ≤
      ((1 : Q') - w) *
        quaternionHaar (tailBlocks + 1)
          (blockAngularSquare selected polynomial) := by
  let steps := pairSteps (show 1 < tailBlocks + 1 by omega)
    ⟨selected, hselected⟩ ⟨multiplier, hmultiplier⟩
  have hdef := chainConjugatedHeadMap_defect_le_angular tailBlocks
    hw0 hw1 K hK steps polynomial hpolynomial
  have hangular := chain_blockAngularSquare_haar steps 0 (by omega)
    polynomial hpolynomial
  have hsource := pair_zero (show 1 < tailBlocks + 1 by omega)
    ⟨selected, hselected⟩ ⟨multiplier, hmultiplier⟩ hdistinct
  rw [hsource] at hangular
  have hangular' :
      quaternionHaar (tailBlocks + 1)
          (angularSquare (applyQuaternionBlockSwapChain steps polynomial)) ≈
        quaternionHaar (tailBlocks + 1)
          (blockAngularSquare selected polynomial) := by
    simpa [angularSquare] using hangular
  exact Q'.le_trans' _ _ _ hdef
    (Q'.le_of_eqv
      (Q'.mul_eqv_congr_left ((1 : Q') - w) _ _ hangular'))

end YMGap.Continuum.SU2QuaternionConjugatedHeadHeatChain

#print axioms YMGap.Continuum.SU2QuaternionConjugatedHeadHeatChain.chainConjugatedHeadMap
#print axioms YMGap.Continuum.SU2QuaternionConjugatedHeadHeatChain.chainConjugatedHeadMap_supported
#print axioms YMGap.Continuum.SU2QuaternionConjugatedHeadHeatChain.chainConjugatedHeadMap_pairing
#print axioms YMGap.Continuum.SU2QuaternionConjugatedHeadHeatChain.chainConjugatedHeadMap_defect_le_angular
#print axioms YMGap.Continuum.SU2QuaternionConjugatedHeadHeatChain.chain_blockAngularSquare_haar
#print axioms YMGap.Continuum.SU2QuaternionConjugatedHeadHeatChain.translationPair_chain_defect_le_selected_block_energy
