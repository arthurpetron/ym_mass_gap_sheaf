/-
# Arbitrary-link propagation of the label-two plaquette character

Five distinct blocks are exposed as the selected lower link, its retained
heat partner, and the other three plaquette links.  The checked canonical
spin-two transmission is then transported back to the original carrier.
-/

import YMGap.Continuum.SU2QuaternionSpinTwoHeatTransmission
import YMGap.Continuum.SU2QuaternionOrientedWordSelection
import YMGap.Continuum.SU2QuaternionBlockSwapChainInverse
import YMGap.Continuum.SU2QuaternionSelectedHarmonicHeatTransmission

namespace YMGap.Continuum.SU2QuaternionSpinTwoPlaquettePropagation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
  (finitePolySum)
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionSpinTwoHeatImage
open YMGap.Continuum.SU2QuaternionFourBlockExposure
open YMGap.Continuum.SU2QuaternionFourBlockSelection
open YMGap.Continuum.SU2QuaternionOrientedWordSelection
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionSpinTwoHeatTransmission
open YMGap.Continuum.SU2QuaternionBlockSwapChainInverse
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.RGTransport (qpow)

local infix:50 " ≈ " => Q'.eqv

private theorem chain_add_local {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) (p q : RatPoly) :
    applyQuaternionBlockSwapChain steps (polyAdd p q) =
      polyAdd (applyQuaternionBlockSwapChain steps p)
        (applyQuaternionBlockSwapChain steps q) := by
  induction steps generalizing p q with
  | nil => rfl
  | cons s rest ih =>
      simp only [applyQuaternionBlockSwapChain,
        reindexQuaternionPolynomial_add, ih]

private theorem chain_smul_local {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) (scale : Q')
    (p : RatPoly) :
    applyQuaternionBlockSwapChain steps (polySmul scale p) =
      polySmul scale (applyQuaternionBlockSwapChain steps p) := by
  induction steps generalizing p with
  | nil => rfl
  | cons s rest ih =>
      simp only [applyQuaternionBlockSwapChain,
        reindexQuaternionPolynomial_smul, ih]

private theorem chain_zero_local {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks)) :
    applyQuaternionBlockSwapChain steps polyZero = polyZero := by
  induction steps with
  | nil => rfl
  | cons s rest ih => exact ih

private theorem scalar_exposed_of_pins {blocks lower upper : Nat}
    (steps : List (QuaternionBlockInvolution blocks))
    (hzero : quaternionBlockSwapChainSource steps 0 = lower)
    (hone : quaternionBlockSwapChainSource steps 1 = upper)
    (hblocks : 1 < blocks) :
    QuaternionPrefixPolynomialEqv blocks
      (applyQuaternionBlockSwapChain steps (scalarAt lower upper))
      relativeScalar := by
  have hp := (applyQuaternionBlockSwapChain_coordinateVariable_prefix steps
      (by omega) hzero).mul
    (applyQuaternionBlockSwapChain_coordinateVariable_prefix steps
      hblocks hone).conj
  rw [← applyQuaternionBlockSwapChainQuaternion_conj,
    ← applyQuaternionBlockSwapChainQuaternion_mul] at hp
  have hs := hp.scalar
  rw [applyQuaternionBlockSwapChainQuaternion_scalar] at hs
  exact hs

private theorem heat_exposed_of_pins {blocks lower upper : Nat}
    (steps : List (QuaternionBlockInvolution blocks))
    (hzero : quaternionBlockSwapChainSource steps 0 = lower)
    (hone : quaternionBlockSwapChainSource steps 1 = upper)
    (hblocks : 1 < blocks) (w : Q') (K : Nat) :
    PaddedPolynomialCoeffEqv blocks
      (applyQuaternionBlockSwapChain steps (heatAt lower upper w K))
      (relativeHeat w K) := by
  have hc (spin : Nat) : QuaternionPrefixPolynomialEqv blocks
      (applyQuaternionBlockSwapChain steps
        (characterPolynomial (scalarAt lower upper) spin))
      (relativeCharacter spin) :=
    (applyQuaternionBlockSwapChain_character_prefix steps _ spin).trans
      ((scalar_exposed_of_pins steps hzero hone hblocks).character spin)
  unfold heatAt relativeHeat
  induction List.range (K+1) with
  | nil =>
      rw [finitePolySum, chain_zero_local]
      exact .refl _ _
  | cons spin rest ih =>
      simp only [finitePolySum, chain_add_local, chain_smul_local]
      exact ((PaddedPolynomialCoeffEqv.of_prefix (hc spin)).smul _).add ih

/-- Deterministic five-slot chart: lower, upper, and the three other word
blocks are sent to `0,1,2,3,4`, respectively. -/
def fiveSlotSteps {blocks : Nat} (hb : 4 < blocks)
    (lower upper b c d : Fin blocks)
    (hlu : lower.val ≠ upper.val) (hlb : lower.val ≠ b.val)
    (hlc : lower.val ≠ c.val) (hub : upper.val ≠ b.val)
    (huc : upper.val ≠ c.val) (hbc : b.val ≠ c.val) :
    List (QuaternionBlockInvolution blocks) :=
  let e := fourBlockExposure (by omega) lower upper b c
    hlu hlb hlc hub huc hbc
  extend e.steps ⟨4, hb⟩ d

theorem fiveSlot_source_lower {blocks : Nat} (hb : 4 < blocks)
    (lower upper b c d : Fin blocks)
    (hlu : lower.val ≠ upper.val) (hlb : lower.val ≠ b.val)
    (hlc : lower.val ≠ c.val) (hub : upper.val ≠ b.val)
    (huc : upper.val ≠ c.val) (hbc : b.val ≠ c.val)
    (hld : lower.val ≠ d.val) :
    quaternionBlockSwapChainSource
      (fiveSlotSteps hb lower upper b c d hlu hlb hlc hub huc hbc) 0 =
      lower.val := by
  unfold fiveSlotSteps
  exact extend_preserves _ ⟨4, hb⟩ d
    (fourBlockExposure (by omega) lower upper b c
      hlu hlb hlc hub huc hbc).source_zero
    (by change (0 : Nat) ≠ 4; decide) hld

theorem fiveSlot_source_upper {blocks : Nat} (hb : 4 < blocks)
    (lower upper b c d : Fin blocks)
    (hlu : lower.val ≠ upper.val) (hlb : lower.val ≠ b.val)
    (hlc : lower.val ≠ c.val) (hub : upper.val ≠ b.val)
    (huc : upper.val ≠ c.val) (hbc : b.val ≠ c.val)
    (hud : upper.val ≠ d.val) :
    quaternionBlockSwapChainSource
      (fiveSlotSteps hb lower upper b c d hlu hlb hlc hub huc hbc) 1 =
      upper.val := by
  unfold fiveSlotSteps
  exact extend_preserves _ ⟨4, hb⟩ d
    (fourBlockExposure (by omega) lower upper b c
      hlu hlb hlc hub huc hbc).source_one
    (by change (1 : Nat) ≠ 4; decide) hud

theorem fiveSlot_source_b {blocks : Nat} (hb : 4 < blocks)
    (lower upper b c d : Fin blocks)
    (hlu : lower.val ≠ upper.val) (hlb : lower.val ≠ b.val)
    (hlc : lower.val ≠ c.val) (hub : upper.val ≠ b.val)
    (huc : upper.val ≠ c.val) (hbc : b.val ≠ c.val)
    (hbd : b.val ≠ d.val) :
    quaternionBlockSwapChainSource
      (fiveSlotSteps hb lower upper b c d hlu hlb hlc hub huc hbc) 2 = b.val := by
  unfold fiveSlotSteps
  exact extend_preserves _ ⟨4, hb⟩ d
    (fourBlockExposure (by omega) lower upper b c
      hlu hlb hlc hub huc hbc).source_two
    (by change (2 : Nat) ≠ 4; decide) hbd

theorem fiveSlot_source_c {blocks : Nat} (hb : 4 < blocks)
    (lower upper b c d : Fin blocks)
    (hlu : lower.val ≠ upper.val) (hlb : lower.val ≠ b.val)
    (hlc : lower.val ≠ c.val) (hub : upper.val ≠ b.val)
    (huc : upper.val ≠ c.val) (hbc : b.val ≠ c.val)
    (hcd : c.val ≠ d.val) :
    quaternionBlockSwapChainSource
      (fiveSlotSteps hb lower upper b c d hlu hlb hlc hub huc hbc) 3 = c.val := by
  unfold fiveSlotSteps
  exact extend_preserves _ ⟨4, hb⟩ d
    (fourBlockExposure (by omega) lower upper b c
      hlu hlb hlc hub huc hbc).source_three
    (by change (3 : Nat) ≠ 4; decide) hcd

theorem fiveSlot_source_d {blocks : Nat} (hb : 4 < blocks)
    (lower upper b c d : Fin blocks)
    (hlu : lower.val ≠ upper.val) (hlb : lower.val ≠ b.val)
    (hlc : lower.val ≠ c.val) (hub : upper.val ≠ b.val)
    (huc : upper.val ≠ c.val) (hbc : b.val ≠ c.val) :
    quaternionBlockSwapChainSource
      (fiveSlotSteps hb lower upper b c d hlu hlb hlc hub huc hbc) 4 = d.val := by
  unfold fiveSlotSteps
  exact extend_source _ ⟨4, hb⟩ d

/-- The actual output polynomial after undoing the deterministic chart. -/
def propagatedSpinTwoCharacter {blocks : Nat}
    (steps : List (QuaternionBlockInvolution blocks))
    (r0 r1 r2 r3 : Bool) : RatPoly :=
  applyQuaternionBlockSwapChain steps.reverse
    (liftHead (characterPolynomial
      (exposedFourWord r0 r1 r2 r3).scalar 2))

theorem inputCharacter_prefix {blocks : Nat} (hb : 4 < blocks)
    (lower upper b c d : Fin blocks)
    (hlu : lower.val ≠ upper.val) (hlb : lower.val ≠ b.val)
    (hlc : lower.val ≠ c.val) (hub : upper.val ≠ b.val)
    (huc : upper.val ≠ c.val) (hbc : b.val ≠ c.val)
    (hld : lower.val ≠ d.val) (hbd : b.val ≠ d.val)
    (hcd : c.val ≠ d.val) (r0 r1 r2 r3 : Bool) :
    QuaternionPrefixPolynomialEqv blocks
      (applyQuaternionBlockSwapChain
        (fiveSlotSteps hb lower upper b c d hlu hlb hlc hub huc hbc)
        (characterPolynomial
          (word lower.val b.val c.val d.val r0 r1 r2 r3).scalar 2))
      (characterPolynomial (selectedWord r0 r1 r2 r3).scalar 2) := by
  let steps := fiveSlotSteps hb lower upper b c d hlu hlb hlc hub huc hbc
  have hq : QuaternionPrefixPolyQuaternionEqv blocks
      (applyQuaternionBlockSwapChainQuaternion steps
        (word lower.val b.val c.val d.val r0 r1 r2 r3))
      (selectedWord r0 r1 r2 r3) := by
    unfold word selectedWord
    rw [applyQuaternionBlockSwapChainQuaternion_mul,
      applyQuaternionBlockSwapChainQuaternion_mul,
      applyQuaternionBlockSwapChainQuaternion_mul]
    exact (((applyQuaternionBlockSwapChain_orientedCoordinate_prefix steps
      (by omega) (fiveSlot_source_lower hb lower upper b c d
        hlu hlb hlc hub huc hbc hld) r0).mul
      (applyQuaternionBlockSwapChain_orientedCoordinate_prefix steps
        (by omega) (fiveSlot_source_b hb lower upper b c d
          hlu hlb hlc hub huc hbc hbd) r1)).mul
      (applyQuaternionBlockSwapChain_orientedCoordinate_prefix steps
        (by omega) (fiveSlot_source_c hb lower upper b c d
          hlu hlb hlc hub huc hbc hcd) r2)).mul
      (applyQuaternionBlockSwapChain_orientedCoordinate_prefix steps
        hb (fiveSlot_source_d hb lower upper b c d
          hlu hlb hlc hub huc hbc) r3)
  have hs := hq.scalar
  rw [applyQuaternionBlockSwapChainQuaternion_scalar] at hs
  exact (applyQuaternionBlockSwapChain_character_prefix steps _ 2).trans
    (hs.character 2)

/-- One arbitrary selected lower/upper heat factor propagates the actual
label-two plaquette character. Every other factor remains in the supported
spectator `r`; only the selected lower block is required independent there. -/
theorem spinTwoPlaquette_heat_pairing
    (tail : Nat) (htail : 4 ≤ tail)
    (lower upper b c d : Fin (tail+1))
    (hlu : lower.val ≠ upper.val) (hlb : lower.val ≠ b.val)
    (hlc : lower.val ≠ c.val) (hub : upper.val ≠ b.val)
    (huc : upper.val ≠ c.val) (hbc : b.val ≠ c.val)
    (hld : lower.val ≠ d.val) (hud : upper.val ≠ d.val)
    (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val)
    (r0 r1 r2 r3 : Bool) (w : Q') (K : Nat) (hK : 2 ≤ K)
    (r : RatPoly) (hr : SupportedQuaternionBlocks (tail+1) r)
    (hindependent : HasQuaternionBlockDegree lower.val 0 r) :
    quaternionHaar (tail+1)
      (polyMul
        (polyMul (heatAt lower.val upper.val w K)
          (characterPolynomial
            (word lower.val b.val c.val d.val r0 r1 r2 r3).scalar 2)) r) ≈
      qpow w 8 * quaternionHaar (tail+1)
        (polyMul
          (propagatedSpinTwoCharacter
            (fiveSlotSteps (by omega) lower upper b c d
              hlu hlb hlc hub huc hbc) r0 r1 r2 r3) r) := by
  let steps := fiveSlotSteps (show 4 < tail+1 by omega)
    lower upper b c d hlu hlb hlc hub huc hbc
  let input := characterPolynomial
    (word lower.val b.val c.val d.val r0 r1 r2 r3).scalar 2
  let tr := applyQuaternionBlockSwapChain steps r
  have hinput : SupportedQuaternionBlocks (tail+1) input :=
    word_supported lower.isLt b.isLt c.isLt d.isLt r0 r1 r2 r3 2
  have htr : SupportedQuaternionBlocks (tail+1) tr :=
    applyQuaternionBlockSwapChain_supported steps r hr
  have htrDegree : HasQuaternionBlockDegree 0 0 tr := by
    apply chain_degree steps (by omega)
    rw [fiveSlot_source_lower (by omega) lower upper b c d
      hlu hlb hlc hub huc hbc hld]
    exact hindependent
  have htrIndependent : HeadQuaternionIndependent tr := htrDegree
  have hheat := heat_supported lower.isLt upper.isLt w K
  have hrelative := heat_supported (show 0 < tail+1 by omega)
    (show 1 < tail+1 by omega) w K
  have hselected : SupportedQuaternionBlocks (tail+1)
      (characterPolynomial (selectedWord r0 r1 r2 r3).scalar 2) :=
    word_supported (by omega) (by omega) (by omega) (by omega)
      r0 r1 r2 r3 2
  have hleft := quaternionHaar_applyQuaternionBlockSwapChain steps _
    (supported_polyMul (supported_polyMul hheat hinput) hr)
  rw [chain_mul, chain_mul] at hleft
  have hpin := (((heat_exposed_of_pins steps
      (fiveSlot_source_lower (by omega) lower upper b c d
        hlu hlb hlc hub huc hbc hld)
      (fiveSlot_source_upper (by omega) lower upper b c d
        hlu hlb hlc hub huc hbc hud)
      (by omega) w K).mul
      (PaddedPolynomialCoeffEqv.of_prefix
        (inputCharacter_prefix (by omega) lower upper b c d
          hlu hlb hlc hub huc hbc hld hbd hcd r0 r1 r2 r3))).mul
      (PaddedPolynomialCoeffEqv.refl (tail+1) tr)).haar
    (supported_polyMul
      (supported_polyMul
        (applyQuaternionBlockSwapChain_supported steps _ hheat)
        (applyQuaternionBlockSwapChain_supported steps _ hinput)) htr)
    (supported_polyMul (supported_polyMul hrelative hselected) htr)
  have hcanonical := selectedCharacterTwo_heat_pairing tail htail
    r0 r1 r2 r3 w K hK tr htr htrIndependent
  let exposed := liftHead
    (characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar 2)
  have hexposed : SupportedQuaternionBlocks (tail+1) exposed := by
    have h4 : SupportedQuaternionBlocks 4
        (characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar 2) :=
      word_supported (by omega) (by omega) (by omega) (by omega)
        r0 r1 r2 r3 2
    have h5 : SupportedQuaternionBlocks 5 exposed := by
      simpa only [liftBoundary] using
        (lift_supported h4 1)
    intro term hterm
    exact Nat.le_trans (h5 term hterm) (by omega)
  have hpropagated : SupportedQuaternionBlocks (tail+1)
      (propagatedSpinTwoCharacter steps r0 r1 r2 r3) :=
    reverse_chain_supported steps exposed hexposed
  have hright := quaternionHaar_applyQuaternionBlockSwapChain steps _
    (supported_polyMul hpropagated hr)
  rw [chain_mul] at hright
  have hrightPin := quaternionHaar_prefixPolynomialEqv (tail+1)
    ((apply_reverse_inverse_prefix steps exposed).mul
      (QuaternionPrefixPolynomialEqv.refl (tail+1) tr))
    (supported_polyMul
      (applyQuaternionBlockSwapChain_supported steps _ hpropagated) htr)
    (supported_polyMul hexposed htr)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft)
    (Q'.eqv_trans _ _ _ hpin
      (Q'.eqv_trans _ _ _ hcanonical
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _ (Q'.eqv_symm hrightPin) hright))))

end YMGap.Continuum.SU2QuaternionSpinTwoPlaquettePropagation

#print axioms YMGap.Continuum.SU2QuaternionSpinTwoPlaquettePropagation.fiveSlot_source_lower
#print axioms YMGap.Continuum.SU2QuaternionSpinTwoPlaquettePropagation.fiveSlot_source_upper
#print axioms YMGap.Continuum.SU2QuaternionSpinTwoPlaquettePropagation.fiveSlot_source_b
#print axioms YMGap.Continuum.SU2QuaternionSpinTwoPlaquettePropagation.fiveSlot_source_c
#print axioms YMGap.Continuum.SU2QuaternionSpinTwoPlaquettePropagation.fiveSlot_source_d
#print axioms YMGap.Continuum.SU2QuaternionSpinTwoPlaquettePropagation.inputCharacter_prefix
#print axioms YMGap.Continuum.SU2QuaternionSpinTwoPlaquettePropagation.spinTwoPlaquette_heat_pairing
