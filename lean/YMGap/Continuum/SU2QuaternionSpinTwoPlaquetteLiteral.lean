/-
# Literal retained plaquette after arbitrary-link heat transmission

Undoing the five-slot chart gives the original ordered word with just the
selected lower link replaced by its actual upper partner. Character lifting
uses common-padding equality; the supported Haar test is never discarded.
-/

import YMGap.Continuum.SU2QuaternionSpinTwoPlaquettePropagation
import YMGap.Continuum.QuaternionHaarWordLift

namespace YMGap.Continuum.SU2QuaternionSpinTwoPlaquetteLiteral

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionFourBlockSelection
open YMGap.Continuum.SU2QuaternionOrientedWordSelection
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionBlockSwapChainInverse
open YMGap.Continuum.SU2QuaternionSpinTwoPlaquettePropagation
open YMGap.Continuum.QuaternionHaarWordLift
open YMGap.Continuum.RGTransport (qpow)

local infix:50 " ≈ " => Q'.eqv

/-- Adjoining blocks shifts the ordered word exactly at scalar level. -/
theorem lift_word_scalar (shift a b c d : Nat) (r0 r1 r2 r3 : Bool) :
    liftBoundary shift (word a b c d r0 r1 r2 r3).scalar =
      (word (shift+a) (shift+b) (shift+c) (shift+d) r0 r1 r2 r3).scalar := by
  have hc (i : Nat) (r : Bool) :
      liftQuaternion shift (orientedCoordinateQuaternion i r) =
        orientedCoordinateQuaternion (shift+i) r := by
    cases r
    · exact liftQuaternion_coordinateVariable shift i
    · exact (liftQuaternion_conj shift _).trans
        (congrArg PolyQuaternion.conj (liftQuaternion_coordinateVariable shift i))
  change (liftQuaternion shift (word a b c d r0 r1 r2 r3)).scalar = _
  unfold word
  simp only [liftQuaternion_mul, hc]

/-- The constant term of a character retains its honest common padding. -/
theorem lift_word_character (blocks shift a b c d : Nat)
    (r0 r1 r2 r3 : Bool) (label : Nat) :
    PaddedPolynomialCoeffEqv blocks
      (liftBoundary shift (characterPolynomial (word a b c d r0 r1 r2 r3).scalar label))
      (characterPolynomial
        (word (shift+a) (shift+b) (shift+c) (shift+d) r0 r1 r2 r3).scalar label) := by
  have h := lift_character blocks shift (word a b c d r0 r1 r2 r3).scalar label
  rw [lift_word_scalar] at h
  exact h

private theorem output_forward {blocks : Nat} (hb : 4 < blocks)
    (steps : List (QuaternionBlockInvolution blocks)) (u b c d : Fin blocks)
    (h1 : quaternionBlockSwapChainSource steps 1 = u.val)
    (h2 : quaternionBlockSwapChainSource steps 2 = b.val)
    (h3 : quaternionBlockSwapChainSource steps 3 = c.val)
    (h4 : quaternionBlockSwapChainSource steps 4 = d.val)
    (r0 r1 r2 r3 : Bool) :
    PaddedPolynomialCoeffEqv blocks
      (applyQuaternionBlockSwapChain steps
        (characterPolynomial (word u.val b.val c.val d.val r0 r1 r2 r3).scalar 2))
      (liftHead (characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar 2)) := by
  have hq : QuaternionPrefixPolyQuaternionEqv blocks
      (applyQuaternionBlockSwapChainQuaternion steps
        (word u.val b.val c.val d.val r0 r1 r2 r3))
      (word 1 2 3 4 r0 r1 r2 r3) := by
    unfold word
    rw [applyQuaternionBlockSwapChainQuaternion_mul,
      applyQuaternionBlockSwapChainQuaternion_mul,
      applyQuaternionBlockSwapChainQuaternion_mul]
    exact (((applyQuaternionBlockSwapChain_orientedCoordinate_prefix steps
      (by omega) h1 r0).mul
      (applyQuaternionBlockSwapChain_orientedCoordinate_prefix steps (by omega) h2 r1)).mul
      (applyQuaternionBlockSwapChain_orientedCoordinate_prefix steps (by omega) h3 r2)).mul
      (applyQuaternionBlockSwapChain_orientedCoordinate_prefix steps hb h4 r3)
  have hs := hq.scalar
  rw [applyQuaternionBlockSwapChainQuaternion_scalar] at hs
  have hchar := (applyQuaternionBlockSwapChain_character_prefix steps _ 2).trans
    (hs.character 2)
  have hlift : PaddedPolynomialCoeffEqv blocks
      (liftHead (characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar 2))
      (characterPolynomial (word 1 2 3 4 r0 r1 r2 r3).scalar 2) :=
    lift_word_character blocks 1 0 1 2 3 r0 r1 r2 r3 2
  exact (PaddedPolynomialCoeffEqv.of_prefix hchar).trans hlift.symm

/-- The computed reverse-chart output equals the literal retained word under
every supported Haar test on the original carrier. -/
theorem propagated_character_pairing {blocks : Nat} (hb : 4 < blocks)
    (steps : List (QuaternionBlockInvolution blocks)) (u b c d : Fin blocks)
    (h1 : quaternionBlockSwapChainSource steps 1 = u.val)
    (h2 : quaternionBlockSwapChainSource steps 2 = b.val)
    (h3 : quaternionBlockSwapChainSource steps 3 = c.val)
    (h4 : quaternionBlockSwapChainSource steps 4 = d.val)
    (r0 r1 r2 r3 : Bool) (r : RatPoly) (hr : SupportedQuaternionBlocks blocks r) :
    quaternionHaar blocks (polyMul (propagatedSpinTwoCharacter steps r0 r1 r2 r3) r) ≈
      quaternionHaar blocks (polyMul
        (characterPolynomial (word u.val b.val c.val d.val r0 r1 r2 r3).scalar 2) r) := by
  let out := liftHead (characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar 2)
  let target := characterPolynomial (word u.val b.val c.val d.val r0 r1 r2 r3).scalar 2
  let tr := applyQuaternionBlockSwapChain steps r
  have hout : SupportedQuaternionBlocks blocks out := by
    have hbase : SupportedQuaternionBlocks 4
        (characterPolynomial (exposedFourWord r0 r1 r2 r3).scalar 2) :=
      word_supported (by omega) (by omega) (by omega) (by omega) r0 r1 r2 r3 2
    have hfive := lift_supported hbase 1
    intro t ht
    exact Nat.le_trans (hfive t ht) (by omega)
  have hp := reverse_chain_supported steps out hout
  have ht : SupportedQuaternionBlocks blocks target :=
    word_supported u.isLt b.isLt c.isLt d.isLt r0 r1 r2 r3 2
  have htr := applyQuaternionBlockSwapChain_supported steps r hr
  have hP := quaternionHaar_applyQuaternionBlockSwapChain steps _ (supported_polyMul hp hr)
  have hT := quaternionHaar_applyQuaternionBlockSwapChain steps _ (supported_polyMul ht hr)
  rw [chain_mul] at hP hT
  have hPinP := quaternionHaar_prefixPolynomialEqv blocks
    ((apply_reverse_inverse_prefix steps out).mul (QuaternionPrefixPolynomialEqv.refl blocks tr))
    (supported_polyMul (applyQuaternionBlockSwapChain_supported steps _ hp) htr)
    (supported_polyMul hout htr)
  have hPinT := ((output_forward hb steps u b c d h1 h2 h3 h4 r0 r1 r2 r3).mul
    (PaddedPolynomialCoeffEqv.refl blocks tr)).haar
    (supported_polyMul (applyQuaternionBlockSwapChain_supported steps target ht) htr)
    (supported_polyMul hout htr)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hP)
    (Q'.eqv_trans _ _ _ hPinP (Q'.eqv_trans _ _ _ (Q'.eqv_symm hPinT) hT))

/-- Actual one-link character propagation, with the original word order and
only the selected lower link replaced by its upper partner. -/
theorem spinTwoPlaquette_literal_heat_pairing
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
      (polyMul (polyMul (heatAt lower.val upper.val w K)
        (characterPolynomial (word lower.val b.val c.val d.val r0 r1 r2 r3).scalar 2)) r) ≈
      qpow w 8 * quaternionHaar (tail+1)
        (polyMul (characterPolynomial
          (word upper.val b.val c.val d.val r0 r1 r2 r3).scalar 2) r) := by
  exact Q'.eqv_trans _ _ _
    (spinTwoPlaquette_heat_pairing tail htail lower upper b c d
      hlu hlb hlc hub huc hbc hld hud hbd hcd r0 r1 r2 r3 w K hK r hr hindependent)
    (Q'.mul_eqv_congr_left _ _ _
      (propagated_character_pairing (by omega) _ upper b c d
        (fiveSlot_source_upper (by omega) lower upper b c d hlu hlb hlc hub huc hbc hud)
        (fiveSlot_source_b (by omega) lower upper b c d hlu hlb hlc hub huc hbc hbd)
        (fiveSlot_source_c (by omega) lower upper b c d hlu hlb hlc hub huc hbc hcd)
        (fiveSlot_source_d (by omega) lower upper b c d hlu hlb hlc hub huc hbc)
        r0 r1 r2 r3 r hr))

end YMGap.Continuum.SU2QuaternionSpinTwoPlaquetteLiteral

#print axioms YMGap.Continuum.SU2QuaternionSpinTwoPlaquetteLiteral.lift_word_scalar
#print axioms YMGap.Continuum.SU2QuaternionSpinTwoPlaquetteLiteral.lift_word_character
#print axioms YMGap.Continuum.SU2QuaternionSpinTwoPlaquetteLiteral.propagated_character_pairing
#print axioms YMGap.Continuum.SU2QuaternionSpinTwoPlaquetteLiteral.spinTwoPlaquette_literal_heat_pairing
