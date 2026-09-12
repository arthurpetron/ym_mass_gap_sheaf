/-
# The full temporal ledger fixes actual lower and fixed links

Every generated step selects an upper link. The arbitrary-index shear pin
therefore composes through the WHOLE concrete ledger on each non-upper
coordinate. This matches the existing upperTemporalLink assignment on the
lower/fixed carrier, not just on one elementary step. Coefficient equality
is stated after explicit identity reindexing so empty ledgers are covered.

The upper-link image, same-observable global substitution and reflected-square
gluing remain open. No slab reflection-positivity or physical gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger

namespace YMGap.Continuum.BF4ExactSlabTemporalGaugeFixedCoordinates

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionSelectedTranslationCoordinates
open YMGap.Continuum.SU2QuaternionInverseTranslationCoordinates
open YMGap.Continuum.SU2QuaternionTranslationCoordinateCoefficients
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

/-- Any chain that never selects a given coordinate fixes that coordinate,
even when it uses the coordinate as a multiplier. -/
theorem applySteps_fixes_coordinate {tailBlocks : Nat} (hb : 0 < tailBlocks)
    (block : Nat) (hblock : block < tailBlocks + 1) :
    ∀ steps : List (SelectedTranslationStep tailBlocks),
      (∀ step, step ∈ steps → block ≠ step.selected) →
      QuaternionPrefixPolyQuaternionEqv (tailBlocks + 1)
        (applySelectedTranslationStepsQuaternion hb steps (PolyQuaternion.coordinateVariable block))
        (PolyQuaternion.coordinateVariable block)
  | [], _ => QuaternionPrefixPolyQuaternionEqv.refl _ _
  | step :: rest, hn => by
      have hstep := applySelectedTranslationStep_coordinate hb step block hblock
      rw [coordinateImage, if_neg (hn step List.mem_cons_self)] at hstep
      exact (applySelectedTranslationStepsQuaternion_prefix hb rest hstep).trans
        (applySteps_fixes_coordinate hb block hblock rest
          (fun s hs => hn s (List.mem_cons_of_mem step hs)))

def applyTemporalLedgerQuaternion (extent half : Nat) (q : PolyQuaternion) : PolyQuaternion :=
  applySelectedTranslationStepsQuaternion (temporalTailBlocks_pos extent) (temporalTranslationSteps extent half) q

/-- Complete concrete-ledger action on every physical non-upper link. -/
theorem temporalLedger_nonupper_link {extent half : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) (hn : linkHalfSide half link ≠ .upper) :
    QuaternionPrefixPolyQuaternionEqv (boundaryCompleteSlabLinks extent).length
      (applyTemporalLedgerQuaternion extent half (correctedSlabLinkPolynomial extent link))
      (correctedSlabLinkPolynomial extent link) := by
  have hi : (boundaryCompleteSlabLinks extent).idxOf link < temporalTailBlocks extent + 1 := by
    rw [temporalTotalBlocks_eq]
    exact List.idxOf_lt_length_of_mem hl
  have h := applySteps_fixes_coordinate (temporalTailBlocks_pos extent) _ hi
    (temporalTranslationSteps extent half) (fun _ hs => temporalTranslationSteps_not_selected hl hn hs)
  rw [temporalTotalBlocks_eq] at h
  simpa only [applyTemporalLedgerQuaternion, correctedSlabLinkPolynomial_of_mem hl] using h

/-- The full ledger is already identified with the COMMON temporal assignment
on the lower/fixed physical link carrier. -/
theorem temporalLedger_nonupper_assignment {extent half : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) (hn : linkHalfSide half link ≠ .upper) :
    QuaternionPrefixPolyQuaternionEqv (boundaryCompleteSlabLinks extent).length
      (applyTemporalLedgerQuaternion extent half (correctedSlabLinkPolynomial extent link))
      (upperTemporalLink extent half link) := by
  rw [upperTemporalLink, if_neg hn]
  exact temporalLedger_nonupper_link hl hn

/-- Common reindexing turns termwise prefix agreement into full coefficient
agreement, with no premise about the original padding lengths. -/
theorem reindex_prefix_coeffEqv {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    {p q : PolyQuaternion} (h : QuaternionPrefixPolyQuaternionEqv blocks p q) :
    PolyQuaternionCoeffEqv (reindexPolyQuaternion permutation p) (reindexPolyQuaternion permutation q) := by
  have lift {r s : YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier.RatPoly}
      (he : QuaternionPrefixPolynomialEqv blocks r s) :
      RatPolyCoeffEqv (reindexQuaternionPolynomial permutation r) (reindexQuaternionPolynomial permutation s) :=
    prefix_coeffEqv_of_lengths (QuaternionPrefixPolynomialEqv.reindex permutation he)
      (reindex_term_length permutation r) (reindex_term_length permutation s)
  exact ⟨lift h.scalar, lift h.iPart, lift h.jPart, lift h.kPart⟩

/-- Coefficient-level non-upper assignment pin, including empty ledgers. -/
theorem temporalLedger_nonupper_assignment_coeffEqv {extent half : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) (hn : linkHalfSide half link ≠ .upper) :
    PolyQuaternionCoeffEqv
      (reindexPolyQuaternion (identityQuaternionBlockInvolution (boundaryCompleteSlabLinks extent).length)
        (applyTemporalLedgerQuaternion extent half (correctedSlabLinkPolynomial extent link)))
      (reindexPolyQuaternion (identityQuaternionBlockInvolution (boundaryCompleteSlabLinks extent).length)
        (upperTemporalLink extent half link)) :=
  reindex_prefix_coeffEqv _ (temporalLedger_nonupper_assignment hl hn)

end YMGap.Continuum.BF4ExactSlabTemporalGaugeFixedCoordinates

#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeFixedCoordinates.applySteps_fixes_coordinate
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeFixedCoordinates.applyTemporalLedgerQuaternion
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeFixedCoordinates.temporalLedger_nonupper_link
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeFixedCoordinates.temporalLedger_nonupper_assignment
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeFixedCoordinates.reindex_prefix_coeffEqv
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeFixedCoordinates.temporalLedger_nonupper_assignment_coeffEqv
