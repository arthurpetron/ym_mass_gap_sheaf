/-
# Ascending temporal gauge: previously reduced faces stay reduced

The cut at h acts by the existing common Haar-preserving link ledger.
Temporal faces below h already use their two literal spatial links, both
of which this ledger fixes. The current layer becomes that same relative
kernel; all other original face characters are preserved under insertions.

This is the one-step identity needed for a simultaneous sweep of the full
finite action. No spin selection, weight positivity, gap or limit is used.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm
import YMGap.Continuum.QuaternionHaarUnitScalarSquare
import YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra

namespace YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.BF4ExactSlabTemporalGaugeFixedCoordinates
open YMGap.Continuum.BF4ExactSlabTemporalGaugeUpperCoordinates
open YMGap.Continuum.BF4ExactSlabTemporalGaugeObservableImages
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarUnitScalarSquare

def Swept (cut : Nat) (face : Z4Plaq) : Prop :=
  (dirsOf face.2).2 = .x3 ∧ face.1.2.2.2 < cut

instance (cut : Nat) (face : Z4Plaq) : Decidable (Swept cut face) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem not_swept_zero (face : Z4Plaq) : ¬ Swept 0 face := fun h => Nat.not_lt_zero _ h.2

theorem swept_mono {cut : Nat} {face : Z4Plaq} (h : Swept cut face) : Swept (cut+1) face :=
  ⟨h.1, Nat.lt_trans h.2 (Nat.lt_succ_self cut)⟩

private theorem new_swept_fixed {cut : Nat} {face : Z4Plaq}
    (hn : ¬ Swept cut face) (hy : Swept (cut+1) face) : plaquetteHalfSide cut face = .fixed := by
  have ht : face.1.2.2.2 = cut := by
    have hge : ¬ face.1.2.2.2 < cut := fun h => hn ⟨hy.1,h⟩
    have hlt := hy.2
    omega
  rcases face with ⟨⟨x,y,z,t⟩,plane⟩
  change t = cut at ht
  have hd := hy.1
  cases plane <;> simp only [dirsOf] at hd <;> try cases hd
  all_goals simp only [plaquetteHalfSide, temporalHalfSide, ht, Nat.lt_irrefl, if_false, if_true]

private theorem fixed_swept_next {cut : Nat} {face : Z4Plaq}
    (h : plaquetteHalfSide cut face = .fixed) : Swept (cut+1) face := by
  rcases face with ⟨⟨x,y,z,t⟩,plane⟩
  cases plane <;> simp only [plaquetteHalfSide, spatialHalfSide, temporalHalfSide] at h
  all_goals repeat' split at h
  all_goals try cases h
  all_goals rename_i ht
  all_goals subst t
  all_goals exact ⟨rfl, Nat.lt_succ_self _⟩

/-- Both links of a previously reduced kernel are outside the new upper half. -/
theorem swept_links_fixed {cut : Nat} {face : Z4Plaq} (h : Swept cut face) :
    linkHalfSide cut (faceLinkA face) ≠ .upper ∧ linkHalfSide cut (faceLinkC face) ≠ .upper := by
  have ht := h.2
  have hd := h.1
  rcases face with ⟨⟨x,y,z,t⟩,plane⟩
  change t < cut at ht
  cases plane <;> simp only [dirsOf] at hd <;> try cases hd
  all_goals constructor
  all_goals simp only [faceLinkA, faceLinkC, dirsOf, addE, linkHalfSide, spatialHalfSide]
  all_goals rw [if_pos (by omega)]
  all_goals decide

def relativeCharacter (extent : Nat) (face : Z4Plaq) (spin : Nat) : RatPoly :=
  characterPolynomial (PolyQuaternion.mul (correctedSlabLinkPolynomial extent (faceLinkA face))
    (PolyQuaternion.conj (correctedSlabLinkPolynomial extent (faceLinkC face)))).scalar spin

def sweptCharacter (extent cut : Nat) (face : Z4Plaq) (spin : Nat) : RatPoly :=
  if Swept cut face then relativeCharacter extent face spin
  else characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin

/-- The polynomial image before applying Haar-unit cancellation. -/
def stepCharacter (extent cut : Nat) (face : Z4Plaq) (spin : Nat) : RatPoly :=
  if Swept cut face then relativeCharacter extent face spin
  else temporalCharacter extent cut face spin

private theorem relative_ledger_image {extent cut : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) (hs : Swept cut face) (spin : Nat) :
    PaddedPolynomialCoeffEqv (boundaryCompleteSlabLinks extent).length
      (applyTemporalTranslationLedger extent cut (relativeCharacter extent face spin))
      (relativeCharacter extent face spin) := by
  have hn := swept_links_fixed hs
  have ha := temporalLedger_assignment (half := cut) (link := faceLinkA face)
    ((mem_boundaryCompleteSlabLinks_iff _ _).mpr ⟨face,hf,
      by simp [faceLinkA, edgesOf]⟩)
  have hc := temporalLedger_assignment (half := cut) (link := faceLinkC face)
    ((mem_boundaryCompleteSlabLinks_iff _ _).mpr ⟨face,hf,
      by simp [faceLinkC, edgesOf]⟩)
  simp only [upperTemporalLink, if_neg hn.1] at ha
  simp only [upperTemporalLink, if_neg hn.2] at hc
  have hm := applySteps_mul (temporalTailBlocks_pos extent) (temporalTranslationSteps extent cut)
    (correctedSlabLinkPolynomial extent (faceLinkA face))
    (PolyQuaternion.conj (correctedSlabLinkPolynomial extent (faceLinkC face)))
  have hconj := applySteps_conj (temporalTailBlocks_pos extent) (temporalTranslationSteps extent cut)
    (correctedSlabLinkPolynomial extent (faceLinkC face))
  have hchar := applySteps_character (temporalTailBlocks_pos extent) (temporalTranslationSteps extent cut)
    (PolyQuaternion.mul (correctedSlabLinkPolynomial extent (faceLinkA face))
      (PolyQuaternion.conj (correctedSlabLinkPolynomial extent (faceLinkC face)))).scalar spin
  rw [temporalTotalBlocks_eq] at hm hconj hchar
  exact hchar.trans (PaddedPolynomialCoeffEqv.character (hm.trans (ha.mul (hconj.trans hc.conj))).scalar spin)

/-- One common ledger acts on every face, including already swept ones. -/
theorem swept_ledger_image {extent cut : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) (spin : Nat) :
    PaddedPolynomialCoeffEqv (boundaryCompleteSlabLinks extent).length
      (applyTemporalTranslationLedger extent cut (sweptCharacter extent cut face spin))
      (stepCharacter extent cut face spin) := by
  by_cases hs : Swept cut face
  · simpa only [sweptCharacter, stepCharacter, if_pos hs] using relative_ledger_image hf hs spin
  · simpa only [sweptCharacter, stepCharacter, if_neg hs] using temporalLedger_character (half := cut) hf spin

/-- Exact all-spin cancellation under arbitrary spectator insertions. -/
theorem step_character_carrier (extent cut : Nat) (face : Z4Plaq) (spin : Nat) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (stepCharacter extent cut face spin) (sweptCharacter extent (cut+1) face spin) := by
  by_cases hs : Swept cut face
  · simp only [stepCharacter, sweptCharacter, if_pos hs, if_pos (swept_mono hs)]
    exact .refl _ _
  · simp only [stepCharacter, if_neg hs]
    cases hc : plaquetteHalfSide cut face with
    | lower =>
      have hn : ¬ Swept (cut+1) face := fun hy => by
        have he := new_swept_fixed hs hy
        rw [hc] at he
        cases he
      rw [sweptCharacter, if_neg hn]
      exact RatPolyCoeffEqv.haarCarrier (characterPolynomial_coeffEqv (lower_face_unchanged extent cut face hc).scalar spin)
    | fixed =>
      rw [sweptCharacter, if_pos (fixed_swept_next hc)]
      exact crossing_face_character extent cut face hc spin
    | upper =>
      have hn : ¬ Swept (cut+1) face := fun hy => by
        have he := new_swept_fixed hs hy
        rw [hc] at he
        cases he
      rw [sweptCharacter, if_neg hn]
      exact upper_face_character extent cut face hc spin

private theorem character_supported {blocks : Nat} {p : RatPoly} (hp : SupportedQuaternionBlocks blocks p) :
    ∀ spin, SupportedQuaternionBlocks blocks (characterPolynomial p spin)
  | 0 => supported_one _
  | 1 => supported_smul hp 2
  | n+2 => supported_add (supported_polyMul (supported_smul hp 2) (character_supported hp (n+1)))
      (supported_smul (character_supported hp n) (-1))

theorem relative_character_supported (extent : Nat) (face : Z4Plaq) (spin : Nat) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length (relativeCharacter extent face spin) :=
  character_supported ((supported_slabLink extent _).mul (supported_slabLink extent _).conj).scalar spin

theorem swept_character_supported (extent cut : Nat) (face : Z4Plaq) (spin : Nat) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length (sweptCharacter extent cut face spin) := by
  unfold sweptCharacter
  split
  · exact relative_character_supported _ _ _
  · exact original_character_support _ _ _

theorem step_character_supported (extent cut : Nat) (face : Z4Plaq) (spin : Nat) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length (stepCharacter extent cut face spin) := by
  unfold stepCharacter
  split
  · exact relative_character_supported _ _ _
  · exact temporal_character_support _ _ _ _

end YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters

#print axioms YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters.Swept
#print axioms YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters.not_swept_zero
#print axioms YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters.swept_mono
#print axioms YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters.swept_links_fixed
#print axioms YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters.relativeCharacter
#print axioms YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters.sweptCharacter
#print axioms YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters.stepCharacter
#print axioms YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters.swept_ledger_image
#print axioms YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters.step_character_carrier
#print axioms YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters.relative_character_supported
#print axioms YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters.swept_character_supported
#print axioms YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters.step_character_supported
