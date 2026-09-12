/-
# The complete temporal ledger has the common upper-link image

The two endpoint shears compose to g_start^-1 U g_end. Every other physical
link batch preserves this word: its selected coordinate is different, while
all fixed-time multipliers remain fixed. Identity fallbacks and empty batches
are included. Equality retains all coefficient probes after common padding.

This identifies the original chain on physical coordinates. The polynomial
substitution theorem for the same observable, global reflected-square gluing,
physical time/transfer, spectral gap and continuum construction remain open.
-/

import YMGap.Continuum.SU2QuaternionTranslationWordComposition

namespace YMGap.Continuum.BF4ExactSlabTemporalGaugeUpperCoordinates

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.SU2QuaternionHaarGaugeCancellation
open YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.BF4ExactSlabTemporalGaugeFixedCoordinates
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionInverseTranslationCoordinates
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

private theorem linkSteps_mem_ledger {extent half : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent)
    {step : SelectedTranslationStep (temporalTailBlocks extent)} (hs : step ∈ linkSteps extent half link) :
    step ∈ temporalTranslationSteps extent half := List.mem_flatMap.mpr ⟨link, hl, hs⟩

private theorem link_index_lt {extent : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) :
    (boundaryCompleteSlabLinks extent).idxOf link < temporalTailBlocks extent + 1 := by
  rw [temporalTotalBlocks_eq]
  exact List.idxOf_lt_length_of_mem hl

/-- The endpoint image uses the existing identity fallback, not a dummy
coordinate, when the projected fixed-time link is absent. -/
def endpointImage (extent half : Nat) (v : Z4Vertex) (side : SelectedTranslationSide)
    (orientation : SelectedMultiplierOrientation) (u : PolyQuaternion) : PolyQuaternion :=
  let g := match orientation with
    | .direct => temporalVertexGauge extent half v
    | .inverse => PolyQuaternion.conj (temporalVertexGauge extent half v)
  match side with
  | .left => PolyQuaternion.mul g u
  | .right => PolyQuaternion.mul u g

theorem endpointSteps_image {extent half : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) (hu : linkHalfSide half link = .upper)
    (v : Z4Vertex) (side : SelectedTranslationSide) (orientation : SelectedMultiplierOrientation) :
    PaddedQuaternionCoeffEqv (temporalTailBlocks extent + 1)
      (applySelectedTranslationStepsQuaternion (temporalTailBlocks_pos extent)
        (endpointSteps extent half link hl hu v side orientation) (correctedSlabLinkPolynomial extent link))
      (endpointImage extent half v side orientation (correctedSlabLinkPolynomial extent link)) := by
  unfold endpointSteps
  split
  · rename_i hv
    let step : SelectedTranslationStep (temporalTailBlocks extent) :=
      { selected := (boundaryCompleteSlabLinks extent).idxOf link
        multiplier := (boundaryCompleteSlabLinks extent).idxOf (fixedTimeLink half v)
        selected_lt := link_index_lt hl
        multiplier_lt := link_index_lt hv
        distinct := fun he => upper_ne_fixedTimeLink hu v (idxOf_injective_on_members hl hv he)
        side := side
        multiplierOrientation := orientation }
    have h := applyStep_coordinate (temporalTailBlocks_pos extent) step step.selected step.selected_lt
    cases side <;> cases orientation <;>
      simpa only [step, coordinateImage, if_pos rfl, endpointImage,
        temporalVertexGauge, correctedSlabLinkPolynomial_of_mem hl, correctedSlabLinkPolynomial_of_mem hv] using h
  · rename_i hv
    have hc : PolyQuaternion.conj PolyQuaternion.one = PolyQuaternion.one := rfl
    cases side <;> cases orientation <;>
      simp only [endpointImage, temporalVertexGauge, correctedSlabLinkPolynomial_of_not_mem hv, hc]
    · exact .of_coeff (PolyQuaternionCoeffEqv.one_mul _).symm
    · exact .of_coeff (PolyQuaternionCoeffEqv.one_mul _).symm
    · exact .of_coeff (PolyQuaternionCoeffEqv.mul_one _).symm
    · exact .of_coeff (PolyQuaternionCoeffEqv.mul_one _).symm

/-- Every subchain of the literal ledger fixes every vertex gauge, including
absent-endpoint constants. -/
theorem subchain_fixes_vertexGauge {extent half : Nat}
    (steps : List (SelectedTranslationStep (temporalTailBlocks extent)))
    (hs : ∀ step, step ∈ steps → step ∈ temporalTranslationSteps extent half) (v : Z4Vertex) :
    PaddedQuaternionCoeffEqv (temporalTailBlocks extent + 1)
      (applySelectedTranslationStepsQuaternion (temporalTailBlocks_pos extent) steps
        (temporalVertexGauge extent half v)) (temporalVertexGauge extent half v) := by
  unfold temporalVertexGauge
  by_cases hv : fixedTimeLink half v ∈ boundaryCompleteSlabLinks extent
  · rw [correctedSlabLinkPolynomial_of_mem hv]
    apply applySteps_fixed_coordinate _ _ _ (link_index_lt hv)
    intro step hm
    exact temporalTranslationSteps_not_selected hv (by rw [fixedTimeLink_fixed]; intro h; cases h) (hs step hm)
  · rw [correctedSlabLinkPolynomial_of_not_mem hv]
    exact applySteps_one _ _

/-- Ordered word substitution, before integration. -/
theorem applySteps_gaugeLink {tailBlocks : Nat} (hb : 0 < tailBlocks)
    (steps : List (SelectedTranslationStep tailBlocks)) (start u finish : PolyQuaternion) :
    PaddedQuaternionCoeffEqv (tailBlocks + 1)
      (applySelectedTranslationStepsQuaternion hb steps (gaugeLink start u finish))
      (gaugeLink (applySelectedTranslationStepsQuaternion hb steps start)
        (applySelectedTranslationStepsQuaternion hb steps u)
        (applySelectedTranslationStepsQuaternion hb steps finish)) := by
  unfold gaugeLink
  exact (applySteps_mul hb steps _ _).trans
    (((applySteps_mul hb steps _ _).trans
      ((applySteps_conj hb steps start).mul (.refl _ _))).mul (.refl _ _))

theorem linkSteps_upper_image {extent half : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) (hu : linkHalfSide half link = .upper) :
    PaddedQuaternionCoeffEqv (temporalTailBlocks extent + 1)
      (applySelectedTranslationStepsQuaternion (temporalTailBlocks_pos extent)
        (linkSteps extent half link) (correctedSlabLinkPolynomial extent link))
      (upperTemporalLink extent half link) := by
  let rest := endpointSteps extent half link hl hu (addE link.1 link.2) .right .direct
  have hs : ∀ step, step ∈ rest → step ∈ temporalTranslationSteps extent half := by
    intro step hm
    apply linkSteps_mem_ledger hl
    simp only [linkSteps, dif_pos hl, dif_pos hu]
    exact List.mem_append_right _ hm
  have hleft := endpointSteps_image hl hu link.1 .left .inverse
  have hright := endpointSteps_image hl hu (addE link.1 link.2) .right .direct
  have hg := subchain_fixes_vertexGauge rest hs link.1
  have hc := (applySteps_conj (temporalTailBlocks_pos extent) rest _).trans hg.conj
  rw [linkSteps, dif_pos hl, dif_pos hu, applySteps_append, upperTemporalLink, if_pos hu]
  exact (hleft.applySteps (temporalTailBlocks_pos extent) rest).trans
    ((applySteps_mul (temporalTailBlocks_pos extent) rest _ _).trans
      ((hc.mul hright).trans (.of_coeff (PolyQuaternionCoeffEqv.mul_assoc _ _ _).symm)))

theorem subchain_fixes_upper_word {extent half : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) (hu : linkHalfSide half link = .upper)
    (steps : List (SelectedTranslationStep (temporalTailBlocks extent)))
    (hs : ∀ step, step ∈ steps → step ∈ temporalTranslationSteps extent half)
    (hn : ∀ step, step ∈ steps → (boundaryCompleteSlabLinks extent).idxOf link ≠ step.selected) :
    PaddedQuaternionCoeffEqv (temporalTailBlocks extent + 1)
      (applySelectedTranslationStepsQuaternion (temporalTailBlocks_pos extent) steps
        (upperTemporalLink extent half link)) (upperTemporalLink extent half link) := by
  have hstart := subchain_fixes_vertexGauge steps hs link.1
  have hfinish := subchain_fixes_vertexGauge steps hs (addE link.1 link.2)
  have hlink := applySteps_fixed_coordinate (temporalTailBlocks_pos extent) steps _ (link_index_lt hl) hn
  rw [upperTemporalLink, if_pos hu, correctedSlabLinkPolynomial_of_mem hl]
  exact (applySteps_gaugeLink _ steps _ _ _).trans ((hstart.conj.mul hlink).mul hfinish)

private theorem other_batch_not_selected {extent half : Nat} {link source : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) (hs : source ∈ boundaryCompleteSlabLinks extent)
    (hne : link ≠ source) {step : SelectedTranslationStep (temporalTailBlocks extent)}
    (hm : step ∈ linkSteps extent half source) :
    (boundaryCompleteSlabLinks extent).idxOf link ≠ step.selected := by
  intro heq
  exact hne (idxOf_injective_on_members hl hs (heq.trans (linkSteps_selected hm).2))

/-- In a duplicate-free list of physical link batches, exactly the target's
batch changes its coordinate. All remaining batches preserve its gauge word. -/
theorem physical_batches_upper_image {extent half : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) (hu : linkHalfSide half link = .upper) :
    ∀ (links : List Z4Link), links.Nodup →
      (∀ source, source ∈ links → source ∈ boundaryCompleteSlabLinks extent) → link ∈ links →
      PaddedQuaternionCoeffEqv (temporalTailBlocks extent + 1)
        (applySelectedTranslationStepsQuaternion (temporalTailBlocks_pos extent)
          (links.flatMap (linkSteps extent half)) (correctedSlabLinkPolynomial extent link))
        (upperTemporalLink extent half link)
  | [], _, _, hm => by cases hm
  | source :: rest, hnd, hphysical, hm => by
      have hsource := hphysical source List.mem_cons_self
      have hr : ∀ s, s ∈ rest → s ∈ boundaryCompleteSlabLinks extent :=
        fun s hs => hphysical s (List.mem_cons_of_mem source hs)
      have hndRest := (List.nodup_cons.mp hnd).2
      simp only [List.flatMap_cons, applySteps_append]
      by_cases he : link = source
      · subst source
        have hn : ∀ step, step ∈ rest.flatMap (linkSteps extent half) →
            (boundaryCompleteSlabLinks extent).idxOf link ≠ step.selected := by
          intro step hs
          obtain ⟨s, hsr, hstep⟩ := List.mem_flatMap.mp hs
          exact other_batch_not_selected hl (hr s hsr)
            (fun heq => (List.nodup_cons.mp hnd).1 (heq ▸ hsr)) hstep
        have hs : ∀ step, step ∈ rest.flatMap (linkSteps extent half) →
            step ∈ temporalTranslationSteps extent half := by
          intro step hm
          obtain ⟨s, hsr, hstep⟩ := List.mem_flatMap.mp hm
          exact linkSteps_mem_ledger (hr s hsr) hstep
        exact ((linkSteps_upper_image hl hu).applySteps (temporalTailBlocks_pos extent) _).trans
          (subchain_fixes_upper_word hl hu _ hs hn)
      · have hfix := applySteps_fixed_coordinate (temporalTailBlocks_pos extent)
          (linkSteps extent half source) _ (link_index_lt hl)
          (fun _ hs => other_batch_not_selected hl hsource he hs)
        rw [← correctedSlabLinkPolynomial_of_mem hl] at hfix
        exact (hfix.applySteps (temporalTailBlocks_pos extent) _).trans
          (physical_batches_upper_image hl hu rest hndRest hr ((List.mem_cons.mp hm).resolve_left he))

theorem temporalLedger_upper_assignment {extent half : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) (hu : linkHalfSide half link = .upper) :
    PaddedQuaternionCoeffEqv (boundaryCompleteSlabLinks extent).length
      (applyTemporalLedgerQuaternion extent half (correctedSlabLinkPolynomial extent link))
      (upperTemporalLink extent half link) := by
  have h := physical_batches_upper_image hl hu (boundaryCompleteSlabLinks extent)
    (boundaryCompleteSlabLinks_nodup extent) (fun _ hm => hm) hl
  rw [temporalTotalBlocks_eq] at h
  exact h

/-- Every actual physical link now has the image of the ONE common temporal
assignment under the WHOLE original Haar-preserving ledger. -/
theorem temporalLedger_assignment {extent half : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) :
    PaddedQuaternionCoeffEqv (boundaryCompleteSlabLinks extent).length
      (applyTemporalLedgerQuaternion extent half (correctedSlabLinkPolynomial extent link))
      (upperTemporalLink extent half link) := by
  by_cases hu : linkHalfSide half link = .upper
  · exact temporalLedger_upper_assignment hl hu
  · exact temporalLedger_nonupper_assignment_coeffEqv hl hu

/-- The ORIGINAL plaquette holonomy, including its oriented fold, is sent
to the previously defined common temporal face word. This is coefficient
equality before Haar, for every physical face and arbitrary slab extent. -/
theorem temporalLedger_plaquette_word {extent half : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) :
    PaddedQuaternionCoeffEqv (boundaryCompleteSlabLinks extent).length
      (applyTemporalLedgerQuaternion extent half (correctedSlabPlaquettePolynomial extent face))
      (temporalFaceWord extent half face) := by
  have hlink (link : Z4Link) (hi : link ∈ edgesOf face) :=
    temporalLedger_assignment (half := half)
      ((mem_boundaryCompleteSlabLinks_iff extent link).mpr ⟨face, hf, hi⟩)
  have ha := hlink (faceLinkA face) (by simp [faceLinkA, edgesOf])
  have hb := hlink (faceLinkB face) (by simp [faceLinkB, edgesOf])
  have hc := hlink (faceLinkC face) (by simp [faceLinkC, edgesOf])
  have hd := hlink (faceLinkD face) (by simp [faceLinkD, edgesOf])
  have hm (p q : PolyQuaternion) : PaddedQuaternionCoeffEqv (boundaryCompleteSlabLinks extent).length
      (applyTemporalLedgerQuaternion extent half (PolyQuaternion.mul p q))
      (PolyQuaternion.mul (applyTemporalLedgerQuaternion extent half p)
        (applyTemporalLedgerQuaternion extent half q)) :=
    .of_coeff (applySelectedTranslationStepsQuaternion_mul (temporalTailBlocks_pos extent) _ p q)
  have hconj (q : PolyQuaternion) : PaddedQuaternionCoeffEqv (boundaryCompleteSlabLinks extent).length
      (applyTemporalLedgerQuaternion extent half (PolyQuaternion.conj q))
      (PolyQuaternion.conj (applyTemporalLedgerQuaternion extent half q)) :=
    .of_coeff (applySelectedTranslationStepsQuaternion_conj (temporalTailBlocks_pos extent) _ q)
  have hsource : PolyQuaternionCoeffEqv (correctedSlabPlaquettePolynomial extent face)
      (plaquetteWord (correctedSlabLinkPolynomial extent (faceLinkA face))
        (correctedSlabLinkPolynomial extent (faceLinkB face))
        (correctedSlabLinkPolynomial extent (faceLinkC face))
        (correctedSlabLinkPolynomial extent (faceLinkD face))) :=
    (((PolyQuaternionCoeffEqv.one_mul _).mul (PolyQuaternionCoeffEqv.refl _)).mul
      (PolyQuaternionCoeffEqv.refl _)).mul (PolyQuaternionCoeffEqv.refl _)
  have hs : PaddedQuaternionCoeffEqv (boundaryCompleteSlabLinks extent).length
      (applyTemporalLedgerQuaternion extent half (correctedSlabPlaquettePolynomial extent face))
      (applyTemporalLedgerQuaternion extent half
        (plaquetteWord (correctedSlabLinkPolynomial extent (faceLinkA face))
          (correctedSlabLinkPolynomial extent (faceLinkB face))
          (correctedSlabLinkPolynomial extent (faceLinkC face))
          (correctedSlabLinkPolynomial extent (faceLinkD face)))) :=
    .of_coeff (applySelectedTranslationStepsQuaternion_coeffEqv (temporalTailBlocks_pos extent) _ hsource)
  exact hs.trans ((hm _ _).trans
    (((hm _ _).trans (((hm _ _).trans (ha.mul hb)).mul ((hconj _).trans hc.conj))).mul
      ((hconj _).trans hd.conj)))

end YMGap.Continuum.BF4ExactSlabTemporalGaugeUpperCoordinates

#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeUpperCoordinates.endpointImage
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeUpperCoordinates.endpointSteps_image
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeUpperCoordinates.subchain_fixes_vertexGauge
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeUpperCoordinates.applySteps_gaugeLink
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeUpperCoordinates.linkSteps_upper_image
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeUpperCoordinates.subchain_fixes_upper_word
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeUpperCoordinates.physical_batches_upper_image
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeUpperCoordinates.temporalLedger_upper_assignment
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeUpperCoordinates.temporalLedger_assignment
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeUpperCoordinates.temporalLedger_plaquette_word
