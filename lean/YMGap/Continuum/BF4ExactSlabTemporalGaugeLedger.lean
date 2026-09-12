/-
# Literal temporal-gauge shear ledger on the original slab carrier

For each actual upper link, emit left-inverse multiplication by its starting
fixed-time link, then right-direct multiplication by its ending fixed-time
link. An absent fixed-time link contributes no step, exactly matching the
existing identity fallback. All index bounds and distinctness proofs are
structural. The generated chain preserves the SAME full product-Haar law.

The full coordinate image of this ledger and its identification with
upperTemporalLink on all observables remain separate proof obligations.
-/

import YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces
import YMGap.Continuum.SU2QuaternionTranslationCoordinateCoefficients

namespace YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslationChain

theorem idxOf_injective_on_members {A : Type} [BEq A] [LawfulBEq A]
    {links : List A} {a b : A} (ha : a ∈ links) (hb : b ∈ links)
    (h : links.idxOf a = links.idxOf b) : a = b := by
  have hva : links[links.idxOf a]'(List.idxOf_lt_length_of_mem ha) = a :=
    eq_of_beq (List.findIdx_getElem (w := List.idxOf_lt_length_of_mem ha))
  have hvb : links[links.idxOf b]'(List.idxOf_lt_length_of_mem hb) = b :=
    eq_of_beq (List.findIdx_getElem (w := List.idxOf_lt_length_of_mem hb))
  have hv : links[links.idxOf a]'(List.idxOf_lt_length_of_mem ha) =
      links[links.idxOf b]'(List.idxOf_lt_length_of_mem hb) := by congr 1
  exact hva.symm.trans (hv.trans hvb)

/-- Even extent zero contains two distinct edges of its bottom spatial face;
the selected-shear carrier therefore always has at least two blocks. -/
theorem slabLinks_length_gt_one (extent : Nat) :
    1 < (boundaryCompleteSlabLinks extent).length := by
  have hf : bottomSpatialPlaquette ∈ boundaryCompleteSlabPlaquettes extent :=
    (mem_boundaryCompleteSlabPlaquettes extent _).mpr
      ⟨bottomSpatialPlaquette_mem_boxPlaquettes (by omega), Nat.zero_le extent⟩
  let a : Z4Link := ((0, 0, 0, 0), .x0)
  let b : Z4Link := ((0, 0, 0, 0), .x1)
  have ha : a ∈ boundaryCompleteSlabLinks extent :=
    (mem_boundaryCompleteSlabLinks_iff extent a).mpr
      ⟨bottomSpatialPlaquette, hf, by simp [a, bottomSpatialPlaquette, edgesOf, dirsOf]⟩
  have hb : b ∈ boundaryCompleteSlabLinks extent :=
    (mem_boundaryCompleteSlabLinks_iff extent b).mpr
      ⟨bottomSpatialPlaquette, hf, by simp [b, bottomSpatialPlaquette, edgesOf, dirsOf]⟩
  have hai := List.idxOf_lt_length_of_mem ha
  have hbi := List.idxOf_lt_length_of_mem hb
  have hne : (boundaryCompleteSlabLinks extent).idxOf a ≠
      (boundaryCompleteSlabLinks extent).idxOf b := by
    intro h
    have he := idxOf_injective_on_members ha hb h
    have hd := congrArg Prod.snd he
    contradiction
  omega

def temporalTailBlocks (extent : Nat) : Nat := (boundaryCompleteSlabLinks extent).length - 1

theorem temporalTailBlocks_pos (extent : Nat) : 0 < temporalTailBlocks extent := by
  have h := slabLinks_length_gt_one extent
  unfold temporalTailBlocks
  omega

theorem temporalTotalBlocks_eq (extent : Nat) :
    temporalTailBlocks extent + 1 = (boundaryCompleteSlabLinks extent).length := by
  have h := slabLinks_length_gt_one extent
  unfold temporalTailBlocks
  omega

theorem fixedTimeLink_fixed (half : Nat) (v : Z4Vertex) :
    linkHalfSide half (fixedTimeLink half v) = .fixed := by
  simp only [fixedTimeLink, linkHalfSide, temporalHalfSide, Nat.lt_irrefl, if_false, if_true]

theorem upper_ne_fixedTimeLink {half : Nat} {link : Z4Link}
    (hu : linkHalfSide half link = .upper) (v : Z4Vertex) : link ≠ fixedTimeLink half v := by
  intro heq
  rw [heq, fixedTimeLink_fixed] at hu
  cases hu

/-- A present fixed-time endpoint gives one proof-carrying elementary shear.
Absence gives the empty list, not an artificial extra Haar variable. -/
def endpointSteps (extent half : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (hu : linkHalfSide half link = .upper)
    (v : Z4Vertex) (side : SelectedTranslationSide) (orientation : SelectedMultiplierOrientation) :
    List (SelectedTranslationStep (temporalTailBlocks extent)) :=
  if hv : fixedTimeLink half v ∈ boundaryCompleteSlabLinks extent then
    [{ selected := (boundaryCompleteSlabLinks extent).idxOf link
       multiplier := (boundaryCompleteSlabLinks extent).idxOf (fixedTimeLink half v)
       selected_lt := by rw [temporalTotalBlocks_eq]; exact List.idxOf_lt_length_of_mem hl
       multiplier_lt := by rw [temporalTotalBlocks_eq]; exact List.idxOf_lt_length_of_mem hv
       distinct := fun he => upper_ne_fixedTimeLink hu v (idxOf_injective_on_members hl hv he)
       side := side
       multiplierOrientation := orientation }]
  else []

def linkSteps (extent half : Nat) (link : Z4Link) :
    List (SelectedTranslationStep (temporalTailBlocks extent)) :=
  if hl : link ∈ boundaryCompleteSlabLinks extent then
    if hu : linkHalfSide half link = .upper then
      endpointSteps extent half link hl hu link.1 .left .inverse ++
        endpointSteps extent half link hl hu (addE link.1 link.2) .right .direct
    else []
  else []

def temporalTranslationSteps (extent half : Nat) :
    List (SelectedTranslationStep (temporalTailBlocks extent)) :=
  (boundaryCompleteSlabLinks extent).flatMap (linkSteps extent half)

def applyTemporalTranslationLedger (extent half : Nat) (p : RatPoly) : RatPoly :=
  applySelectedTranslationSteps (temporalTailBlocks_pos extent) (temporalTranslationSteps extent half) p

theorem applyTemporalTranslationLedger_supported (extent half : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length
      (applyTemporalTranslationLedger extent half p) := by
  have h := applySelectedTranslationSteps_supported (temporalTailBlocks_pos extent)
    (temporalTranslationSteps extent half) p
  rw [temporalTotalBlocks_eq] at h
  exact h hp

/-- Full original product-Haar invariance at arbitrary extent, half-plane
and polynomial degree. There is no successive scan or degree hypothesis. -/
theorem applyTemporalTranslationLedger_haar (extent half : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p) :
    (quaternionHaar (boundaryCompleteSlabLinks extent).length (applyTemporalTranslationLedger extent half p)).eqv
      (quaternionHaar (boundaryCompleteSlabLinks extent).length p) := by
  have h := applySelectedTranslationSteps_haar (temporalTailBlocks_pos extent)
    (temporalTranslationSteps extent half) p
  rw [temporalTotalBlocks_eq] at h
  exact h hp

theorem endpointSteps_selected {extent half : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) (hu : linkHalfSide half link = .upper)
    (v : Z4Vertex) (side : SelectedTranslationSide) (orientation : SelectedMultiplierOrientation)
    {step : SelectedTranslationStep (temporalTailBlocks extent)}
    (hs : step ∈ endpointSteps extent half link hl hu v side orientation) :
    step.selected = (boundaryCompleteSlabLinks extent).idxOf link := by
  unfold endpointSteps at hs
  split at hs
  · have he := List.mem_singleton.mp hs
    rw [he]
  · cases hs

theorem linkSteps_selected {extent half : Nat} {link : Z4Link}
    {step : SelectedTranslationStep (temporalTailBlocks extent)}
    (hs : step ∈ linkSteps extent half link) :
    linkHalfSide half link = .upper ∧
      step.selected = (boundaryCompleteSlabLinks extent).idxOf link := by
  unfold linkSteps at hs
  split at hs
  · split at hs
    · rename_i hl hu
      refine ⟨hu, ?_⟩
      rcases List.mem_append.mp hs with hs | hs
      · exact endpointSteps_selected hl hu _ _ _ hs
      · exact endpointSteps_selected hl hu _ _ _ hs
    · cases hs
  · cases hs

/-- Every emitted step selects an actual upper link. -/
theorem temporalTranslationSteps_selected_upper {extent half : Nat}
    {step : SelectedTranslationStep (temporalTailBlocks extent)}
    (hs : step ∈ temporalTranslationSteps extent half) :
    ∃ link, link ∈ boundaryCompleteSlabLinks extent ∧
      linkHalfSide half link = .upper ∧ step.selected = (boundaryCompleteSlabLinks extent).idxOf link := by
  obtain ⟨link, hl, hs⟩ := List.mem_flatMap.mp hs
  exact ⟨link, hl, linkSteps_selected hs⟩

theorem endpointSteps_multiplier {extent half : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) (hu : linkHalfSide half link = .upper)
    (v : Z4Vertex) (side : SelectedTranslationSide) (orientation : SelectedMultiplierOrientation)
    {step : SelectedTranslationStep (temporalTailBlocks extent)}
    (hs : step ∈ endpointSteps extent half link hl hu v side orientation) :
    fixedTimeLink half v ∈ boundaryCompleteSlabLinks extent ∧
      step.multiplier = (boundaryCompleteSlabLinks extent).idxOf (fixedTimeLink half v) := by
  unfold endpointSteps at hs
  split at hs
  · rename_i hv
    have he := List.mem_singleton.mp hs
    rw [he]
    exact ⟨hv, rfl⟩
  · cases hs

theorem linkSteps_multiplier {extent half : Nat} {link : Z4Link}
    {step : SelectedTranslationStep (temporalTailBlocks extent)}
    (hs : step ∈ linkSteps extent half link) :
    ∃ v, fixedTimeLink half v ∈ boundaryCompleteSlabLinks extent ∧
      step.multiplier = (boundaryCompleteSlabLinks extent).idxOf (fixedTimeLink half v) := by
  unfold linkSteps at hs
  split at hs
  · split at hs
    · rename_i hl hu
      rcases List.mem_append.mp hs with hs | hs
      · exact ⟨link.1, endpointSteps_multiplier hl hu _ _ _ hs⟩
      · exact ⟨addE link.1 link.2, endpointSteps_multiplier hl hu _ _ _ hs⟩
    · cases hs
  · cases hs

/-- Every emitted multiplier is an actual fixed-time link on this carrier. -/
theorem temporalTranslationSteps_multiplier_fixed {extent half : Nat}
    {step : SelectedTranslationStep (temporalTailBlocks extent)}
    (hs : step ∈ temporalTranslationSteps extent half) :
    ∃ link, link ∈ boundaryCompleteSlabLinks extent ∧
      linkHalfSide half link = .fixed ∧ step.multiplier = (boundaryCompleteSlabLinks extent).idxOf link := by
  obtain ⟨source, _, hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨v, hv, heq⟩ := linkSteps_multiplier hs
  exact ⟨fixedTimeLink half v, hv, fixedTimeLink_fixed half v, heq⟩

theorem temporalTranslationSteps_not_selected {extent half : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) (hn : linkHalfSide half link ≠ .upper)
    {step : SelectedTranslationStep (temporalTailBlocks extent)}
    (hs : step ∈ temporalTranslationSteps extent half) :
    (boundaryCompleteSlabLinks extent).idxOf link ≠ step.selected := by
  obtain ⟨source, hm, hu, he⟩ := temporalTranslationSteps_selected_upper hs
  intro heq
  have hlink := idxOf_injective_on_members hl hm (heq.trans he)
  exact hn (hlink ▸ hu)

end YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger

#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger.idxOf_injective_on_members
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger.slabLinks_length_gt_one
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger.temporalTailBlocks
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger.temporalTailBlocks_pos
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger.temporalTotalBlocks_eq
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger.fixedTimeLink_fixed
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger.upper_ne_fixedTimeLink
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger.endpointSteps
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger.linkSteps
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger.temporalTranslationSteps
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger.applyTemporalTranslationLedger
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger.applyTemporalTranslationLedger_supported
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger.applyTemporalTranslationLedger_haar
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger.endpointSteps_selected
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger.linkSteps_selected
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger.temporalTranslationSteps_selected_upper
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger.endpointSteps_multiplier
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger.linkSteps_multiplier
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger.temporalTranslationSteps_multiplier_fixed
#print axioms YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger.temporalTranslationSteps_not_selected
