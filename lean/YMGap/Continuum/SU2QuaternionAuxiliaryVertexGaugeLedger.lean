/-
# A common three-auxiliary-gauge change of variables on all original links

The three gauge quaternions occupy blocks 0,1,2; the n original links occupy
blocks 3,...,n+2. For each original link, a supplied pair of endpoint tags
selects one of the three gauges or the identity. The explicit finite ledger
has the simultaneous image g_start^-1 U g_finish on EVERY original link,
fixes every auxiliary gauge, and preserves the full supported product-Haar
integral at every degree. No original action factor is dropped or integrated
independently by this construction.

Endpoint tags are finite data, not analytic hypotheses. Their identification
with the vertices of the physical slab, and preservation of its full action
and observable insertion, must still be proved by the physical consumer.
-/

import YMGap.Continuum.BF4ExactSlabTemporalGaugeUpperCoordinates
import YMGap.Continuum.SU2QuaternionTranslationPolynomialImages

namespace YMGap.Continuum.SU2QuaternionAuxiliaryVertexGaugeLedger

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslationChain
open YMGap.Continuum.SU2QuaternionInverseTranslationCoordinates
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.SU2QuaternionHaarGaugeCancellation
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.BF4ExactSlabTemporalGaugeUpperCoordinates (applySteps_gaugeLink)

/-- None fixes a vertex gauge to one; some j selects auxiliary block j. -/
def auxiliaryGauge : Option (Fin 3) → PolyQuaternion
  | none => PolyQuaternion.one
  | some j => PolyQuaternion.coordinateVariable j.val

def originalLink {n : Nat} (i : Fin n) : PolyQuaternion :=
  PolyQuaternion.coordinateVariable (i.val + 3)

def endpointSteps {n : Nat} (i : Fin n) (tag : Option (Fin 3))
    (side : SelectedTranslationSide) (orientation : SelectedMultiplierOrientation) :
    List (SelectedTranslationStep (n + 2)) :=
  match tag with
  | none => []
  | some j => [{ selected := i.val + 3
                 multiplier := j.val
                 selected_lt := by have := i.isLt; omega
                 multiplier_lt := by have := j.isLt; omega
                 distinct := by have := j.isLt; omega
                 side := side
                 multiplierOrientation := orientation }]

def linkSteps {n : Nat} (start finish : Fin n → Option (Fin 3)) (i : Fin n) :
    List (SelectedTranslationStep (n + 2)) :=
  endpointSteps i (start i) .left .inverse ++ endpointSteps i (finish i) .right .direct

def linkImage {n : Nat} (start finish : Fin n → Option (Fin 3)) (i : Fin n) : PolyQuaternion :=
  gaugeLink (auxiliaryGauge (start i)) (originalLink i) (auxiliaryGauge (finish i))

private theorem endpoint_selected {n : Nat} (i : Fin n) (tag : Option (Fin 3))
    (side : SelectedTranslationSide) (orientation : SelectedMultiplierOrientation)
    {step : SelectedTranslationStep (n + 2)} (h : step ∈ endpointSteps i tag side orientation) :
    step.selected = i.val + 3 := by
  cases tag with
  | none => cases h
  | some j => have he := List.mem_singleton.mp h; rw [he]

theorem linkSteps_selected {n : Nat} (start finish : Fin n → Option (Fin 3)) (i : Fin n)
    {step : SelectedTranslationStep (n + 2)} (h : step ∈ linkSteps start finish i) :
    step.selected = i.val + 3 := by
  rcases List.mem_append.mp h with h | h
  · exact endpoint_selected i _ _ _ h
  · exact endpoint_selected i _ _ _ h

/-- Every chain selecting only original links fixes all three auxiliaries. -/
theorem steps_fix_gauge {n : Nat} (steps : List (SelectedTranslationStep (n + 2)))
    (hs : ∀ step, step ∈ steps → 3 ≤ step.selected) (tag : Option (Fin 3)) :
    PaddedQuaternionCoeffEqv (n + 3)
      (applySelectedTranslationStepsQuaternion (by omega : 0 < n + 2) steps (auxiliaryGauge tag))
      (auxiliaryGauge tag) := by
  cases tag with
  | none => exact applySteps_one _ _
  | some j =>
      apply applySteps_fixed_coordinate _ _ _ (by have := j.isLt; omega)
      intro step hm
      have := hs step hm
      have := j.isLt
      omega

private theorem left_endpoint_image {n : Nat} (i : Fin n) (tag : Option (Fin 3)) :
    PaddedQuaternionCoeffEqv (n + 3)
      (applySelectedTranslationStepsQuaternion (by omega : 0 < n + 2)
        (endpointSteps i tag .left .inverse) (originalLink i))
      (PolyQuaternion.mul (PolyQuaternion.conj (auxiliaryGauge tag)) (originalLink i)) := by
  cases tag with
  | none => exact .of_coeff (PolyQuaternionCoeffEqv.one_mul _).symm
  | some j =>
      let step : SelectedTranslationStep (n + 2) :=
        { selected := i.val + 3, multiplier := j.val,
          selected_lt := by have := i.isLt; omega,
          multiplier_lt := by have := j.isLt; omega,
          distinct := by have := j.isLt; omega,
          side := .left, multiplierOrientation := .inverse }
      have h := applyStep_coordinate (by omega : 0 < n + 2) step step.selected step.selected_lt
      simpa only [step, coordinateImage, if_pos rfl, originalLink, auxiliaryGauge] using h

private theorem right_endpoint_image {n : Nat} (i : Fin n) (tag : Option (Fin 3)) :
    PaddedQuaternionCoeffEqv (n + 3)
      (applySelectedTranslationStepsQuaternion (by omega : 0 < n + 2)
        (endpointSteps i tag .right .direct) (originalLink i))
      (PolyQuaternion.mul (originalLink i) (auxiliaryGauge tag)) := by
  cases tag with
  | none => exact .of_coeff (PolyQuaternionCoeffEqv.mul_one _).symm
  | some j =>
      let step : SelectedTranslationStep (n + 2) :=
        { selected := i.val + 3, multiplier := j.val,
          selected_lt := by have := i.isLt; omega,
          multiplier_lt := by have := j.isLt; omega,
          distinct := by have := j.isLt; omega,
          side := .right, multiplierOrientation := .direct }
      have h := applyStep_coordinate (by omega : 0 < n + 2) step step.selected step.selected_lt
      simpa only [step, coordinateImage, if_pos rfl, originalLink, auxiliaryGauge] using h

theorem linkSteps_image {n : Nat} (start finish : Fin n → Option (Fin 3)) (i : Fin n) :
    PaddedQuaternionCoeffEqv (n + 3)
      (applySelectedTranslationStepsQuaternion (by omega : 0 < n + 2)
        (linkSteps start finish i) (originalLink i)) (linkImage start finish i) := by
  let rest := endpointSteps i (finish i) .right .direct
  have hg := steps_fix_gauge rest (fun step hm => by
    have := endpoint_selected i (finish i) .right .direct hm; omega) (start i)
  have hc := (applySteps_conj (by omega : 0 < n + 2) rest _).trans hg.conj
  rw [linkSteps, applySteps_append]
  exact ((left_endpoint_image i (start i)).applySteps (by omega : 0 < n + 2) rest).trans
    ((applySteps_mul (by omega : 0 < n + 2) rest _ _).trans
      ((hc.mul (right_endpoint_image i (finish i))).trans
        (.of_coeff (PolyQuaternionCoeffEqv.mul_assoc _ _ _).symm)))

private theorem batches_original {n : Nat} (start finish : Fin n → Option (Fin 3))
    (indices : List (Fin n)) {step : SelectedTranslationStep (n + 2)}
    (h : step ∈ indices.flatMap (linkSteps start finish)) : 3 ≤ step.selected := by
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp h
  rw [linkSteps_selected start finish i hi]
  omega

private theorem other_batch {n : Nat} (start finish : Fin n → Option (Fin 3))
    {i j : Fin n} (hne : i ≠ j) {step : SelectedTranslationStep (n + 2)}
    (h : step ∈ linkSteps start finish j) : i.val + 3 ≠ step.selected := by
  rw [linkSteps_selected start finish j h]
  intro he
  apply hne
  apply Fin.ext
  omega

private theorem steps_fix_image {n : Nat} (start finish : Fin n → Option (Fin 3)) (i : Fin n)
    (steps : List (SelectedTranslationStep (n + 2)))
    (hs : ∀ step, step ∈ steps → 3 ≤ step.selected)
    (hn : ∀ step, step ∈ steps → i.val + 3 ≠ step.selected) :
    PaddedQuaternionCoeffEqv (n + 3)
      (applySelectedTranslationStepsQuaternion (by omega : 0 < n + 2) steps (linkImage start finish i))
      (linkImage start finish i) :=
  (applySteps_gaugeLink _ steps _ _ _).trans
    (((steps_fix_gauge steps hs (start i)).conj.mul
      (applySteps_fixed_coordinate _ steps _ (by have := i.isLt; omega) hn)).mul
        (steps_fix_gauge steps hs (finish i)))

/-- A link changes in its own batch only; every later batch preserves the
whole endpoint word, not merely its central coordinate. -/
theorem batches_image {n : Nat} (start finish : Fin n → Option (Fin 3)) (i : Fin n) :
    ∀ indices : List (Fin n), indices.Nodup → i ∈ indices →
      PaddedQuaternionCoeffEqv (n + 3)
        (applySelectedTranslationStepsQuaternion (by omega : 0 < n + 2)
          (indices.flatMap (linkSteps start finish)) (originalLink i)) (linkImage start finish i)
  | [], _, hi => by cases hi
  | j :: rest, hnd, hi => by
      simp only [List.flatMap_cons, applySteps_append]
      by_cases he : i = j
      · subst j
        have hn : ∀ step, step ∈ rest.flatMap (linkSteps start finish) → i.val + 3 ≠ step.selected := by
          intro step hm
          obtain ⟨j, hj, hs⟩ := List.mem_flatMap.mp hm
          exact other_batch start finish (fun h : i = j => (List.nodup_cons.mp hnd).1 (h.symm ▸ hj)) hs
        exact ((linkSteps_image start finish i).applySteps _ _).trans
          (steps_fix_image start finish i _ (fun _ hm => batches_original start finish rest hm) hn)
      · have hfix := applySteps_fixed_coordinate (by omega : 0 < n + 2)
          (linkSteps start finish j) (i.val + 3) (by have := i.isLt; omega)
          (fun _ hm => other_batch start finish he hm)
        exact (hfix.applySteps _ _).trans
          (batches_image start finish i rest (List.nodup_cons.mp hnd).2
            ((List.mem_cons.mp hi).resolve_left he))

private theorem finRange_nodup : ∀ n : Nat, (List.finRange n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
      rw [List.finRange_succ]
      apply List.nodup_cons.mpr
      constructor
      · intro hm
        obtain ⟨i, _, he⟩ := List.mem_map.mp hm
        have hv := congrArg Fin.val he
        simp at hv
      · exact CayleyPruferInjection.nodup_map_of_injOn _ _ (finRange_nodup n)
          (fun _ _ _ _ he => Fin.ext (by have hv := congrArg Fin.val he; simpa using hv))

def gaugeLedger {n : Nat} (start finish : Fin n → Option (Fin 3)) :
    List (SelectedTranslationStep (n + 2)) :=
  (List.finRange n).flatMap (linkSteps start finish)

def gaugePolynomial {n : Nat} (start finish : Fin n → Option (Fin 3)) (p : RatPoly) : RatPoly :=
  applySelectedTranslationSteps (by omega : 0 < n + 2) (gaugeLedger start finish) p

def gaugeQuaternion {n : Nat} (start finish : Fin n → Option (Fin 3)) (q : PolyQuaternion) : PolyQuaternion :=
  applySelectedTranslationStepsQuaternion (by omega : 0 < n + 2) (gaugeLedger start finish) q

theorem gaugeQuaternion_link {n : Nat} (start finish : Fin n → Option (Fin 3)) (i : Fin n) :
    PaddedQuaternionCoeffEqv (n + 3) (gaugeQuaternion start finish (originalLink i))
      (linkImage start finish i) :=
  batches_image start finish i (List.finRange n) (finRange_nodup n) (List.mem_finRange i)

theorem gaugeQuaternion_auxiliary {n : Nat} (start finish : Fin n → Option (Fin 3))
    (tag : Option (Fin 3)) :
    PaddedQuaternionCoeffEqv (n + 3) (gaugeQuaternion start finish (auxiliaryGauge tag))
      (auxiliaryGauge tag) :=
  steps_fix_gauge _ (fun _ hm => batches_original start finish _ hm) tag

theorem gaugePolynomial_supported {n : Nat} (start finish : Fin n → Option (Fin 3)) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (n + 3) p) :
    SupportedQuaternionBlocks (n + 3) (gaugePolynomial start finish p) :=
  applySelectedTranslationSteps_supported _ _ p hp

/-- The WHOLE supported polynomial is changed together; this does not
replace a gauge-dependent action factor by an independent spectator. -/
theorem gaugePolynomial_haar {n : Nat} (start finish : Fin n → Option (Fin 3)) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (n + 3) p) :
    (quaternionHaar (n + 3) (gaugePolynomial start finish p)).eqv (quaternionHaar (n + 3) p) :=
  applySelectedTranslationSteps_haar _ _ p hp

end YMGap.Continuum.SU2QuaternionAuxiliaryVertexGaugeLedger

#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryVertexGaugeLedger.auxiliaryGauge
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryVertexGaugeLedger.originalLink
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryVertexGaugeLedger.endpointSteps
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryVertexGaugeLedger.linkSteps
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryVertexGaugeLedger.linkImage
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryVertexGaugeLedger.linkSteps_selected
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryVertexGaugeLedger.steps_fix_gauge
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryVertexGaugeLedger.linkSteps_image
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryVertexGaugeLedger.batches_image
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryVertexGaugeLedger.gaugeLedger
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryVertexGaugeLedger.gaugePolynomial
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryVertexGaugeLedger.gaugeQuaternion
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryVertexGaugeLedger.gaugeQuaternion_link
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryVertexGaugeLedger.gaugeQuaternion_auxiliary
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryVertexGaugeLedger.gaugePolynomial_supported
#print axioms YMGap.Continuum.SU2QuaternionAuxiliaryVertexGaugeLedger.gaugePolynomial_haar
