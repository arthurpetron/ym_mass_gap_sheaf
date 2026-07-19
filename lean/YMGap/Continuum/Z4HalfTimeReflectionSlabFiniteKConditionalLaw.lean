/-
# Exact arbitrary-cutoff conditional law of the corrected reflection slab

At every nonnegative rational coupling and finite character cutoff, the
corrected-slab partition is the ambient corner-box partition restricted to
labellings whose excited support stays in the slab.  Reindexing exact support
fibres identifies that physical conditional ensemble with the literal
coupling-parametric compatible support gas conditioned by the same event.

This is an arbitrary-cutoff statement.  It neither specializes to nor
identifies the law with the cutoff-one canonical polymer gas.
-/

import YMGap.Continuum.Z4HalfTimeReflectionSlabCouplingCarrierTail
import YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientComplement
import YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
import YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge

namespace YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalLaw

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientPartition
open YMGap.Continuum.Z4HalfTimeReflectionSlabCanonicalEvent
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientWeights
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4SpinSummedCrossVolumeCylinder

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_mask_eq_filter_local {A : Type}
    (weight : A → Q') (event : A → Bool) : ∀ source : List A,
    listQSum (fun item => if event item then weight item else 0) source ≈
      listQSum weight (source.filter event)
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      cases hevent : event head with
      | false =>
          simp only [hevent, Bool.false_eq_true, if_false,
            List.filter_cons, listQSum]
          exact Q'.eqv_trans _
            (0 + listQSum weight (tail.filter event)) _
            (Q'.add_eqv_congr' (Q'.eqv_refl 0)
              (listQSum_mask_eq_filter_local weight event tail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [hevent, if_true, List.filter_cons, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_mask_eq_filter_local weight event tail)

theorem ambientSlabSupportedPhysicalPartition_eqv_eventNumerator
    (coupling : Q') (cutoff extent : Nat) :
    ambientSlabSupportedPhysicalPartition coupling cutoff extent ≈
      parametricKEventNumerator coupling cutoff (extent + 1)
        (ambientSlabSupportedB extent) := by
  unfold ambientSlabSupportedPhysicalPartition
    ambientSlabSupportedLabellings
    parametricKEventNumerator parametricKEventTerm
  exact Q'.eqv_symm
    (listQSum_mask_eq_filter_local
      (parametricKPhysicalTerm coupling cutoff (extent + 1))
      (ambientSlabSupportedB extent)
      (boundedEdgeLabellings cutoff
        (List.range (plaquetteEdgeCount (extent + 1)))))

theorem slabParametricKPhysicalPartition_eqv_physicalSupportNumerator
    (coupling : Q') (cutoff extent : Nat) :
    slabParametricKPhysicalPartition coupling cutoff extent ≈
      parametricKEventNumerator coupling cutoff (extent + 1)
        (ambientSlabSupportedB extent) := by
  exact Q'.eqv_trans _
    (ambientSlabSupportedPhysicalPartition coupling cutoff extent) _
    (slabParametricKPhysicalPartition_eq_ambientSupported
      coupling cutoff extent)
    (ambientSlabSupportedPhysicalPartition_eqv_eventNumerator
      coupling cutoff extent)

/-- Zero extension identifies an arbitrary corrected-slab event numerator
with the same ambient event conjoined with the exact slab-support mask.

This is purely a finite change of variables.  In particular, it requires no
coupling sign, coefficient disintegration, or Fubini theorem. -/
theorem slabEventNumerator_zeroExtension_eqv_ambientMasked
    (coupling : Q') (cutoff extent : Nat)
    (event : EdgeLabelling → Bool) :
    slabEventNumerator coupling cutoff extent
        (fun slab => event (slabToAmbientPhysical extent slab)) ≈
      parametricKEventNumerator coupling cutoff (extent + 1)
        (fun ambient =>
          ambientSlabSupportedB extent ambient && event ambient) := by
  let observable : EdgeLabelling → Q' := fun slab =>
    if event (slabToAmbientPhysical extent slab) then 1 else 0
  have hslab :
      slabEventNumerator coupling cutoff extent
          (fun slab => event (slabToAmbientPhysical extent slab)) ≈
        slabWeightedPhysicalSum coupling cutoff extent observable := by
    unfold slabEventNumerator slabWeightedPhysicalSum
    apply listQSum_congr_on
    intro slab _hslab
    unfold observable
    cases hevent : event (slabToAmbientPhysical extent slab) with
    | false =>
        simp only [hevent, Bool.false_eq_true, if_false]
        exact Q'.eqv_symm (Q'.zero_mul_eqv _)
    | true =>
        simp only [hevent, if_true]
        exact Q'.eqv_symm (Q'.one_mul_eqv _)
  have hpullback :
      ambientSlabSupportedWeightedSum coupling cutoff extent observable ≈
        listQSum
          (fun ambient =>
            if event ambient then
              parametricKPhysicalTerm coupling cutoff (extent + 1) ambient
            else 0)
          (ambientSlabSupportedLabellings cutoff extent) := by
    unfold ambientSlabSupportedWeightedSum
    apply listQSum_congr_on
    intro ambient hambient
    have hparts := List.mem_filter.mp hambient
    have hroundtrip := slabToAmbientPhysical_ambientToSlab
      hparts.1 hparts.2
    unfold observable
    rw [hroundtrip]
    cases hevent : event ambient with
    | false =>
        exact Q'.zero_mul_eqv _
    | true =>
        exact Q'.one_mul_eqv _
  have hmasked :
      listQSum
          (fun ambient =>
            if event ambient then
              parametricKPhysicalTerm coupling cutoff (extent + 1) ambient
            else 0)
          (ambientSlabSupportedLabellings cutoff extent) ≈
        parametricKEventNumerator coupling cutoff (extent + 1)
          (fun ambient =>
            ambientSlabSupportedB extent ambient && event ambient) := by
    unfold ambientSlabSupportedLabellings
      parametricKEventNumerator parametricKEventTerm
    let labels := boundedEdgeLabellings cutoff
      (List.range (plaquetteEdgeCount (extent + 1)))
    let weight := parametricKPhysicalTerm coupling cutoff (extent + 1)
    let supported := ambientSlabSupportedB extent
    have hfilters :
        (labels.filter supported).filter event =
          labels.filter (fun ambient =>
            supported ambient && event ambient) := by
      rw [List.filter_filter]
      apply List.filter_congr
      intro ambient _hambient
      exact Bool.and_comm (event ambient) (supported ambient)
    change
      listQSum (fun ambient =>
          if event ambient then weight ambient else 0)
          (labels.filter supported) ≈
        listQSum (fun ambient =>
          if supported ambient && event ambient then weight ambient else 0)
          labels
    refine Q'.eqv_trans _
      (listQSum weight ((labels.filter supported).filter event)) _
      (listQSum_mask_eq_filter_local
        weight event (labels.filter supported)) ?_
    refine Q'.eqv_trans _
      (listQSum weight
        (labels.filter (fun ambient =>
          supported ambient && event ambient))) _
      (Q'.eqv_of_eq (congrArg (listQSum weight) hfilters)) ?_
    exact Q'.eqv_symm
      (listQSum_mask_eq_filter_local weight
        (fun ambient => supported ambient && event ambient) labels)
  exact Q'.eqv_trans _ _ _ hslab
    (Q'.eqv_trans _ _ _
      (slabWeightedPhysicalSum_eq_ambientSupported
        coupling cutoff extent observable)
      (Q'.eqv_trans _ _ _ hpullback hmasked))

theorem couplingParametricKPhysicalSlabSupportNumerator_eqv_compatible
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff extent : Nat) :
    parametricKEventNumerator coupling cutoff (extent + 1)
        (ambientSlabSupportedB extent) ≈
      couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff (extent + 1)
          (canonicalFamilySlabSupportedB extent) := by
  have hbridge :=
    couplingParametricKEventNumerator_eqv_compatibleEventNumerator
      hcoupling cutoff (extent + 1)
        (canonicalFamilySlabSupportedB extent)
  rw [cutoffOneLiftedSlabEvent_eq_physical extent] at hbridge
  exact hbridge

theorem slabParametricKPhysicalPartition_eqv_compatibleSlabSupport
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff extent : Nat) :
    slabParametricKPhysicalPartition coupling cutoff extent ≈
      couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff (extent + 1)
          (canonicalFamilySlabSupportedB extent) :=
  Q'.eqv_trans _ _ _
    (slabParametricKPhysicalPartition_eqv_physicalSupportNumerator
      coupling cutoff extent)
    (couplingParametricKPhysicalSlabSupportNumerator_eqv_compatible
      hcoupling cutoff extent)

theorem couplingParametricKPhysicalSlabRestrictedNumerator_eqv_compatible
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff extent : Nat) (event : List (List Nat) → Bool) :
    parametricKEventNumerator coupling cutoff (extent + 1)
        (fun physical => ambientSlabSupportedB extent physical &&
          cutoffOneLiftedFamilyEvent (extent + 1) event physical) ≈
      couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff (extent + 1)
          (canonicalSlabRestrictedEvent extent event) := by
  have hbridge :=
    couplingParametricKEventNumerator_eqv_compatibleEventNumerator
      hcoupling cutoff (extent + 1)
        (canonicalSlabRestrictedEvent extent event)
  rw [cutoffOneLiftedSlabRestrictedEvent_eq_physical extent event]
    at hbridge
  exact hbridge

theorem couplingParametricKPhysicalSlabSupportNumerator_pos
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff extent : Nat) :
    (0 : Q') <
      parametricKEventNumerator coupling cutoff (extent + 1)
        (ambientSlabSupportedB extent) :=
  Q'.pos_of_lt_of_le
    (slabParametricKPhysicalPartition_pos
      hcoupling cutoff extent)
    (Q'.le_of_eqv
      (slabParametricKPhysicalPartition_eqv_physicalSupportNumerator
        coupling cutoff extent))

theorem couplingParametricKCompatibleSlabSupportNumerator_pos
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff extent : Nat) :
    (0 : Q') <
      couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff (extent + 1)
          (canonicalFamilySlabSupportedB extent) :=
  Q'.pos_of_lt_of_le
    (slabParametricKPhysicalPartition_pos
      hcoupling cutoff extent)
    (Q'.le_of_eqv
      (slabParametricKPhysicalPartition_eqv_compatibleSlabSupport
        hcoupling cutoff extent))

/-- The exact finite physical law conditioned on corrected-slab support and
tested by a lifted compatible-family event. -/
def couplingParametricKPhysicalGivenSlabProbability
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff extent : Nat) (event : List (List Nat) → Bool) : Q' :=
  Q'.divPos
    (parametricKEventNumerator coupling cutoff (extent + 1)
      (fun physical => ambientSlabSupportedB extent physical &&
        cutoffOneLiftedFamilyEvent (extent + 1) event physical))
    (parametricKEventNumerator coupling cutoff (extent + 1)
      (ambientSlabSupportedB extent))
    (couplingParametricKPhysicalSlabSupportNumerator_pos
      hcoupling cutoff extent)

/-- The literal spin-summed compatible support gas conditioned on every
occupied connected support lying in the corrected slab. -/
def couplingParametricKCompatibleGivenSlabProbability
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff extent : Nat) (event : List (List Nat) → Bool) : Q' :=
  Q'.divPos
    (couplingParametricKCompatibleSupportEventNumerator
      coupling cutoff (extent + 1)
        (canonicalSlabRestrictedEvent extent event))
    (couplingParametricKCompatibleSupportEventNumerator
      coupling cutoff (extent + 1)
        (canonicalFamilySlabSupportedB extent))
    (couplingParametricKCompatibleSlabSupportNumerator_pos
      hcoupling cutoff extent)

/-- Exact arbitrary-cutoff physical/support-gas conditional-law bridge. -/
theorem couplingParametricKPhysicalGivenSlabProbability_eqv_compatible
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff extent : Nat) (event : List (List Nat) → Bool) :
    couplingParametricKPhysicalGivenSlabProbability
        coupling hcoupling cutoff extent event ≈
      couplingParametricKCompatibleGivenSlabProbability
        coupling hcoupling cutoff extent event := by
  unfold couplingParametricKPhysicalGivenSlabProbability
    couplingParametricKCompatibleGivenSlabProbability
  exact divPos_eqv_congr
    (couplingParametricKPhysicalSlabSupportNumerator_pos
      hcoupling cutoff extent)
    (couplingParametricKCompatibleSlabSupportNumerator_pos
      hcoupling cutoff extent)
    (couplingParametricKPhysicalSlabRestrictedNumerator_eqv_compatible
      hcoupling cutoff extent event)
    (couplingParametricKPhysicalSlabSupportNumerator_eqv_compatible
      hcoupling cutoff extent)

#print axioms ambientSlabSupportedPhysicalPartition_eqv_eventNumerator
#print axioms slabParametricKPhysicalPartition_eqv_physicalSupportNumerator
#print axioms slabEventNumerator_zeroExtension_eqv_ambientMasked
#print axioms slabParametricKPhysicalPartition_eqv_compatibleSlabSupport
#print axioms couplingParametricKPhysicalSlabRestrictedNumerator_eqv_compatible
#print axioms couplingParametricKCompatibleSlabSupportNumerator_pos
#print axioms couplingParametricKPhysicalGivenSlabProbability_eqv_compatible

end YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalLaw
