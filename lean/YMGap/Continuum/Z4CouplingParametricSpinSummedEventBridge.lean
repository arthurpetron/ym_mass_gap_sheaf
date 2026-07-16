/-
# Coupling-parametric arbitrary-cutoff event bridge

A family event lifted to physical spin labellings is constant on each exact
excited-support fibre.  Threading an arbitrary nonnegative rational coupling
through that fibre sum and the coupling-parametric support-component
factorization identifies both event numerators and normalized probabilities
with the corresponding compatible support gas.
-/

import YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
import YMGap.Continuum.Z4SpinSummedCutoffEventBridge

namespace YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4ConditionalAuxiliaryMultiplicity
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4CouplingParametricSpinSummedPinnedLayer
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4SpinSummedCrossVolumeCylinder
open YMGap.Continuum.Z4SpinSummedCutoffEventBridge
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4SpinSummedSupportComponentUpper
open YMGap.Continuum.Z4SpinSummedSupportPartition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Fibrewise support masks -/

private theorem listQSum_zero_local {A : Type} {value : A → Q'} :
    ∀ source : List A, (∀ item, item ∈ source → value item ≈ 0) →
      listQSum value source ≈ 0
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hvalue => by
      change value head + listQSum value tail ≈ 0
      refine Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr'
          (hvalue head List.mem_cons_self)
          (listQSum_zero_local tail
            (fun item hitem =>
              hvalue item (List.mem_cons_of_mem head hitem)))) ?_
      exact Q'.eqv_of_eq (Q'.zero_add' 0)

theorem couplingParametricKEventFiberSum_eqv_maskedSupportActivity
    (coupling : Q') (cutoff n : Nat)
    (event : List (List Nat) → Bool) (support : List Nat) :
    listQSum
        (parametricKEventTerm coupling cutoff n
          (cutoffOneLiftedFamilyEvent n event))
        (physicalLabellingsWithSupport cutoff n support) ≈
      if event (ambientOrderedFamily n (canonicalSurfaceFamily n support))
      then couplingParametricKSupportActivity coupling cutoff n support
      else 0 := by
  by_cases hevent :
      event (ambientOrderedFamily n
        (canonicalSurfaceFamily n support)) = true
  · rw [if_pos hevent]
    unfold couplingParametricKSupportActivity
    apply listQSum_congr_on
    intro physical hphysical
    unfold parametricKEventTerm cutoffOneLiftedFamilyEvent
    rw [physicalCanonicalAmbientFamily_of_mem_supportFiber hphysical,
      if_pos hevent]
    exact Q'.eqv_refl _
  · rw [if_neg hevent]
    apply listQSum_zero_local
    intro physical hphysical
    unfold parametricKEventTerm cutoffOneLiftedFamilyEvent
    rw [physicalCanonicalAmbientFamily_of_mem_supportFiber hphysical,
      if_neg hevent]
    exact Q'.eqv_refl 0

def couplingParametricKSupportMaskedFamilyEventNumerator
    (coupling : Q') (cutoff n : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  listQSum
    (fun support =>
      if event (ambientOrderedFamily n (canonicalSurfaceFamily n support))
      then couplingParametricKSupportActivity coupling cutoff n support
      else 0)
    (cutoffOneFaceSupports n)

theorem couplingParametricKEventNumerator_eqv_supportMasked
    (coupling : Q') (cutoff n : Nat)
    (event : List (List Nat) → Bool) :
    parametricKEventNumerator coupling cutoff n
        (cutoffOneLiftedFamilyEvent n event) ≈
      couplingParametricKSupportMaskedFamilyEventNumerator
        coupling cutoff n event := by
  unfold parametricKEventNumerator
  refine Q'.eqv_trans _
    (listQSum
      (parametricKEventTerm coupling cutoff n
        (cutoffOneLiftedFamilyEvent n event))
      (parametricKSupportFibers cutoff n)) _ ?_ ?_
  · exact listQSum_perm _
      (boundedEdgeLabellings_perm_supportFibers cutoff n)
  unfold parametricKSupportFibers
    couplingParametricKSupportMaskedFamilyEventNumerator
  refine Q'.eqv_trans _
    (listQSum
      (fun support =>
        listQSum
          (parametricKEventTerm coupling cutoff n
            (cutoffOneLiftedFamilyEvent n event))
          (physicalLabellingsWithSupport cutoff n support))
      (cutoffOneFaceSupports n)) _
    (listQSum_flatMap _ _ _) ?_
  apply listQSum_congr_on
  intro support _
  exact couplingParametricKEventFiberSum_eqv_maskedSupportActivity
    coupling cutoff n event support

/-! ## 2. Canonical component and compatible-family masks -/

def couplingParametricKAmbientMaskedFamilyEventNumerator
    (coupling : Q') (cutoff n : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  listQSum
    (fun family => if event family
      then couplingParametricKSupportFamilyActivity
        coupling cutoff n family
      else 0)
    (ambientOrderedExactGas n)

private theorem maskedSupportActivity_eqv_ambientFamilyActivity
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (event : List (List Nat) → Bool)
    {support : List Nat} (hsupport : support ∈ cutoffOneFaceSupports n) :
    (if event (ambientOrderedFamily n (canonicalSurfaceFamily n support))
      then couplingParametricKSupportActivity coupling cutoff n support
      else 0) ≈
    (if event (ambientOrderedFamily n (canonicalSurfaceFamily n support))
      then couplingParametricKSupportFamilyActivity coupling cutoff n
        (ambientOrderedFamily n (canonicalSurfaceFamily n support))
      else 0) := by
  by_cases hevent :
      event (ambientOrderedFamily n
        (canonicalSurfaceFamily n support)) = true
  · rw [if_pos hevent, if_pos hevent]
    exact Q'.eqv_trans _ _ _
      (couplingParametricKSupportActivity_eqv_componentFamilyActivity
        hcoupling cutoff n support hsupport)
      (couplingParametricKSupportFamilyActivity_perm
        coupling cutoff n
        (gasFamily_perm_ambientOrdered
          (canonicalSurfaceFamily_mem_connectedGas hsupport)))
  · rw [if_neg hevent, if_neg hevent]
    exact Q'.eqv_refl 0

theorem couplingParametricKSupportMasked_eqv_ambientMasked
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (event : List (List Nat) → Bool) :
    couplingParametricKSupportMaskedFamilyEventNumerator
        coupling cutoff n event ≈
      couplingParametricKAmbientMaskedFamilyEventNumerator
        coupling cutoff n event := by
  unfold couplingParametricKSupportMaskedFamilyEventNumerator
    couplingParametricKAmbientMaskedFamilyEventNumerator
    ambientOrderedExactGas canonicalConnectedSurfaceGas
  rw [List.map_map]
  apply listQSum_map_eqv
  intro support hsupport
  exact maskedSupportActivity_eqv_ambientFamilyActivity
    hcoupling cutoff n event hsupport

def couplingParametricKCompatibleSupportEventNumerator
    (coupling : Q') (cutoff n : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
    ((canonicalCompatibleAmbientFamilies n).filter event)

private theorem listQSum_mask_eq_filter_local {A : Type}
    (weight : A → Q') (event : A → Bool) :
    ∀ source : List A,
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

theorem couplingParametricKAmbientMasked_eqv_compatibleEventNumerator
    (coupling : Q') (cutoff n : Nat)
    (event : List (List Nat) → Bool) :
    couplingParametricKAmbientMaskedFamilyEventNumerator
        coupling cutoff n event ≈
      couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff n event := by
  let masked : List (List Nat) → Q' := fun family =>
    if event family then
      couplingParametricKSupportFamilyActivity coupling cutoff n family
    else 0
  have hperm :
      listQSum masked (ambientOrderedExactGas n) ≈
        listQSum masked (canonicalCompatibleAmbientFamilies n) :=
    listQSum_perm masked
      (ambientOrderedExactGas_perm_compatibleFamilies n)
  have hfilter := listQSum_mask_eq_filter_local
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
    event (canonicalCompatibleAmbientFamilies n)
  unfold couplingParametricKAmbientMaskedFamilyEventNumerator
    couplingParametricKCompatibleSupportEventNumerator
  dsimp only [masked] at hperm
  exact Q'.eqv_trans _ _ _ hperm hfilter

theorem couplingParametricKEventNumerator_eqv_compatibleEventNumerator
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (event : List (List Nat) → Bool) :
    parametricKEventNumerator coupling cutoff n
        (cutoffOneLiftedFamilyEvent n event) ≈
      couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff n event :=
  Q'.eqv_trans _ _ _
    (couplingParametricKEventNumerator_eqv_supportMasked
      coupling cutoff n event)
    (Q'.eqv_trans _ _ _
      (couplingParametricKSupportMasked_eqv_ambientMasked
        hcoupling cutoff n event)
      (couplingParametricKAmbientMasked_eqv_compatibleEventNumerator
        coupling cutoff n event))

/-! ## 3. Normalized arbitrary-coupling laws -/

theorem couplingParametricKCompatibleSupportGasPartition_pos
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) :
    (0 : Q') < couplingParametricKCompatibleSupportGasPartition
      coupling cutoff n :=
  YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le
    (couplingKPhysicalPartition_pos hcoupling cutoff n)
    (Q'.le_of_eqv
      (couplingParametricKPhysicalPartition_eqv_compatibleSupportGas
        hcoupling cutoff n))

def couplingParametricKCompatibleSupportEventProbability
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (event : List (List Nat) → Bool) : Q' :=
  Q'.divPos
    (couplingParametricKCompatibleSupportEventNumerator
      coupling cutoff n event)
    (couplingParametricKCompatibleSupportGasPartition
      coupling cutoff n)
    (couplingParametricKCompatibleSupportGasPartition_pos
      hcoupling cutoff n)

/-- **Normalized arbitrary-coupling event bridge.** -/
theorem couplingKFamilyEventProbability_eqv_compatible
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (event : List (List Nat) → Bool) :
    couplingKFamilyEventProbability coupling hcoupling cutoff n event ≈
      couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff n event := by
  unfold couplingKFamilyEventProbability
    couplingParametricKCompatibleSupportEventProbability
  exact divPos_eqv_congr
    (couplingKPhysicalPartition_pos hcoupling cutoff n)
    (couplingParametricKCompatibleSupportGasPartition_pos
      hcoupling cutoff n)
    (couplingParametricKEventNumerator_eqv_compatibleEventNumerator
      hcoupling cutoff n event)
    (couplingParametricKPhysicalPartition_eqv_compatibleSupportGas
      hcoupling cutoff n)

#print axioms couplingParametricKEventFiberSum_eqv_maskedSupportActivity
#print axioms couplingParametricKEventNumerator_eqv_supportMasked
#print axioms couplingParametricKSupportMasked_eqv_ambientMasked
#print axioms couplingParametricKAmbientMasked_eqv_compatibleEventNumerator
#print axioms couplingParametricKEventNumerator_eqv_compatibleEventNumerator
#print axioms couplingParametricKCompatibleSupportGasPartition_pos
#print axioms couplingKFamilyEventProbability_eqv_compatible

end YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
