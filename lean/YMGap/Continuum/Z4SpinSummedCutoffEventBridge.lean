/-
# Arbitrary-cutoff physical-to-compatible event bridge

The cutoff-cofinal measure is enumerated by physical face labellings, whereas
the thermodynamic cylinder estimates are enumerated by compatible connected
support families.  A physical event lifted from a family predicate is constant
on every exact excited-support fibre.  Summing fibrewise and then decomposing
the support into its canonical connected family therefore identifies the two
event numerators at every representation cutoff, not only at cutoff one.
-/

import YMGap.Continuum.Z4CutoffOneEventBridge
import YMGap.Continuum.Z4SpinSummedCrossVolumeCylinder

namespace YMGap.Continuum.Z4SpinSummedCutoffEventBridge

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4AdjacentCutoffDyadicSchedule
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ConditionalAuxiliaryMultiplicity
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4SpinSummedCompatibleGas
open YMGap.Continuum.Z4SpinSummedCrossVolumeCylinder
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4SpinSummedSupportComponentLower
open YMGap.Continuum.Z4SpinSummedSupportComponentUpper
open YMGap.Continuum.Z4SpinSummedSupportPartition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A family event is constant on each exact support fibre -/

theorem physicalCanonicalAmbientFamily_of_mem_supportFiber
    {cutoff n : Nat} {support : List Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈
      physicalLabellingsWithSupport cutoff n support) :
    physicalCanonicalAmbientFamily n physical =
      ambientOrderedFamily n (canonicalSurfaceFamily n support) := by
  unfold physicalCanonicalAmbientFamily
  rw [(mem_physicalLabellingsWithSupport_iff.mp hphysical).2]

private theorem listQSum_zero_local {A : Type} {f : A → Q'}
    : ∀ xs : List A, (∀ x, x ∈ xs → f x ≈ 0) →
      listQSum f xs ≈ 0
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hf => by
      change f head + listQSum f tail ≈ 0
      refine Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr'
          (hf head List.mem_cons_self)
          (listQSum_zero_local tail
            (fun x hx => hf x (List.mem_cons_of_mem head hx)))) ?_
      exact Q'.eqv_of_eq (Q'.zero_add' 0)

theorem parametricKEventFiberSum_eqv_maskedSupportActivity
    (cutoff n : Nat) (event : List (List Nat) → Bool)
    (support : List Nat) :
    listQSum
        (parametricKEventTerm anchorCoupling cutoff n
          (cutoffOneLiftedFamilyEvent n event))
        (physicalLabellingsWithSupport cutoff n support) ≈
      if event (ambientOrderedFamily n (canonicalSurfaceFamily n support))
      then parametricKSupportActivity cutoff n support else 0 := by
  by_cases hevent :
      event (ambientOrderedFamily n (canonicalSurfaceFamily n support)) = true
  · rw [if_pos hevent]
    unfold parametricKSupportActivity
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

/-! ## 2. Reindexing the physical numerator through support fibres -/

def parametricKSupportMaskedFamilyEventNumerator
    (cutoff n : Nat) (event : List (List Nat) → Bool) : Q' :=
  listQSum
    (fun support =>
      if event (ambientOrderedFamily n (canonicalSurfaceFamily n support))
      then parametricKSupportActivity cutoff n support else 0)
    (cutoffOneFaceSupports n)

theorem anchorParametricKEventNumerator_eqv_supportMasked
    (cutoff n : Nat) (event : List (List Nat) → Bool) :
    parametricKEventNumerator anchorCoupling cutoff n
        (cutoffOneLiftedFamilyEvent n event) ≈
      parametricKSupportMaskedFamilyEventNumerator cutoff n event := by
  unfold parametricKEventNumerator
  refine Q'.eqv_trans _
    (listQSum
      (parametricKEventTerm anchorCoupling cutoff n
        (cutoffOneLiftedFamilyEvent n event))
      (parametricKSupportFibers cutoff n)) _ ?_ ?_
  · exact listQSum_perm _
      (boundedEdgeLabellings_perm_supportFibers cutoff n)
  unfold parametricKSupportFibers
    parametricKSupportMaskedFamilyEventNumerator
  refine Q'.eqv_trans _
    (listQSum
      (fun support =>
        listQSum
          (parametricKEventTerm anchorCoupling cutoff n
            (cutoffOneLiftedFamilyEvent n event))
          (physicalLabellingsWithSupport cutoff n support))
      (cutoffOneFaceSupports n)) _
    (listQSum_flatMap _ _ _) ?_
  apply listQSum_congr_on
  intro support _
  exact parametricKEventFiberSum_eqv_maskedSupportActivity
    cutoff n event support

/-! ## 3. Reindexing masked supports into compatible families -/

def parametricKAmbientMaskedFamilyEventNumerator
    (cutoff n : Nat) (event : List (List Nat) → Bool) : Q' :=
  listQSum
    (fun family => if event family
      then parametricKSupportFamilyActivity cutoff n family else 0)
    (ambientOrderedExactGas n)

private theorem maskedSupportActivity_eqv_ambientFamilyActivity
    (cutoff n : Nat) (event : List (List Nat) → Bool)
    {support : List Nat} (hsupport : support ∈ cutoffOneFaceSupports n) :
    (if event (ambientOrderedFamily n (canonicalSurfaceFamily n support))
      then parametricKSupportActivity cutoff n support else 0) ≈
    (if event (ambientOrderedFamily n (canonicalSurfaceFamily n support))
      then parametricKSupportFamilyActivity cutoff n
        (ambientOrderedFamily n (canonicalSurfaceFamily n support)) else 0) := by
  by_cases hevent :
      event (ambientOrderedFamily n (canonicalSurfaceFamily n support)) = true
  · rw [if_pos hevent, if_pos hevent]
    exact Q'.eqv_trans _ _ _
      (parametricKSupportActivity_eqv_componentFamilyActivity
        cutoff n support hsupport)
      (parametricKGasFamilyActivity_eqv_ambientOrdered cutoff
        (canonicalSurfaceFamily_mem_connectedGas hsupport))
  · rw [if_neg hevent, if_neg hevent]
    exact Q'.eqv_refl 0

theorem parametricKSupportMasked_eqv_ambientMasked
    (cutoff n : Nat) (event : List (List Nat) → Bool) :
    parametricKSupportMaskedFamilyEventNumerator cutoff n event ≈
      parametricKAmbientMaskedFamilyEventNumerator cutoff n event := by
  unfold parametricKSupportMaskedFamilyEventNumerator
    parametricKAmbientMaskedFamilyEventNumerator
    ambientOrderedExactGas canonicalConnectedSurfaceGas
  rw [List.map_map]
  apply listQSum_map_eqv
  intro support hsupport
  exact maskedSupportActivity_eqv_ambientFamilyActivity
    cutoff n event hsupport

private theorem listQSum_mask_eq_filter_local {A : Type}
    (weight : A → Q') (event : A → Bool) :
    ∀ xs : List A,
      listQSum (fun item => if event item then weight item else 0) xs ≈
        listQSum weight (xs.filter event)
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

theorem parametricKAmbientMasked_eqv_compatibleEventNumerator
    (cutoff n : Nat) (event : List (List Nat) → Bool) :
    parametricKAmbientMaskedFamilyEventNumerator cutoff n event ≈
      parametricKCompatibleSupportEventNumerator cutoff n event := by
  let masked : List (List Nat) → Q' := fun family =>
    if event family
    then parametricKSupportFamilyActivity cutoff n family else 0
  have hperm :
      listQSum masked (ambientOrderedExactGas n) ≈
        listQSum masked (canonicalCompatibleAmbientFamilies n) :=
    listQSum_perm masked (ambientOrderedExactGas_perm_compatibleFamilies n)
  have hfilter := listQSum_mask_eq_filter_local
    (parametricKSupportFamilyActivity cutoff n) event
    (canonicalCompatibleAmbientFamilies n)
  unfold parametricKAmbientMaskedFamilyEventNumerator
    parametricKCompatibleSupportEventNumerator
  dsimp only [masked] at hperm
  exact Q'.eqv_trans _ _ _ hperm hfilter

/-- **Arbitrary-cutoff event-numerator bridge.** -/
theorem anchorParametricKEventNumerator_eqv_compatibleEventNumerator
    (cutoff n : Nat) (event : List (List Nat) → Bool) :
    parametricKEventNumerator anchorCoupling cutoff n
        (cutoffOneLiftedFamilyEvent n event) ≈
      parametricKCompatibleSupportEventNumerator cutoff n event :=
  Q'.eqv_trans _ _ _
    (anchorParametricKEventNumerator_eqv_supportMasked cutoff n event)
    (Q'.eqv_trans _ _ _
      (parametricKSupportMasked_eqv_ambientMasked cutoff n event)
      (parametricKAmbientMasked_eqv_compatibleEventNumerator
        cutoff n event))

/-! ## 4. Normalized laws and the scheduled cutoff sequence -/

def anchorParametricKLiftedFamilyEventProbability
    (cutoff n : Nat) (hcutoff : 1 ≤ cutoff)
    (event : List (List Nat) → Bool) : Q' :=
  Q'.divPos
    (parametricKEventNumerator anchorCoupling cutoff n
      (cutoffOneLiftedFamilyEvent n event))
    (parametricKPhysicalPartition anchorCoupling cutoff n)
    (anchorParametricPartition_pos hcutoff n)

theorem anchorParametricKLiftedFamilyEventProbability_eqv_compatible
    (cutoff n : Nat) (hcutoff : 1 ≤ cutoff)
    (event : List (List Nat) → Bool) :
    anchorParametricKLiftedFamilyEventProbability
        cutoff n hcutoff event ≈
      parametricKCompatibleSupportEventProbability cutoff n event := by
  unfold anchorParametricKLiftedFamilyEventProbability
    parametricKCompatibleSupportEventProbability
  exact divPos_eqv_congr
    (anchorParametricPartition_pos hcutoff n)
    (parametricKCompatibleSupportGasPartition_pos cutoff n)
    (anchorParametricKEventNumerator_eqv_compatibleEventNumerator
      cutoff n event)
    (parametricKPhysicalPartition_eqv_compatibleSupportGas cutoff n)

theorem interactingAdjacentCutoff_ge_one
    (stage n : Nat) : 1 ≤ interactingAdjacentCutoff stage n := by
  unfold interactingAdjacentCutoff
  omega

theorem anchorParametricCutoffProbabilitySequence_eqv_compatible
    (n : Nat) (event : List (List Nat) → Bool) (stage : Nat) :
    anchorParametricCutoffEventProbabilitySequence n
        (cutoffOneLiftedFamilyEvent n event) stage ≈
      parametricKCompatibleSupportEventProbability
        (interactingAdjacentCutoff stage n) n event := by
  change anchorParametricKLiftedFamilyEventProbability
      (interactingAdjacentCutoff stage n) n
        (interactingAdjacentCutoff_ge_one stage n) event ≈
    parametricKCompatibleSupportEventProbability
      (interactingAdjacentCutoff stage n) n event
  exact anchorParametricKLiftedFamilyEventProbability_eqv_compatible
    (interactingAdjacentCutoff stage n) n
      (interactingAdjacentCutoff_ge_one stage n) event

#print axioms parametricKEventFiberSum_eqv_maskedSupportActivity
#print axioms anchorParametricKEventNumerator_eqv_supportMasked
#print axioms parametricKSupportMasked_eqv_ambientMasked
#print axioms anchorParametricKEventNumerator_eqv_compatibleEventNumerator
#print axioms anchorParametricKLiftedFamilyEventProbability_eqv_compatible
#print axioms anchorParametricCutoffProbabilitySequence_eqv_compatible

end YMGap.Continuum.Z4SpinSummedCutoffEventBridge
