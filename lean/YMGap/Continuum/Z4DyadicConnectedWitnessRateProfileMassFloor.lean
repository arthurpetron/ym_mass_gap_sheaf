/-
# The two-scale profile pays the connected spatial separation

The corridor contraction exposes one anchor power indexed by the sum of the
fine/coarse exterior/core counters.  This file identifies its geometric
content.  The coarse canonical peel clears the entire target-support
component.  Every face of that component initially carries positive
twice-spin mass, so the coarse trace mass dominates the component cardinality.
The complete four-counter mass therefore dominates both component size and
the observable-to-source separation.

Consequently the pointwise corridor estimate can be weakened to an explicit
spatial anchor power.  This is still a terminal-weight estimate; summing its
inverse fibers is the next obligation.

Constructive contract: finite support inclusion, canonical-peel mass
telescope, exact profile identity, and rational power antitonicity only; no
classical choice, proof hole, trusted external computation, computability
escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass
import YMGap.Continuum.Z4DyadicConnectedWitnessRateCouplingProfileCorridor

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateProfileMassFloor

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingHighSpinProfile
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicAcceptedStateCouplingRebase
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentHeatBudget
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentShapeChildWeightedCarrier
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentSlackDecomposition
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedDependentCarrier
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedMassFloor
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicConnectedExpandedWitnessCompilerFaithfulness
open YMGap.Continuum.Z4DyadicConnectedFourEntryComponentPeeling
open YMGap.Continuum.Z4DyadicConnectedWitnessRateCouplingProfileCorridor
open YMGap.Continuum.Z4DyadicConnectedWitnessRateCouplingProfiledTerminalDomination
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalDomination
open YMGap.Continuum.Z4DyadicConnectedWitnessRateWeightedPeeling
open YMGap.Continuum.Z4DyadicJointUnitReferenceExpandedWitness
open YMGap.Continuum.Z4DyadicLocalizedUnitTargetExpandedWitness
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

private theorem range_nodup_local (N : Nat) : (List.range N).Nodup := by
  induction N with
  | zero => exact List.nodup_nil
  | succ N ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro x hx y hy hxy
      have hyN : y = N := List.mem_singleton.mp hy
      rw [hxy, hyN] at hx
      exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl N)

private theorem list_length_le_listNatWeight_of_one_le_local
    {A : Type} (weight : A → Nat) : ∀ items : List A,
    (∀ item, item ∈ items → 1 ≤ weight item) →
      items.length ≤ listNatWeight weight items
  | [], _ => Nat.le_refl 0
  | head :: tail, hweight => by
      have hhead := hweight head List.mem_cons_self
      have htail := list_length_le_listNatWeight_of_one_le_local
        weight tail (fun item hitem =>
          hweight item (List.mem_cons_of_mem head hitem))
      simp only [List.length_cons, listNatWeight]
      omega

/-! ## 1. The enumerated coarse scan is the whole connected component -/

theorem finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_nodup
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
      S orientation observableFaceId entry).Nodup := by
  unfold finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
  apply List.filter_sublist.nodup
  unfold SlabPhysicalData.faceEdges slabPhysicalFaceEdges
  exact range_nodup_local _

theorem finePacketGlobalNonzeroConnectedEntryTargetComponent_mem_coarseComponentFaces
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId)
    (faceId : Nat)
    (hface : faceId ∈
      finePacketGlobalConnectedEntryTargetComponent
        S observableFaceId entry.1) :
    faceId ∈ finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
      S orientation observableFaceId entry := by
  unfold finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
  apply List.mem_filter.mpr
  refine ⟨?_, decide_eq_true hface⟩
  exact finePacketObservableTargetSupportComponent_face_mem_physical
    S entry.1.targets observableFaceId hobservableFace
      (finePacketGlobalConnectedEntryPath
        S observableFaceId hobservableFace entry.1).observable_targetStates_ne
      faceId hface

/-! ## 2. The coarse profile alone pays component cardinality -/

theorem finePacketGlobalNonzeroConnectedExpandedWitness_componentSize_le_coarseRateProfileMass
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    let result :=
      finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
        S rate hrate0 orientation observableFaceId hobservableFace expanded
    finePacketGlobalNonzeroConnectedEntryComponentSize
        S orientation observableFaceId expanded.1 ≤
      result.2.2.2.1 + result.2.2.2.2 := by
  let coarseD := finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0
  let coarseFaces :=
    finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
      S orientation observableFaceId expanded.1
  let coarsePhysical :=
    finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_mem_ratePhysical
      S rate hrate0 orientation observableFaceId hobservableFace expanded.1
  let unitCoarseState :=
    finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
      S expanded.2.1
  let coarseState := slabAcceptedTwoReplicaStateAtCoupling
    (coarseUnitCouplingSlabPhysicalData S) rate hrate0 unitCoarseState
  let coarseResult := slabAcceptedPairCanonicalHighSpinProfile
    coarseD (anchorPaidExteriorThreshold rate)
      coarseFaces coarsePhysical coarseState
  let targetComponent :=
    finePacketGlobalConnectedEntryTargetComponent
      S observableFaceId expanded.1.1
  let targetWeight : Nat → Nat := fun faceId =>
    expanded.1.1.targets.1 faceId + expanded.1.1.targets.2 faceId
  have hfacesNodup : coarseFaces.Nodup :=
    finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_nodup
      S orientation observableFaceId expanded.1
  have hcomponentNodup : targetComponent.Nodup := by
    unfold targetComponent finePacketGlobalConnectedEntryTargetComponent
    exact rootComponent_nodup _ _ _
  have hcomponentSubset : ∀ faceId, faceId ∈ targetComponent →
      faceId ∈ coarseFaces := by
    intro faceId hface
    exact
      finePacketGlobalNonzeroConnectedEntryTargetComponent_mem_coarseComponentFaces
        S orientation observableFaceId hobservableFace expanded.1 faceId hface
  have hcomponentLength : targetComponent.length ≤
      listNatWeight targetWeight targetComponent := by
    apply list_length_le_listNatWeight_of_one_le_local
    intro faceId hface
    have hpositive :=
      finePacketObservableTargetSupportComponent_face_positive
        S expanded.1.1.targets observableFaceId hobservableFace
          (finePacketGlobalConnectedEntryPath
            S observableFaceId hobservableFace
              expanded.1.1).observable_targetStates_ne
          faceId hface
    unfold targetWeight
    rcases hpositive with hleft | hright <;> omega
  have hcomponentMassSubset :
      listNatWeight targetWeight targetComponent ≤
        listNatWeight targetWeight coarseFaces :=
    listNatWeight_le_of_nodup_mem targetWeight targetComponent coarseFaces
      hcomponentNodup hcomponentSubset
  have hleft :=
    finePacketOrientedJointUnitExpandedWitness_coarseFirst_physical_eq
      S orientation expanded.1.1.sources.1 expanded.1.1.sources.2
        expanded.1.1.targets
        (finePacketGlobalNonzeroConnectedEntry_leftTarget_mem_physical
          S orientation observableFaceId expanded.1)
        (finePacketGlobalNonzeroConnectedEntry_rightTarget_mem_physical
          S orientation observableFaceId expanded.1)
        expanded.2.1 expanded.2.2
  have hright :=
    finePacketOrientedJointUnitExpandedWitness_coarseSecond_physical_eq
      S orientation expanded.1.1.sources.1 expanded.1.1.sources.2
        expanded.1.1.targets
        (finePacketGlobalNonzeroConnectedEntry_leftTarget_mem_physical
          S orientation observableFaceId expanded.1)
        (finePacketGlobalNonzeroConnectedEntry_rightTarget_mem_physical
          S orientation observableFaceId expanded.1)
        expanded.2.1 expanded.2.2
  have hleftRate : coarseState.1.1.1 = expanded.1.1.targets.1 := by
    exact hleft
  have hrightRate : coarseState.2.1.1 = expanded.1.1.targets.2 := by
    exact hright
  have hpeelMass :=
    slabAcceptedPairCanonicalPeeling_componentMass_le_traceMass
      coarseD coarseFaces hfacesNodup coarsePhysical coarseState
  rw [hleftRate, hrightRate] at hpeelMass
  have hterminalTrace :=
    slabAcceptedPairCanonicalHighSpinProfile_terminal_trace
      coarseD (anchorPaidExteriorThreshold rate)
        coarseFaces coarsePhysical coarseState
  have htrace := congrArg Prod.snd hterminalTrace
  change coarseResult.2.1 =
    (slabAcceptedPairCanonicalPeeling
      coarseD coarseFaces coarsePhysical coarseState).2 at htrace
  rw [← htrace] at hpeelMass
  have hprofileMass :=
    slabAcceptedPairCanonicalHighSpinProfile_traceMass
      coarseD (anchorPaidExteriorThreshold rate)
        coarseFaces coarsePhysical coarseState
  change slabAcceptedPairedPeelTraceMass coarseResult.2.1 =
    coarseResult.2.2.1 + coarseResult.2.2.2 at hprofileMass
  rw [hprofileMass] at hpeelMass
  change targetComponent.length ≤ coarseResult.2.2.1 + coarseResult.2.2.2
  exact Nat.le_trans hcomponentLength
    (Nat.le_trans hcomponentMassSubset hpeelMass)

/-! ## 3. Complete profile mass pays component size and separation -/

theorem finePacketGlobalNonzeroConnectedExpandedWitness_componentSize_le_rateTotalProfileMass
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    finePacketGlobalNonzeroConnectedEntryComponentSize
        S orientation observableFaceId expanded.1 ≤
      finePacketGlobalNonzeroConnectedExpandedWitnessRateTotalProfileMass
        S rate hrate0 orientation observableFaceId hobservableFace expanded := by
  let result :=
    finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
      S rate hrate0 orientation observableFaceId hobservableFace expanded
  have hcoarse :=
    finePacketGlobalNonzeroConnectedExpandedWitness_componentSize_le_coarseRateProfileMass
      S rate hrate0 orientation observableFaceId hobservableFace expanded
  have hcoarse' :
      finePacketGlobalNonzeroConnectedEntryComponentSize
          S orientation observableFaceId expanded.1 ≤
        result.2.2.2.1 + result.2.2.2.2 := by
    simpa only [result] using hcoarse
  change
    finePacketGlobalNonzeroConnectedEntryComponentSize
        S orientation observableFaceId expanded.1 ≤
      (result.1.2.2.1 + result.1.2.2.2) +
        (result.2.2.2.1 + result.2.2.2.2)
  omega

theorem finePacketGlobalNonzeroConnectedExpandedWitness_distance_le_rateTotalProfileMass
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    finePacketGlobalNonzeroConnectedEntryDistance
        S orientation observableFaceId hobservableFace expanded.1 ≤
      finePacketGlobalNonzeroConnectedExpandedWitnessRateTotalProfileMass
        S rate hrate0 orientation observableFaceId hobservableFace expanded := by
  exact Nat.le_trans
    (finePacketGlobalNonzeroConnectedEntry_distance_le_componentSize
      S orientation observableFaceId hobservableFace expanded.1)
    (finePacketGlobalNonzeroConnectedExpandedWitness_componentSize_le_rateTotalProfileMass
      S rate hrate0 orientation observableFaceId hobservableFace expanded)

#print axioms finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_nodup
#print axioms finePacketGlobalNonzeroConnectedEntryTargetComponent_mem_coarseComponentFaces
#print axioms finePacketGlobalNonzeroConnectedExpandedWitness_componentSize_le_coarseRateProfileMass
#print axioms finePacketGlobalNonzeroConnectedExpandedWitness_componentSize_le_rateTotalProfileMass
#print axioms finePacketGlobalNonzeroConnectedExpandedWitness_distance_le_rateTotalProfileMass

end YMGap.Continuum.Z4DyadicConnectedWitnessRateProfileMassFloor
