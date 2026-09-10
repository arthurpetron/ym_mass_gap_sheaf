/-
# Finite local SU(2) code on the connected component

At every face of a nonzero oriented target-support component there are four
cutoff-four labels: two packet-total source spins and two coarse target
spins.  Both targets lie in their assigned parity-preserving lowering rows,
and at least one target is positive.

This module enumerates that finite local state space, proves by kernel
reduction that it has exactly 72 elements, and compiles every component face
to a member.  It also proves that the sum of `(local activity - 1)` along the
resulting word is exactly the component's total local-activity excess.

The catalogue count is a Lean certificate (`by decide`), not trusted output
from an external enumerator.  Rust is unnecessary for this 625-case search;
it remains available for larger recoupling certificates.

Constructive contract: finite ranges, list filters, decidable propositions,
and bounded natural arithmetic only; no classical choice, proof hole,
trusted external computation, noncomputable declaration, enlarged heartbeat
budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryConnectedComponentSlackDecomposition

namespace YMGap.Continuum.Z4DyadicBinaryConnectedComponentLocalCode

set_option autoImplicit false

open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4BoundedEdgeLabellingNodup
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentHeatBudget
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentSlackDecomposition
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedDependentCarrier
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourceParityExcitationSplit
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedMassFloor
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedSwapObstruction
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicSpinFourLoweringDownset
open YMGap.Continuum.Z4ExplicitSpinFoamBounds

/-! ## 1. The complete 72-state local catalogue -/

structure FinePacketComponentLocalCode : Type where
  leftSource : Nat
  rightSource : Nat
  leftTarget : Nat
  rightTarget : Nat
deriving DecidableEq

def FinePacketComponentLocalCode.Admissible
    (code : FinePacketComponentLocalCode) : Prop :=
  code.leftSource ≤ 4 ∧
    code.rightSource ≤ 4 ∧
    code.leftTarget ≤ 4 ∧
    code.rightTarget ≤ 4 ∧
    spinFourLoweringCompatible code.leftSource code.leftTarget ∧
    spinFourLoweringCompatible code.rightSource code.rightTarget ∧
    (0 < code.leftTarget ∨ 0 < code.rightTarget)

instance (code : FinePacketComponentLocalCode) : Decidable code.Admissible := by
  unfold FinePacketComponentLocalCode.Admissible spinFourLoweringCompatible
  infer_instance

def finePacketComponentRawLocalCodes :
    List FinePacketComponentLocalCode :=
  (List.range 5).flatMap fun leftSource =>
    (List.range 5).flatMap fun rightSource =>
      (List.range 5).flatMap fun leftTarget =>
        (List.range 5).map fun rightTarget =>
          { leftSource := leftSource
            rightSource := rightSource
            leftTarget := leftTarget
            rightTarget := rightTarget }

def finePacketComponentLocalCodes :
    List FinePacketComponentLocalCode :=
  finePacketComponentRawLocalCodes.filter fun code =>
    decide code.Admissible

/-- The complete bounded, supported, positive local lowering catalogue has
72 states.  The proof term is produced by reduction inside Lean. -/
theorem finePacketComponentLocalCodes_length :
    finePacketComponentLocalCodes.length = 72 := by
  decide

def FinePacketComponentLocalCode.activity
    (code : FinePacketComponentLocalCode) : Nat :=
  code.leftSource + code.rightSource +
    spinFourParityExcitationLevel code.leftSource code.leftTarget +
    spinFourParityExcitationLevel code.rightSource code.rightTarget

theorem FinePacketComponentLocalCode.one_le_activity
    (code : FinePacketComponentLocalCode) (hcode : code.Admissible) :
    1 ≤ code.activity := by
  exact spinFourSupportedPositivePair_jointActivity_one_le
    hcode.1 hcode.2.1 hcode.2.2.1 hcode.2.2.2.1
      hcode.2.2.2.2.1 hcode.2.2.2.2.2.1 hcode.2.2.2.2.2.2

/-- Number of admissible local codes at each activity `0, ..., 12`. -/
def finePacketComponentLocalActivityHistogram : List Nat :=
  (List.range 13).map fun activity =>
    (finePacketComponentLocalCodes.filter fun code =>
      decide (code.activity = activity)).length

/-- Kernel-checked weighted-entropy data for the local catalogue.  In
particular there are only two minimal-activity states; all other local codes
pay positive activity-excess heat. -/
theorem finePacketComponentLocalActivityHistogram_exact :
    finePacketComponentLocalActivityHistogram =
      [0, 2, 1, 6, 6, 10, 10, 12, 9, 8, 5, 2, 1] := by
  decide

/-! ## 2. Compile one literal component face -/

def finePacketGlobalNonzeroConnectedEntryLocalCodeAt
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId faceId : Nat)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) : FinePacketComponentLocalCode :=
  { leftSource := finePacketOrientedLeftSource
      S orientation entry.1.sources.1.1 entry.1.sources.2.1 faceId
    rightSource := finePacketOrientedRightSource
      S orientation entry.1.sources.1.1 entry.1.sources.2.1 faceId
    leftTarget := entry.1.targets.1 faceId
    rightTarget := entry.1.targets.2 faceId }

private theorem finePacketGlobalNonzeroConnectedEntry_leftSource_le_four
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId)
    (faceId : Nat) (hface : faceId ∈ S.coarse.faceEdges) :
    finePacketOrientedLeftSource
      S orientation entry.1.sources.1.1 entry.1.sources.2.1 faceId ≤ 4 := by
  cases orientation with
  | forward =>
      exact wholeSlabFinePacketTotalLabelling_le_four
        S hfineCutoff entry.1.sources.1.2.1 faceId hface
  | reverse =>
      exact wholeSlabFinePacketTotalLabelling_le_four
        S hfineCutoff entry.1.sources.2.2.1 faceId hface

private theorem finePacketGlobalNonzeroConnectedEntry_rightSource_le_four
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId)
    (faceId : Nat) (hface : faceId ∈ S.coarse.faceEdges) :
    finePacketOrientedRightSource
      S orientation entry.1.sources.1.1 entry.1.sources.2.1 faceId ≤ 4 := by
  cases orientation with
  | forward =>
      exact wholeSlabFinePacketTotalLabelling_le_four
        S hfineCutoff entry.1.sources.2.2.1 faceId hface
  | reverse =>
      exact wholeSlabFinePacketTotalLabelling_le_four
        S hfineCutoff entry.1.sources.1.2.1 faceId hface

private theorem coarseTargetSpin_le_four_local
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    {target : EdgeLabelling} (htarget : target ∈ S.coarse.physicalLabellings)
    (faceId : Nat) (hface : faceId ∈ S.coarse.faceEdges) :
    target faceId ≤ 4 := by
  have hbound := Nat.le_of_lt_succ
    ((boundedEdgeLabellings_sound
      S.coarse.cutoff S.coarse.faceEdges target htarget).1 faceId hface)
  rw [S.coarse_cutoff, hfineCutoff] at hbound
  omega

private theorem finePacketComponentRawLocalCodes_mem
    (code : FinePacketComponentLocalCode)
    (hleftSource : code.leftSource ≤ 4)
    (hrightSource : code.rightSource ≤ 4)
    (hleftTarget : code.leftTarget ≤ 4)
    (hrightTarget : code.rightTarget ≤ 4) :
    code ∈ finePacketComponentRawLocalCodes := by
  unfold finePacketComponentRawLocalCodes
  apply List.mem_flatMap.mpr
  refine ⟨code.leftSource, List.mem_range.mpr (by omega), ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨code.rightSource, List.mem_range.mpr (by omega), ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨code.leftTarget, List.mem_range.mpr (by omega), ?_⟩
  exact List.mem_map.mpr
    ⟨code.rightTarget, List.mem_range.mpr (by omega), by cases code; rfl⟩

theorem finePacketGlobalNonzeroConnectedEntryLocalCodeAt_mem
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId)
    (faceId : Nat)
    (hcomponent : faceId ∈ finePacketGlobalConnectedEntryTargetComponent
      S observableFaceId entry.1) :
    finePacketGlobalNonzeroConnectedEntryLocalCodeAt
        S orientation observableFaceId faceId entry ∈
      finePacketComponentLocalCodes := by
  let path := finePacketGlobalConnectedEntryPath
    S observableFaceId hobservableFace entry.1
  have hface :=
    finePacketObservableTargetSupportComponent_face_mem_physical
      S entry.1.targets observableFaceId hobservableFace
        path.observable_targetStates_ne faceId hcomponent
  have hlowering :=
    finePacketGlobalOrientedNonzeroConnectedEntryLowering
      S hfineCutoff orientation observableFaceId entry
  have hleftRow := (mem_spinFourLoweringTargets_iff S _ _).mp hlowering.1
  have hrightRow := (mem_spinFourLoweringTargets_iff S _ _).mp hlowering.2
  have hleftSource :=
    finePacketGlobalNonzeroConnectedEntry_leftSource_le_four
      S hfineCutoff orientation observableFaceId entry faceId hface
  have hrightSource :=
    finePacketGlobalNonzeroConnectedEntry_rightSource_le_four
      S hfineCutoff orientation observableFaceId entry faceId hface
  have hleftTarget := coarseTargetSpin_le_four_local
    S hfineCutoff hleftRow.1 faceId hface
  have hrightTarget := coarseTargetSpin_le_four_local
    S hfineCutoff hrightRow.1 faceId hface
  have hpositive :=
    finePacketObservableTargetSupportComponent_face_positive
      S entry.1.targets observableFaceId hobservableFace
        path.observable_targetStates_ne faceId hcomponent
  apply List.mem_filter.mpr
  refine ⟨finePacketComponentRawLocalCodes_mem
    (finePacketGlobalNonzeroConnectedEntryLocalCodeAt
      S orientation observableFaceId faceId entry)
    hleftSource hrightSource hleftTarget hrightTarget, ?_⟩
  simp only [decide_eq_true_eq]
  exact ⟨hleftSource, hrightSource, hleftTarget, hrightTarget,
    hleftRow.2 faceId hface, hrightRow.2 faceId hface, hpositive⟩

/-! ## 3. The component word and its exact excess statistic -/

def finePacketGlobalNonzeroConnectedEntryLocalCode
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    List FinePacketComponentLocalCode :=
  (finePacketGlobalConnectedEntryTargetComponent
    S observableFaceId entry.1).map fun faceId =>
      finePacketGlobalNonzeroConnectedEntryLocalCodeAt
        S orientation observableFaceId faceId entry

theorem finePacketGlobalNonzeroConnectedEntryLocalCode_mem_catalogue
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId)
    (code : FinePacketComponentLocalCode)
    (hcode : code ∈ finePacketGlobalNonzeroConnectedEntryLocalCode
      S orientation observableFaceId entry) :
    code ∈ finePacketComponentLocalCodes := by
  unfold finePacketGlobalNonzeroConnectedEntryLocalCode at hcode
  obtain ⟨faceId, hcomponent, rfl⟩ := List.mem_map.mp hcode
  exact finePacketGlobalNonzeroConnectedEntryLocalCodeAt_mem
    S hfineCutoff orientation observableFaceId hobservableFace entry
      faceId hcomponent

theorem finePacketGlobalNonzeroConnectedEntryLocalCode_activity_total
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    listNatWeight FinePacketComponentLocalCode.activity
        (finePacketGlobalNonzeroConnectedEntryLocalCode
          S orientation observableFaceId entry) =
      finePacketGlobalNonzeroConnectedEntryComponentActivity
        S orientation observableFaceId entry := by
  unfold finePacketGlobalNonzeroConnectedEntryLocalCode
    finePacketGlobalNonzeroConnectedEntryComponentActivity
    finePacketOrientedObservableJointActivityMass
  rw [listNatWeight_map]
  rfl

private theorem list_length_le_listNatWeight_of_one_le
    {A : Type} (weight : A → Nat) : ∀ items : List A,
    (∀ item, item ∈ items → 1 ≤ weight item) →
    items.length ≤ listNatWeight weight items
  | [], _ => Nat.le_refl 0
  | head :: tail, hone => by
      have hhead := hone head List.mem_cons_self
      have htail := list_length_le_listNatWeight_of_one_le weight tail
        (fun item hitem => hone item (List.mem_cons_of_mem head hitem))
      simp only [List.length_cons, listNatWeight]
      omega

private theorem listNatWeight_sub_one_eq_total_sub_length
    {A : Type} (weight : A → Nat) : ∀ items : List A,
    (∀ item, item ∈ items → 1 ≤ weight item) →
    listNatWeight (fun item => weight item - 1) items =
      listNatWeight weight items - items.length
  | [], _ => rfl
  | head :: tail, hone => by
      have hhead := hone head List.mem_cons_self
      have htailLe := list_length_le_listNatWeight_of_one_le weight tail
        (fun item hitem => hone item (List.mem_cons_of_mem head hitem))
      have htail := listNatWeight_sub_one_eq_total_sub_length weight tail
        (fun item hitem => hone item (List.mem_cons_of_mem head hitem))
      simp only [listNatWeight, List.length_cons]
      rw [htail]
      omega

theorem finePacketGlobalNonzeroConnectedEntryLocalCode_excess_total
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    listNatWeight
        (fun code : FinePacketComponentLocalCode => code.activity - 1)
        (finePacketGlobalNonzeroConnectedEntryLocalCode
          S orientation observableFaceId entry) =
      finePacketGlobalNonzeroConnectedEntryComponentActivity
          S orientation observableFaceId entry -
        finePacketGlobalNonzeroConnectedEntryComponentSize
          S orientation observableFaceId entry := by
  rw [listNatWeight_sub_one_eq_total_sub_length]
  · rw [finePacketGlobalNonzeroConnectedEntryLocalCode_activity_total]
    unfold finePacketGlobalNonzeroConnectedEntryLocalCode
      finePacketGlobalNonzeroConnectedEntryComponentSize
    rw [List.length_map]
  · intro code hcode
    have hcatalogue :=
      finePacketGlobalNonzeroConnectedEntryLocalCode_mem_catalogue
        S hfineCutoff orientation observableFaceId hobservableFace entry
          code hcode
    have hadmissible := of_decide_eq_true (List.mem_filter.mp hcatalogue).2
    exact code.one_le_activity hadmissible

theorem finePacketGlobalNonzeroConnectedEntryLocalCode_scaledExcess_eq_heat
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    3 * listNatWeight
        (fun code : FinePacketComponentLocalCode => code.activity - 1)
        (finePacketGlobalNonzeroConnectedEntryLocalCode
          S orientation observableFaceId entry) =
      finePacketGlobalNonzeroConnectedEntryLocalActivityExcessHeat
        S orientation observableFaceId entry := by
  rw [finePacketGlobalNonzeroConnectedEntryLocalCode_excess_total
    S hfineCutoff orientation observableFaceId hobservableFace entry]
  rfl

/-! ## 4. Axiom audit -/

#print axioms FinePacketComponentLocalCode
#print axioms FinePacketComponentLocalCode.Admissible
#print axioms finePacketComponentRawLocalCodes
#print axioms finePacketComponentLocalCodes
#print axioms finePacketComponentLocalCodes_length
#print axioms FinePacketComponentLocalCode.activity
#print axioms FinePacketComponentLocalCode.one_le_activity
#print axioms finePacketComponentLocalActivityHistogram
#print axioms finePacketComponentLocalActivityHistogram_exact
#print axioms finePacketGlobalNonzeroConnectedEntryLocalCodeAt
#print axioms finePacketGlobalNonzeroConnectedEntryLocalCodeAt_mem
#print axioms finePacketGlobalNonzeroConnectedEntryLocalCode
#print axioms finePacketGlobalNonzeroConnectedEntryLocalCode_mem_catalogue
#print axioms finePacketGlobalNonzeroConnectedEntryLocalCode_activity_total
#print axioms finePacketGlobalNonzeroConnectedEntryLocalCode_excess_total
#print axioms finePacketGlobalNonzeroConnectedEntryLocalCode_scaledExcess_eq_heat

end YMGap.Continuum.Z4DyadicBinaryConnectedComponentLocalCode
