/-
# Refine the connected local code by the literal fine-child positions

The 72-state component code records only the two four-child packet totals
and the two coarse targets.  A background reconstruction must also know which
of the four cutoff-one fine children carry those totals.  This file makes that
finite datum explicit.

The resulting catalogue has 720 states, but only eight have minimal joint
activity.  All other 712 states carry at least one unit of activity excess.
That distinction is the input to the next weighted-entropy estimate: the
large nonminimal part is paid by the already-retained cubic heat factor,
rather than by enlarging the unweighted per-face entropy base from 72 to 720.

Constructive contract: literal finite packet enumeration and structural
component words only, with the repository trust boundary and heartbeat
budget unchanged.
-/

import YMGap.Continuum.Z4DyadicBinaryConnectedComponentEntropyFundedWeight

namespace YMGap.Continuum.Z4DyadicBinaryConnectedComponentChildCode

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentLocalCode
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentHeatBudget
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedDependentCarrier
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentSlackDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedSwapObstruction
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4DyadicSpinFourXorAssembly
open YMGap.Continuum.CompactDualCutoffOneCoarseFaceDoor
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel

/-! ## 1. The complete child-resolved local state -/

structure FinePacketComponentChildCode : Type where
  leftPacket : FaceSpinPacket
  rightPacket : FaceSpinPacket
  leftTarget : Nat
  rightTarget : Nat
deriving DecidableEq

def FinePacketComponentChildCode.toLocalCode
    (code : FinePacketComponentChildCode) :
    FinePacketComponentLocalCode where
  leftSource := faceSpinPacketTotal code.leftPacket
  rightSource := faceSpinPacketTotal code.rightPacket
  leftTarget := code.leftTarget
  rightTarget := code.rightTarget

def FinePacketComponentChildCode.Admissible
    (code : FinePacketComponentChildCode) : Prop :=
  PacketBinary code.leftPacket ∧
    PacketBinary code.rightPacket ∧
    code.toLocalCode.Admissible

instance (code : FinePacketComponentChildCode) :
    Decidable code.Admissible := by
  unfold FinePacketComponentChildCode.Admissible
    FinePacketComponentLocalCode.Admissible PacketBinary
    spinFourLoweringCompatible
  infer_instance

def finePacketComponentRawChildCodes :
    List FinePacketComponentChildCode :=
  (faceSpinPacketStateSpace 1).flatMap fun leftPacket =>
    (faceSpinPacketStateSpace 1).flatMap fun rightPacket =>
      (List.range 5).flatMap fun leftTarget =>
        (List.range 5).map fun rightTarget =>
          { leftPacket := leftPacket
            rightPacket := rightPacket
            leftTarget := leftTarget
            rightTarget := rightTarget }

def finePacketComponentChildCodes :
    List FinePacketComponentChildCode :=
  finePacketComponentRawChildCodes.filter fun code =>
    decide code.Admissible

/-- Resolving the four child positions refines the 72 total-spin states into
exactly 720 literal local states. -/
theorem finePacketComponentChildCodes_length :
    finePacketComponentChildCodes.length = 720 := by
  decide

def FinePacketComponentChildCode.activity
    (code : FinePacketComponentChildCode) : Nat :=
  code.toLocalCode.activity

def finePacketComponentMinimalChildCodes :
    List FinePacketComponentChildCode :=
  finePacketComponentChildCodes.filter fun code =>
    decide (code.activity = 1)

/-- Only eight child-resolved states have the minimal activity one. -/
theorem finePacketComponentMinimalChildCodes_length :
    finePacketComponentMinimalChildCodes.length = 8 := by
  decide

def finePacketComponentChildActivityHistogram : List Nat :=
  (List.range 13).map fun activity =>
    (finePacketComponentChildCodes.filter fun code =>
      decide (code.activity = activity)).length

/-- Exact child-resolved activity profile.  Its sum is 720 and its first
nonzero entry is the eight-state minimal sector. -/
theorem finePacketComponentChildActivityHistogram_exact :
    finePacketComponentChildActivityHistogram =
      [0, 8, 16, 68, 88, 162, 158, 120, 56, 30, 11, 2, 1] := by
  decide

/-! ## 2. Compile an actual cross-scale component face -/

def finePacketGlobalNonzeroConnectedEntryLeftChildPacketAt
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId faceId : Nat)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) : FaceSpinPacket :=
  match orientation with
  | .forward => wholeSlabFinePacket S entry.1.sources.1.1 faceId
  | .reverse => wholeSlabFinePacket S entry.1.sources.2.1 faceId

def finePacketGlobalNonzeroConnectedEntryRightChildPacketAt
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId faceId : Nat)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) : FaceSpinPacket :=
  match orientation with
  | .forward => wholeSlabFinePacket S entry.1.sources.2.1 faceId
  | .reverse => wholeSlabFinePacket S entry.1.sources.1.1 faceId

def finePacketGlobalNonzeroConnectedEntryChildCodeAt
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId faceId : Nat)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) : FinePacketComponentChildCode where
  leftPacket :=
    finePacketGlobalNonzeroConnectedEntryLeftChildPacketAt
      S orientation observableFaceId faceId entry
  rightPacket :=
    finePacketGlobalNonzeroConnectedEntryRightChildPacketAt
      S orientation observableFaceId faceId entry
  leftTarget := entry.1.targets.1 faceId
  rightTarget := entry.1.targets.2 faceId

theorem finePacketGlobalNonzeroConnectedEntryChildCodeAt_toLocalCode
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId faceId : Nat)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    (finePacketGlobalNonzeroConnectedEntryChildCodeAt
        S orientation observableFaceId faceId entry).toLocalCode =
      finePacketGlobalNonzeroConnectedEntryLocalCodeAt
        S orientation observableFaceId faceId entry := by
  cases orientation <;> rfl

private theorem finePacketComponentRawChildCodes_mem
    (code : FinePacketComponentChildCode)
    (hleftPacket : code.leftPacket ∈ faceSpinPacketStateSpace 1)
    (hrightPacket : code.rightPacket ∈ faceSpinPacketStateSpace 1)
    (hleftTarget : code.leftTarget ≤ 4)
    (hrightTarget : code.rightTarget ≤ 4) :
    code ∈ finePacketComponentRawChildCodes := by
  unfold finePacketComponentRawChildCodes
  apply List.mem_flatMap.mpr
  refine ⟨code.leftPacket, hleftPacket, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨code.rightPacket, hrightPacket, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨code.leftTarget, List.mem_range.mpr (by omega), ?_⟩
  exact List.mem_map.mpr
    ⟨code.rightTarget, List.mem_range.mpr (by omega), by cases code; rfl⟩

theorem finePacketGlobalNonzeroConnectedEntryChildCodeAt_mem
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId)
    (faceId : Nat)
    (hcomponent : faceId ∈ finePacketGlobalConnectedEntryTargetComponent
      S observableFaceId entry.1) :
    finePacketGlobalNonzeroConnectedEntryChildCodeAt
        S orientation observableFaceId faceId entry ∈
      finePacketComponentChildCodes := by
  let code := finePacketGlobalNonzeroConnectedEntryChildCodeAt
    S orientation observableFaceId faceId entry
  have hlocalMem :=
    finePacketGlobalNonzeroConnectedEntryLocalCodeAt_mem
      S hfineCutoff orientation observableFaceId hobservableFace entry
        faceId hcomponent
  have hlocal :
      (finePacketGlobalNonzeroConnectedEntryLocalCodeAt
        S orientation observableFaceId faceId entry).Admissible :=
    of_decide_eq_true (List.mem_filter.mp hlocalMem).2
  have hleftBinary : PacketBinary code.leftPacket := by
    cases orientation with
    | forward =>
        exact wholeSlabFinePacket_binary
          S hfineCutoff entry.1.sources.1.2.1 faceId
    | reverse =>
        exact wholeSlabFinePacket_binary
          S hfineCutoff entry.1.sources.2.2.1 faceId
  have hrightBinary : PacketBinary code.rightPacket := by
    cases orientation with
    | forward =>
        exact wholeSlabFinePacket_binary
          S hfineCutoff entry.1.sources.2.2.1 faceId
    | reverse =>
        exact wholeSlabFinePacket_binary
          S hfineCutoff entry.1.sources.1.2.1 faceId
  have hleftPacket : code.leftPacket ∈ faceSpinPacketStateSpace 1 :=
    (mem_faceSpinPacketStateSpace_iff 1 code.leftPacket).mpr hleftBinary
  have hrightPacket : code.rightPacket ∈ faceSpinPacketStateSpace 1 :=
    (mem_faceSpinPacketStateSpace_iff 1 code.rightPacket).mpr hrightBinary
  have hcodeLocal : code.toLocalCode.Admissible := by
    rw [finePacketGlobalNonzeroConnectedEntryChildCodeAt_toLocalCode]
    exact hlocal
  apply List.mem_filter.mpr
  refine ⟨finePacketComponentRawChildCodes_mem code hleftPacket hrightPacket
      hcodeLocal.2.2.1 hcodeLocal.2.2.2.1, ?_⟩
  simp only [decide_eq_true_eq]
  exact ⟨hleftBinary, hrightBinary, hcodeLocal⟩

/-! ## 3. The child-resolved component word -/

def finePacketGlobalNonzeroConnectedEntryChildCode
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    List FinePacketComponentChildCode :=
  (finePacketGlobalConnectedEntryTargetComponent
    S observableFaceId entry.1).map fun faceId =>
      finePacketGlobalNonzeroConnectedEntryChildCodeAt
        S orientation observableFaceId faceId entry

theorem finePacketGlobalNonzeroConnectedEntryChildCode_mem_catalogue
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId)
    (code : FinePacketComponentChildCode)
    (hcode : code ∈ finePacketGlobalNonzeroConnectedEntryChildCode
      S orientation observableFaceId entry) :
    code ∈ finePacketComponentChildCodes := by
  unfold finePacketGlobalNonzeroConnectedEntryChildCode at hcode
  obtain ⟨faceId, hcomponent, rfl⟩ := List.mem_map.mp hcode
  exact finePacketGlobalNonzeroConnectedEntryChildCodeAt_mem
    S hfineCutoff orientation observableFaceId hobservableFace entry
      faceId hcomponent

theorem finePacketGlobalNonzeroConnectedEntryChildCode_toLocalCode :
    ∀ (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
      (observableFaceId : Nat)
      (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
        S orientation observableFaceId),
    (finePacketGlobalNonzeroConnectedEntryChildCode
        S orientation observableFaceId entry).map
          FinePacketComponentChildCode.toLocalCode =
      finePacketGlobalNonzeroConnectedEntryLocalCode
        S orientation observableFaceId entry := by
  intro S orientation observableFaceId entry
  unfold finePacketGlobalNonzeroConnectedEntryChildCode
    finePacketGlobalNonzeroConnectedEntryLocalCode
  rw [List.map_map]
  apply List.map_congr_left
  intro faceId _hface
  exact finePacketGlobalNonzeroConnectedEntryChildCodeAt_toLocalCode
    S orientation observableFaceId faceId entry

theorem finePacketGlobalNonzeroConnectedEntryChildCode_activity_total
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    listNatWeight FinePacketComponentChildCode.activity
        (finePacketGlobalNonzeroConnectedEntryChildCode
          S orientation observableFaceId entry) =
      finePacketGlobalNonzeroConnectedEntryComponentActivity
        S orientation observableFaceId entry := by
  rw [← finePacketGlobalNonzeroConnectedEntryLocalCode_activity_total
    S orientation observableFaceId entry]
  rw [← finePacketGlobalNonzeroConnectedEntryChildCode_toLocalCode
    S orientation observableFaceId entry]
  rw [listNatWeight_map]
  rfl

theorem finePacketGlobalNonzeroConnectedEntryChildCode_excess_total
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    listNatWeight
        (fun code : FinePacketComponentChildCode => code.activity - 1)
        (finePacketGlobalNonzeroConnectedEntryChildCode
          S orientation observableFaceId entry) =
      finePacketGlobalNonzeroConnectedEntryComponentActivity
          S orientation observableFaceId entry -
        finePacketGlobalNonzeroConnectedEntryComponentSize
          S orientation observableFaceId entry := by
  rw [← finePacketGlobalNonzeroConnectedEntryLocalCode_excess_total
    S hfineCutoff orientation observableFaceId hobservableFace entry]
  rw [← finePacketGlobalNonzeroConnectedEntryChildCode_toLocalCode
    S orientation observableFaceId entry]
  rw [listNatWeight_map]
  rfl

theorem finePacketGlobalNonzeroConnectedEntryChildCode_scaledExcess_eq_heat
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    3 * listNatWeight
        (fun code : FinePacketComponentChildCode => code.activity - 1)
        (finePacketGlobalNonzeroConnectedEntryChildCode
          S orientation observableFaceId entry) =
      finePacketGlobalNonzeroConnectedEntryLocalActivityExcessHeat
        S orientation observableFaceId entry := by
  rw [finePacketGlobalNonzeroConnectedEntryChildCode_excess_total
    S hfineCutoff orientation observableFaceId hobservableFace entry]
  rfl

/-! ## 4. Axiom audit -/

#print axioms FinePacketComponentChildCode
#print axioms FinePacketComponentChildCode.Admissible
#print axioms finePacketComponentChildCodes
#print axioms finePacketComponentChildCodes_length
#print axioms finePacketComponentMinimalChildCodes_length
#print axioms finePacketComponentChildActivityHistogram_exact
#print axioms finePacketGlobalNonzeroConnectedEntryChildCodeAt
#print axioms finePacketGlobalNonzeroConnectedEntryChildCodeAt_mem
#print axioms finePacketGlobalNonzeroConnectedEntryChildCode
#print axioms finePacketGlobalNonzeroConnectedEntryChildCode_mem_catalogue
#print axioms finePacketGlobalNonzeroConnectedEntryChildCode_activity_total
#print axioms finePacketGlobalNonzeroConnectedEntryChildCode_excess_total
#print axioms finePacketGlobalNonzeroConnectedEntryChildCode_scaledExcess_eq_heat

end YMGap.Continuum.Z4DyadicBinaryConnectedComponentChildCode
