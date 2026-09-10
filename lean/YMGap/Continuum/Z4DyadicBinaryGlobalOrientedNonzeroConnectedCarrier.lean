/-
# Delete zero orientations from the global connected carrier

The connected target carrier is shared by the forward and reverse envelope
orientations.  A target pair can therefore belong to the carrier while its
raw weight in one chosen orientation is zero.  Such entries must not be sent
to the lowering/component compiler merely because a looser upper carrier is
nonnegative there.

This module strengthens the global comparison by assigning zero refined
weight to a zero raw orientation.  It then constructively deletes precisely
those entries and attaches a proof of nonzero oriented raw weight to every
survivor.  Each survivor computes its load-bearing lowering-pair witness.

Constructive contract: decidable rational equality, structural list
recursion, and existing finite-carrier witnesses only; no classical choice,
proof hole, trusted external computation, noncomputable declaration,
enlarged heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryGlobalConnectedDependentCarrier

namespace YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedDependentCarrier
open YMGap.Continuum.Z4DyadicBinaryJointGibbsHeatExponentFactorization
open YMGap.Continuum.Z4DyadicBinaryNormalizedConnectedGroundFractionSum
open YMGap.Continuum.Z4DyadicBinaryNormalizedConnectedUnitCongestionSum
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedEnvelopeNormalization
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsRelativeExcitationEndpoints

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_mono_local {A : Type}
    (lower upper : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → lower item ≤ upper item) →
      listQSum lower items ≤ listQSum upper items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle => by
      simp only [listQSum]
      exact Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun item hitem =>
            hle item (List.mem_cons_of_mem head hitem)))

/-! ## 1. The raw-orientation test and its zero-aware upper weight -/

def finePacketGlobalConnectedEntryOrientedRawWeight
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (entry : FinePacketGlobalConnectedEntry S observableFaceId) : Q' :=
  finePacketOrientedLocalizedRawPairWeight
    S orientation entry.sources.1.1 entry.sources.2.1 entry.targets

/-- The refined upper weight is retained exactly on a nonzero oriented row
and is replaced by zero on an orientation-incompatible target pair. -/
def finePacketGlobalConnectedEntryActiveRefinedWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalConnectedEntry S observableFaceId) : Q' :=
  if finePacketGlobalConnectedEntryOrientedRawWeight
      S orientation observableFaceId entry ≈ 0 then
    0
  else
    finePacketGlobalConnectedEntryRefinedWeight
      S hfineCutoff hcoarseCoupling rate orientation observableFaceId
        hobservableFace entry

/-! ## 2. The proof-carrying nonzero subcarrier -/

abbrev FinePacketGlobalOrientedNonzeroConnectedEntry
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat) :=
  {entry : FinePacketGlobalConnectedEntry S observableFaceId //
    ¬ finePacketGlobalConnectedEntryOrientedRawWeight
      S orientation observableFaceId entry ≈ 0}

private def orientedNonzeroEntriesAux
    {A : Type} (raw : A → Q') :
    List A → List {item : A // ¬ raw item ≈ 0}
  | [] => []
  | head :: tail =>
      if hzero : raw head ≈ 0 then
        orientedNonzeroEntriesAux raw tail
      else
        ⟨head, hzero⟩ :: orientedNonzeroEntriesAux raw tail

private theorem listQSum_zeroAware_eq_nonzeroAux
    {A : Type} (raw refined : A → Q') : ∀ items : List A,
    listQSum
        (fun item => if raw item ≈ 0 then 0 else refined item)
        items ≈
      listQSum (fun item : {item : A // ¬ raw item ≈ 0} =>
        refined item.1) (orientedNonzeroEntriesAux raw items)
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      by_cases hzero : raw head ≈ 0
      · simp only [listQSum, hzero, if_true, orientedNonzeroEntriesAux]
        exact Q'.eqv_trans _ _ _
          (Q'.eqv_of_eq (Q'.zero_add' _))
          (listQSum_zeroAware_eq_nonzeroAux raw refined tail)
      · simp only [listQSum, hzero, if_false, orientedNonzeroEntriesAux]
        exact Q'.add_eqv_congr'
          (Q'.eqv_refl _)
          (listQSum_zeroAware_eq_nonzeroAux raw refined tail)

def finePacketGlobalOrientedNonzeroConnectedEntries
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat) :
    List (FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :=
  orientedNonzeroEntriesAux
    (finePacketGlobalConnectedEntryOrientedRawWeight
      S orientation observableFaceId)
    (finePacketGlobalConnectedEntries S observableFaceId)

def finePacketGlobalOrientedNonzeroConnectedEntryRefinedWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) : Q' :=
  finePacketGlobalConnectedEntryRefinedWeight
      S hfineCutoff hcoarseCoupling rate orientation observableFaceId
      hobservableFace entry.1

/-- Every retained entry has the two literal lowering rows required by the
component heat budget. -/
def finePacketGlobalOrientedNonzeroConnectedEntryLowering
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    finePacketOrientedLoweringPair
      S orientation entry.1.sources.1.1 entry.1.sources.2.1
        entry.1.targets := by
  have hactive := (List.mem_filter.mp entry.1.target_mem).1
  have hphysical := (List.mem_filter.mp hactive).1
  cases orientation with
  | forward =>
      exact finePacketForwardLocalizedRawPairWeight_ne_zero_implies_lowering
        S hfineCutoff entry.1.sources.1 entry.1.sources.2
          entry.1.targets hphysical entry.2
  | reverse =>
      exact finePacketReverseLocalizedRawPairWeight_ne_zero_implies_lowering
        S hfineCutoff entry.1.sources.1 entry.1.sources.2
          entry.1.targets hphysical entry.2

/-! ## 3. Strengthened pointwise and global comparison -/

theorem finePacketGlobalConnectedEntryNormalizedWeight_le_activeRefined
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hfineRate : S.fine.coupling ≤ rate)
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalConnectedEntry S observableFaceId) :
    finePacketGlobalConnectedEntryNormalizedWeight
        S hfineCutoff hcoarseCoupling orientation observableFaceId entry ≤
      finePacketGlobalConnectedEntryActiveRefinedWeight
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace entry := by
  by_cases hzero : finePacketGlobalConnectedEntryOrientedRawWeight
      S orientation observableFaceId entry ≈ 0
  · unfold finePacketGlobalConnectedEntryNormalizedWeight
      finePacketGlobalConnectedEntryActiveRefinedWeight
      finePacketGlobalConnectedEntryOrientedRawWeight at *
    rw [if_pos hzero]
    exact Q'.le_of_eqv
      (finePacketOrientedNormalizedJointPairWeight_eqv_zero_of_raw_zero
        S hfineCutoff hcoarseCoupling orientation
          entry.sources.1 entry.sources.2 entry.targets hzero)
  · let nonzero : FinePacketGlobalOrientedNonzeroConnectedEntry
        S orientation observableFaceId := ⟨entry, hzero⟩
    have hlowering :=
      finePacketGlobalOrientedNonzeroConnectedEntryLowering
        S hfineCutoff orientation observableFaceId nonzero
    unfold finePacketGlobalConnectedEntryActiveRefinedWeight
    rw [if_neg hzero]
    unfold finePacketGlobalConnectedEntryNormalizedWeight
      finePacketGlobalConnectedEntryRefinedWeight
    exact
      finePacketOrientedNormalizedJointPairWeight_le_distanceResidualGroundCongestion
        S hfineCutoff hcoarseCoupling rate hfineRate hcoarseRate
          orientation entry.sources.1 entry.sources.2 observableFaceId
            hobservableFace entry.targets hlowering
            (finePacketGlobalConnectedEntryPath
              S observableFaceId hobservableFace entry)

theorem finePacketGlobalConnectedEntryNormalizedSum_le_activeRefinedSum
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hfineRate : S.fine.coupling ≤ rate)
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    listQSum
        (finePacketGlobalConnectedEntryNormalizedWeight
          S hfineCutoff hcoarseCoupling orientation observableFaceId)
        (finePacketGlobalConnectedEntries S observableFaceId) ≤
      listQSum
        (finePacketGlobalConnectedEntryActiveRefinedWeight
          S hfineCutoff hcoarseCoupling rate orientation observableFaceId
            hobservableFace)
        (finePacketGlobalConnectedEntries S observableFaceId) := by
  apply listQSum_mono_local
  intro entry _hentry
  exact finePacketGlobalConnectedEntryNormalizedWeight_le_activeRefined
    S hfineCutoff hcoarseCoupling rate hfineRate hcoarseRate orientation
      observableFaceId hobservableFace entry

/-- Deleting zero orientations changes no active refined mass. -/
theorem finePacketGlobalConnectedEntryActiveRefinedSum_eqv_nonzeroSum
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    listQSum
        (finePacketGlobalConnectedEntryActiveRefinedWeight
          S hfineCutoff hcoarseCoupling rate orientation observableFaceId
            hobservableFace)
        (finePacketGlobalConnectedEntries S observableFaceId) ≈
      listQSum
        (finePacketGlobalOrientedNonzeroConnectedEntryRefinedWeight
          S hfineCutoff hcoarseCoupling rate orientation observableFaceId
            hobservableFace)
        (finePacketGlobalOrientedNonzeroConnectedEntries
          S orientation observableFaceId) := by
  unfold finePacketGlobalConnectedEntryActiveRefinedWeight
    finePacketGlobalOrientedNonzeroConnectedEntryRefinedWeight
    finePacketGlobalOrientedNonzeroConnectedEntries
  exact listQSum_zeroAware_eq_nonzeroAux
    (finePacketGlobalConnectedEntryOrientedRawWeight
      S orientation observableFaceId)
    (finePacketGlobalConnectedEntryRefinedWeight
      S hfineCutoff hcoarseCoupling rate orientation observableFaceId
        hobservableFace)
    (finePacketGlobalConnectedEntries S observableFaceId)

/-- Final nonzero-carrier form of the strengthened global comparison. -/
theorem finePacketGlobalConnectedEntryNormalizedSum_le_nonzeroRefinedSum
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hfineRate : S.fine.coupling ≤ rate)
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    listQSum
        (finePacketGlobalConnectedEntryNormalizedWeight
          S hfineCutoff hcoarseCoupling orientation observableFaceId)
        (finePacketGlobalConnectedEntries S observableFaceId) ≤
      listQSum
        (finePacketGlobalOrientedNonzeroConnectedEntryRefinedWeight
          S hfineCutoff hcoarseCoupling rate orientation observableFaceId
            hobservableFace)
        (finePacketGlobalOrientedNonzeroConnectedEntries
          S orientation observableFaceId) := by
  exact Q'.le_trans' _ _ _
    (finePacketGlobalConnectedEntryNormalizedSum_le_activeRefinedSum
      S hfineCutoff hcoarseCoupling rate hfineRate hcoarseRate orientation
        observableFaceId hobservableFace)
    (Q'.le_of_eqv
      (finePacketGlobalConnectedEntryActiveRefinedSum_eqv_nonzeroSum
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace))

/-! ## 4. Axiom audit -/

#print axioms finePacketGlobalConnectedEntryOrientedRawWeight
#print axioms finePacketGlobalConnectedEntryActiveRefinedWeight
#print axioms FinePacketGlobalOrientedNonzeroConnectedEntry
#print axioms finePacketGlobalOrientedNonzeroConnectedEntries
#print axioms finePacketGlobalOrientedNonzeroConnectedEntryRefinedWeight
#print axioms finePacketGlobalOrientedNonzeroConnectedEntryLowering
#print axioms finePacketGlobalConnectedEntryNormalizedWeight_le_activeRefined
#print axioms finePacketGlobalConnectedEntryNormalizedSum_le_activeRefinedSum
#print axioms finePacketGlobalConnectedEntryActiveRefinedSum_eqv_nonzeroSum
#print axioms finePacketGlobalConnectedEntryNormalizedSum_le_nonzeroRefinedSum

end YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
