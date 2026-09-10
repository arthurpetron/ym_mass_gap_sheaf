/-
# Fubini from structural codes to terminal-skeleton rows

The preceding structural Fubini theorem leaves one lowering-row cell for
every distinct full structural code.  The adaptive words inside the fine and
coarse peeling traces are the remaining presentation multiplicity.  This
module groups structural codes by exactly the data held fixed by the
accepted-pair profile inverse-fiber theorem:

* the physical source and target rows;
* the fine and coarse terminal accepted-state keys;
* the fine and coarse peel skeletons and exterior/core counters; and
* the exact lowering-row weight.

The target row is read from the first literal expanded-witness representative
already constructed for each realized structural code.  Hence this is finite
search, not choice.  Exact finite Fubini then reassembles the structural row
sum as fibers over a duplicate-free list of terminal-skeleton row codes.

Constructive contract: finite search, finite maps and filters, and exact
rational finite sums only; no classical choice, proof hole, trusted external
computation, computability escape, heartbeat increase, or new trusted
principle.
-/

import YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralRowFubini

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFubini

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingTraceCarrier
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralRowFubini
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalCodeMass

local infix:50 " ≈ " => Q'.eqv

private theorem filteredEraseDupsNodupLocal {A : Type}
    [BEq A] [LawfulBEq A] (items : List A) :
    ∀ predicate : A → Bool, (items.filter predicate).eraseDups.Nodup := by
  induction items with
  | nil =>
      intro _
      exact List.nodup_nil
  | cons head tail ih =>
      intro predicate
      rw [List.filter_cons]
      split
      · rw [List.eraseDups_cons, List.filter_filter]
        refine List.nodup_cons.mpr ⟨?_, ih _⟩
        intro hmem
        have hfiltered := List.mem_eraseDups.mp hmem
        have hfalse := (List.mem_filter.mp hfiltered).2
        have hself : (head == head) = true := BEq.rfl
        rw [hself] at hfalse
        contradiction
      · exact ih _

private theorem filterTrueLocal {A : Type} : ∀ items : List A,
    items.filter (fun _ => true) = items
  | [] => rfl
  | head :: tail => congrArg (List.cons head) (filterTrueLocal tail)

private theorem eraseDupsNodupLocal {A : Type}
    [BEq A] [LawfulBEq A] (items : List A) : items.eraseDups.Nodup := by
  have h := filteredEraseDupsNodupLocal items (fun _ => true)
  rw [filterTrueLocal] at h
  exact h

/-! ## 1. The terminal-skeleton row code -/

/-- The coarsest row data currently justified by an exact inverse-fiber
theorem.  In particular, the full adaptive peel records are replaced by their
skeletons, but the two terminal accepted states and both counter pairs remain
visible. -/
structure FinePacketConnectedRateProfiledTerminalSkeletonRowCode : Type where
  leftSource : List Nat
  rightSource : List Nat
  leftTarget : List Nat
  rightTarget : List Nat
  fineTerminal : SlabExpandedFineTargetKey × SlabExpandedFineTargetKey
  fineSkeletons : List SlabAcceptedPairedPeelSkeleton
  fineExterior : Nat
  fineCore : Nat
  coarseTerminal : SlabExpandedFineTargetKey × SlabExpandedFineTargetKey
  coarseSkeletons : List SlabAcceptedPairedPeelSkeleton
  coarseExterior : Nat
  coarseCore : Nat
  weight : Q'
deriving DecidableEq

/-- The physical target words of the first expanded witness realizing a
structural code.  Unrealized codes receive empty words; every structural code
in the carrier below is realized. -/
def finePacketConnectedRateProfiledStructuralTargetWords
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (structural : FinePacketConnectedRateProfiledStructuralCode) :
    List Nat × List Nat :=
  match
    finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?
      S rate hrate0 orientation observableFaceId hobservableFace structural
  with
  | none => ([], [])
  | some reference =>
      (finiteEdgeLabellingWord S.coarse.faceEdges reference.1.1.targets.1,
        finiteEdgeLabellingWord S.coarse.faceEdges reference.1.1.targets.2)

/-- Forget the adaptive peel words and structural presentation while
retaining the exact coordinates needed for the next weighted fiber bound. -/
def finePacketConnectedRateProfiledTerminalSkeletonRowCompiler
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (structural : FinePacketConnectedRateProfiledStructuralCode) :
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode where
  leftSource := structural.leftSource
  rightSource := structural.rightSource
  leftTarget :=
    (finePacketConnectedRateProfiledStructuralTargetWords
      S rate hrate0 orientation observableFaceId hobservableFace structural).1
  rightTarget :=
    (finePacketConnectedRateProfiledStructuralTargetWords
      S rate hrate0 orientation observableFaceId hobservableFace structural).2
  fineTerminal := structural.fineProfile.1
  fineSkeletons := structural.fineProfile.2.1.map
    SlabAcceptedPairedPeelRecord.skeleton
  fineExterior := structural.fineProfile.2.2.1
  fineCore := structural.fineProfile.2.2.2
  coarseTerminal := structural.coarseProfile.1
  coarseSkeletons := structural.coarseProfile.2.1.map
    SlabAcceptedPairedPeelRecord.skeleton
  coarseExterior := structural.coarseProfile.2.2.1
  coarseCore := structural.coarseProfile.2.2.2
  weight :=
    finePacketConnectedRateProfiledStructuralLoweringRowEnvelope
      S hfineCutoff hcoarseCoupling rate hrate0 orientation
        observableFaceId hobservableFace structural

/-- One occurrence of every realized terminal-skeleton row. -/
def finePacketConnectedRateProfiledTerminalSkeletonRowCodes
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    List FinePacketConnectedRateProfiledTerminalSkeletonRowCode :=
  ((finePacketConnectedRateProfiledStructuralCodes
      S rate hrate0 orientation observableFaceId hobservableFace).map
    (finePacketConnectedRateProfiledTerminalSkeletonRowCompiler
      S hfineCutoff hcoarseCoupling rate hrate0 orientation
        observableFaceId hobservableFace)).eraseDups

theorem finePacketConnectedRateProfiledTerminalSkeletonRowCodes_nodup
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    (finePacketConnectedRateProfiledTerminalSkeletonRowCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation
        observableFaceId hobservableFace).Nodup := by
  unfold finePacketConnectedRateProfiledTerminalSkeletonRowCodes
  exact eraseDupsNodupLocal _

theorem finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_mem
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (structural : FinePacketConnectedRateProfiledStructuralCode)
    (hstructural : structural ∈
      finePacketConnectedRateProfiledStructuralCodes
        S rate hrate0 orientation observableFaceId hobservableFace) :
    finePacketConnectedRateProfiledTerminalSkeletonRowCompiler
        S hfineCutoff hcoarseCoupling rate hrate0 orientation
          observableFaceId hobservableFace structural ∈
      finePacketConnectedRateProfiledTerminalSkeletonRowCodes
        S hfineCutoff hcoarseCoupling rate hrate0 orientation
          observableFaceId hobservableFace := by
  unfold finePacketConnectedRateProfiledTerminalSkeletonRowCodes
  apply List.mem_eraseDups.mpr
  exact List.mem_map.mpr ⟨structural, hstructural, rfl⟩

/-! ## 2. Exact row-weight factorization and Fubini -/

def finePacketConnectedRateProfiledTerminalSkeletonRowWeight
    (code : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) : Q' :=
  code.weight

/-- Exact Fubini over the duplicate-free terminal-skeleton row carrier. -/
theorem finePacketConnectedRateProfiledTerminalSkeletonRowFiber_total
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    listQSum
        (fiberWeight
          (finePacketConnectedRateProfiledStructuralCodes
            S rate hrate0 orientation observableFaceId hobservableFace)
          (finePacketConnectedRateProfiledStructuralLoweringRowEnvelope
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace)
          (finePacketConnectedRateProfiledTerminalSkeletonRowCompiler
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace))
        (finePacketConnectedRateProfiledTerminalSkeletonRowCodes
          S hfineCutoff hcoarseCoupling rate hrate0 orientation
            observableFaceId hobservableFace) ≈
      listQSum
        (finePacketConnectedRateProfiledStructuralLoweringRowEnvelope
          S hfineCutoff hcoarseCoupling rate hrate0 orientation
            observableFaceId hobservableFace)
        (finePacketConnectedRateProfiledStructuralCodes
          S rate hrate0 orientation observableFaceId hobservableFace) := by
  exact fiberWeight_total _ _ _ _
    (finePacketConnectedRateProfiledTerminalSkeletonRowCodes_nodup
      S hfineCutoff hcoarseCoupling rate hrate0 orientation
        observableFaceId hobservableFace)
    (finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_mem
      S hfineCutoff hcoarseCoupling rate hrate0 orientation
        observableFaceId hobservableFace)

/-- The complete terminal-code mass is now bounded by fibers over the exact
terminal/skeleton row coordinates required by the adaptive-profile theorem. -/
theorem finePacketConnectedRateProfiledTerminalCodeMass_le_terminalSkeletonRowFiberMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketConnectedRateProfiledTerminalCodeMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace ≤
      listQSum
        (fiberWeight
          (finePacketConnectedRateProfiledStructuralCodes
            S rate hrate0 orientation observableFaceId hobservableFace)
          (finePacketConnectedRateProfiledStructuralLoweringRowEnvelope
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace)
          (finePacketConnectedRateProfiledTerminalSkeletonRowCompiler
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace))
        (finePacketConnectedRateProfiledTerminalSkeletonRowCodes
          S hfineCutoff hcoarseCoupling rate hrate0 orientation
            observableFaceId hobservableFace) := by
  refine Q'.le_trans' _ _ _
    (finePacketConnectedRateProfiledTerminalCodeMass_le_structuralLoweringRowEnvelopeMass
      S hfineCutoff hcoarseCoupling rate hrate0 orientation
        observableFaceId hobservableFace) ?_
  exact Q'.le_of_eqv (Q'.eqv_symm
    (finePacketConnectedRateProfiledTerminalSkeletonRowFiber_total
      S hfineCutoff hcoarseCoupling rate hrate0 orientation
        observableFaceId hobservableFace))

#print axioms FinePacketConnectedRateProfiledTerminalSkeletonRowCode
#print axioms finePacketConnectedRateProfiledStructuralTargetWords
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowCompiler
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowCodes
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowCodes_nodup
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_mem
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowWeight
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowFiber_total
#print axioms finePacketConnectedRateProfiledTerminalCodeMass_le_terminalSkeletonRowFiberMass

end YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFubini
