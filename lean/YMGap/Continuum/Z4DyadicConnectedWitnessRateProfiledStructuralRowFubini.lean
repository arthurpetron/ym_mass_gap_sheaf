/-
# Fubini from structural terminal codes to lowering-row cells

Every realized structural code has a literal expanded-witness preimage,
because the structural carrier is obtained by mapping the faithful terminal
compiler and deleting duplicates.  We select the first such preimage by
finite list recursion.  This is constructive finite search, not choice.

The structural-fiber row bound can then be applied once to every distinct
structural code.  Exact structural Fubini yields a bound on the complete
terminal-code mass by a sum of explicit lowering-row cells, with no duplicate
structural representatives and no volume-blind cardinality constant.

Constructive contract: finite search, proof-irrelevant carrier membership,
and exact rational finite sums only; no classical choice, proof hole, trusted
external computation, computability escape, heartbeat increase, or new
trusted principle.
-/

import YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralFiberRow

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralRowFubini

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalCompiler
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralFiberRow
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralLoweringCarrier
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalCodeMass

private def firstOption {A : Type} : List A → Option A
  | [] => none
  | head :: _tail => some head

private theorem firstOption_exists_of_mem {A : Type}
    {item : A} {items : List A} (hitem : item ∈ items) :
    ∃ first, firstOption items = some first ∧ first ∈ items := by
  cases items with
  | nil => exact False.elim (List.not_mem_nil hitem)
  | cons head tail => exact ⟨head, rfl, List.mem_cons_self⟩

private theorem listQSum_le_termwise_local {A : Type}
    (left right : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → left item ≤ right item) →
      listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem => hle item (List.mem_cons_of_mem head hitem)))

/-! ## 1. A canonical literal representative of every realized structure -/

/-- Expanded witnesses whose faithful terminal code has the prescribed
structural projection. -/
def finePacketGlobalNonzeroConnectedExpandedWitnessesAtStructuralCode
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (structural : FinePacketConnectedRateProfiledStructuralCode) :
    List (FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :=
  (finePacketGlobalNonzeroConnectedExpandedWitnessEntries
      S orientation observableFaceId).filter
    (fun expanded => decide
      (structural =
        finePacketConnectedRateProfiledStructuralCompiler
          (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
            S rate hrate0 orientation observableFaceId hobservableFace
              expanded)))

/-- The first literal expanded witness realizing a structural code, when one
exists. -/
def finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (structural : FinePacketConnectedRateProfiledStructuralCode) :
    Option (FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :=
  firstOption
    (finePacketGlobalNonzeroConnectedExpandedWitnessesAtStructuralCode
      S rate hrate0 orientation observableFaceId hobservableFace structural)

/-- Membership in the realized structural carrier supplies a concrete first
expanded-witness representative and its exact structural equality. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?_exists_of_mem
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (structural : FinePacketConnectedRateProfiledStructuralCode)
    (hstructural : structural ∈
      finePacketConnectedRateProfiledStructuralCodes
        S rate hrate0 orientation observableFaceId hobservableFace) :
    ∃ reference,
      finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?
          S rate hrate0 orientation observableFaceId hobservableFace
            structural = some reference ∧
        reference ∈
          finePacketGlobalNonzeroConnectedExpandedWitnessEntries
            S orientation observableFaceId ∧
        structural =
          finePacketConnectedRateProfiledStructuralCompiler
            (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
              S rate hrate0 orientation observableFaceId hobservableFace
                reference) := by
  unfold finePacketConnectedRateProfiledStructuralCodes at hstructural
  have hmapped := List.mem_eraseDups.mp hstructural
  obtain ⟨code, hcode, hcodeStructural⟩ := List.mem_map.mp hmapped
  unfold finePacketConnectedRateProfiledNormalizedTerminalCodes at hcode
  obtain ⟨expanded, hexpanded, hcompiled⟩ := List.mem_map.mp hcode
  have hstructuralExpanded :
      structural =
        finePacketConnectedRateProfiledStructuralCompiler
          (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledNormalizedTerminalCompiler
            S rate hrate0 orientation observableFaceId hobservableFace
              expanded) :=
    hcodeStructural.symm.trans
      (congrArg finePacketConnectedRateProfiledStructuralCompiler
        hcompiled).symm
  have hexpandedMatch : expanded ∈
      finePacketGlobalNonzeroConnectedExpandedWitnessesAtStructuralCode
        S rate hrate0 orientation observableFaceId hobservableFace
          structural := by
    unfold
      finePacketGlobalNonzeroConnectedExpandedWitnessesAtStructuralCode
    exact List.mem_filter.mpr
      ⟨hexpanded, decide_eq_true hstructuralExpanded⟩
  obtain ⟨reference, hfirst, hreferenceMatch⟩ :=
    firstOption_exists_of_mem hexpandedMatch
  have hparts := List.mem_filter.mp hreferenceMatch
  refine ⟨reference, ?_, hparts.1, of_decide_eq_true hparts.2⟩
  unfold
    finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?
  exact hfirst

/-! ## 2. One row-cell envelope per distinct structural code -/

/-- The exact lowering-row mass of the canonical representative.  Unrealized
codes receive zero, making this a total function on structural codes while
retaining a literal representative on the realized carrier. -/
def finePacketConnectedRateProfiledStructuralLoweringRowEnvelope
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (structural : FinePacketConnectedRateProfiledStructuralCode) : Q' :=
  match
    finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?
      S rate hrate0 orientation observableFaceId hobservableFace structural
  with
  | none => 0
  | some reference =>
      listQSum
        (finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowWeight
          S hfineCutoff hcoarseCoupling rate hrate0 orientation
            observableFaceId hobservableFace reference)
        (finePacketGlobalNonzeroConnectedExpandedWitnessLoweringCodeCarrier
          S orientation observableFaceId reference)

/-- Each distinct structural fiber is bounded by its canonical literal row
cell. -/
theorem finePacketConnectedRateProfiledStructuralFiberWeight_le_rowEnvelope
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
    fiberWeight
        (finePacketConnectedRateProfiledNormalizedTerminalCodes
          S rate hrate0 orientation observableFaceId hobservableFace)
        (finePacketConnectedRateProfiledTerminalCodeWeight
          S hfineCutoff hcoarseCoupling rate hrate0)
        finePacketConnectedRateProfiledStructuralCompiler structural ≤
      finePacketConnectedRateProfiledStructuralLoweringRowEnvelope
        S hfineCutoff hcoarseCoupling rate hrate0 orientation
          observableFaceId hobservableFace structural := by
  obtain ⟨reference, hreference, _hreferenceMem, hreferenceStructural⟩ :=
    finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?_exists_of_mem
      S rate hrate0 orientation observableFaceId hobservableFace structural
        hstructural
  unfold finePacketConnectedRateProfiledStructuralLoweringRowEnvelope
  rw [hreference]
  have hrow :=
    finePacketGlobalNonzeroConnectedExpandedWitnessStructuralFiberWeight_le_loweringRow
      S hfineCutoff hcoarseCoupling rate hrate0 orientation
        observableFaceId hobservableFace reference
  unfold finePacketGlobalNonzeroConnectedExpandedWitnessStructuralCode at hrow
  rw [← hreferenceStructural] at hrow
  exact hrow

/-! ## 3. Contract the exact structural Fubini decomposition -/

/-- The complete profile-weighted terminal-code mass is bounded by one exact
lowering-row cell for each distinct realized structural code. -/
theorem finePacketConnectedRateProfiledTerminalCodeMass_le_structuralLoweringRowEnvelopeMass
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
        (finePacketConnectedRateProfiledStructuralLoweringRowEnvelope
          S hfineCutoff hcoarseCoupling rate hrate0 orientation
            observableFaceId hobservableFace)
        (finePacketConnectedRateProfiledStructuralCodes
          S rate hrate0 orientation observableFaceId hobservableFace) := by
  have hfubini := finePacketConnectedRateProfiledStructuralFiber_total
    S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
      hobservableFace
  refine Q'.le_trans' _
    (listQSum
      (fiberWeight
        (finePacketConnectedRateProfiledNormalizedTerminalCodes
          S rate hrate0 orientation observableFaceId hobservableFace)
        (finePacketConnectedRateProfiledTerminalCodeWeight
          S hfineCutoff hcoarseCoupling rate hrate0)
        finePacketConnectedRateProfiledStructuralCompiler)
      (finePacketConnectedRateProfiledStructuralCodes
        S rate hrate0 orientation observableFaceId hobservableFace)) _ ?_ ?_
  · exact Q'.le_of_eqv (Q'.eqv_symm hfubini)
  · apply listQSum_le_termwise_local
    intro structural hstructural
    exact
      finePacketConnectedRateProfiledStructuralFiberWeight_le_rowEnvelope
        S hfineCutoff hcoarseCoupling rate hrate0 orientation
          observableFaceId hobservableFace structural hstructural

#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessesAtStructuralCode
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?_exists_of_mem
#print axioms finePacketConnectedRateProfiledStructuralLoweringRowEnvelope
#print axioms finePacketConnectedRateProfiledStructuralFiberWeight_le_rowEnvelope
#print axioms finePacketConnectedRateProfiledTerminalCodeMass_le_structuralLoweringRowEnvelopeMass

end YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralRowFubini
