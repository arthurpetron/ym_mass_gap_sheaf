/-
# Sum the strict terminal-skeleton row contractions

Every realized terminal/skeleton row has a finite, nonempty structural fiber.
Finite first-element search selects one structural representative and then the
already-constructed first literal expanded witness above it.  This makes the
normalized lowering-row residual a total function of the row, without choice.

Termwise application of the adaptive-anchor theorem gives a single finite-sum
bound from the complete profiled terminal mass to rows weighted by the strict
factor `(8/25)^profileMass`.  The residual remains explicit for the next exact
normalization and spatial-tail contraction.

Constructive contract: finite list recursion and exact rational inequalities
only; no classical choice, proof hole, trusted external computation,
computability escape, heartbeat increase, or new trusted principle.
-/

import YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowAdaptiveAnchor

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowContraction

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalCompiler
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralRowFubini
open YMGap.Continuum.Z4DyadicConnectedWitnessRateSpatialTerminalResidual
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalCodeMass
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowAdaptiveAnchor
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFubini

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

/-! ## 1. Constructive representatives of realized rows -/

/-- The first structural code in the exact inverse fiber of a row. -/
def finePacketConnectedRateProfiledTerminalSkeletonRowFirstStructural?
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) :
    Option FinePacketConnectedRateProfiledStructuralCode :=
  firstOption
    (finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row)

theorem finePacketConnectedRateProfiledTerminalSkeletonRowFirstStructural?_exists_of_mem
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode)
    (hrow : row ∈ finePacketConnectedRateProfiledTerminalSkeletonRowCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace) :
    ∃ structural,
      finePacketConnectedRateProfiledTerminalSkeletonRowFirstStructural?
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace row = some structural ∧
        structural ∈
          finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace row := by
  unfold finePacketConnectedRateProfiledTerminalSkeletonRowCodes at hrow
  have hmapped := List.mem_eraseDups.mp hrow
  obtain ⟨structural, hstructural, hcompiler⟩ := List.mem_map.mp hmapped
  have hfiber : structural ∈
      finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace row := by
    unfold finePacketConnectedRateProfiledStructuralCodesAtTerminalSkeletonRow
    exact List.mem_filter.mpr
      ⟨hstructural, decide_eq_true hcompiler.symm⟩
  unfold finePacketConnectedRateProfiledTerminalSkeletonRowFirstStructural?
  exact firstOption_exists_of_mem hfiber

/-! ## 2. The selected normalized row residual -/

/-- Total selected residual: unrealized rows receive zero, while every row in
the row carrier uses its first structural code and first literal expanded
witness. -/
def finePacketConnectedRateProfiledTerminalSkeletonRowResidual
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) : Q' :=
  match
    finePacketConnectedRateProfiledTerminalSkeletonRowFirstStructural?
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row
  with
  | none => 0
  | some structural =>
      match
        finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?
          S rate hrate0 orientation observableFaceId hobservableFace structural
      with
      | none => 0
      | some reference =>
          finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowResidual
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace reference

theorem finePacketConnectedRateProfiledTerminalSkeletonRowResidual_eq_of_selected
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode)
    (structural : FinePacketConnectedRateProfiledStructuralCode)
    (hstructural :
      finePacketConnectedRateProfiledTerminalSkeletonRowFirstStructural?
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace row = some structural)
    (reference : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId)
    (hreference :
      finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?
        S rate hrate0 orientation observableFaceId hobservableFace structural =
          some reference) :
    finePacketConnectedRateProfiledTerminalSkeletonRowResidual
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace row =
      finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowResidual
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace reference := by
  unfold finePacketConnectedRateProfiledTerminalSkeletonRowResidual
  simp only [hstructural, hreference]

theorem finePacketConnectedRateProfiledTerminalSkeletonRowResidual_nonnegative
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) :
    (0 : Q') ≤
      finePacketConnectedRateProfiledTerminalSkeletonRowResidual
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace row := by
  unfold finePacketConnectedRateProfiledTerminalSkeletonRowResidual
  split
  · exact Q'.le_refl' 0
  · rename_i structural hstructural
    split
    · exact Q'.le_refl' 0
    · rename_i reference hreference
      unfold
        finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowResidual
      apply listQSum_nonnegative_on
      intro lowering _hlowering
      unfold
        finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowResidualWeight
      have hresidual :=
        finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalResidual_nonnegative
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace reference
      exact Q'.le_trans' _ _ _ hresidual
        (Q'.ge_of_eqv
          (finePacketConnectedFourEntryRateProfiledCompilerCodeNormalizedTerminalResidual_compiler
            S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
              hobservableFace reference))

/-! ## 3. Per-row and total strict contraction -/

/-- The selected representative makes the strict row theorem unconditional
on every member of the realized row carrier. -/
theorem finePacketConnectedRateProfiledTerminalSkeletonRowFiberWeight_le_contracted
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode)
    (hrow : row ∈ finePacketConnectedRateProfiledTerminalSkeletonRowCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace) :
    fiberWeight
        (finePacketConnectedRateProfiledStructuralCodes
          S rate hrate0 orientation observableFaceId hobservableFace)
        (finePacketConnectedRateProfiledStructuralLoweringRowEnvelope
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace)
        (finePacketConnectedRateProfiledTerminalSkeletonRowCompiler
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace)
        row ≤
      (Q'.mkPos 8 25 (by decide)) ^
          ((row.fineExterior + row.fineCore) +
            (row.coarseExterior + row.coarseCore)) *
        finePacketConnectedRateProfiledTerminalSkeletonRowResidual
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace row := by
  obtain ⟨structural, hfirst, hstructural⟩ :=
    finePacketConnectedRateProfiledTerminalSkeletonRowFirstStructural?_exists_of_mem
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row hrow
  have hstructuralCarrier :=
    finePacketConnectedRateProfiledStructuralCode_mem_of_mem_row
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row structural hstructural
  obtain ⟨reference, hreference, _hreferenceMem, hreferenceStructural⟩ :=
    finePacketGlobalNonzeroConnectedExpandedWitnessAtStructuralCode?_exists_of_mem
      S rate hrate0 orientation observableFaceId hobservableFace structural
        hstructuralCarrier
  have hbound :=
    finePacketConnectedRateProfiledTerminalSkeletonRowFiberWeight_le_eightTwentyFifths_mul_residual
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row hrow structural hstructural reference hreference
          hreferenceStructural
  rw [finePacketConnectedRateProfiledTerminalSkeletonRowResidual_eq_of_selected
    S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
      hobservableFace row structural hfirst reference hreference]
  exact hbound

/-- The finite contracted row mass with the strict `8/25` profile factor
still attached to each selected normalized residual. -/
def finePacketConnectedRateProfiledTerminalSkeletonContractedMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) : Q' :=
  listQSum
    (fun row =>
      (Q'.mkPos 8 25 (by decide)) ^
          ((row.fineExterior + row.fineCore) +
            (row.coarseExterior + row.coarseCore)) *
        finePacketConnectedRateProfiledTerminalSkeletonRowResidual
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace row)
    (finePacketConnectedRateProfiledTerminalSkeletonRowCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)

/-- Complete finite contraction from the profiled terminal-code mass to the
strictly weighted selected residual rows. -/
theorem finePacketConnectedRateProfiledTerminalCodeMass_le_terminalSkeletonContractedMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketConnectedRateProfiledTerminalCodeMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace ≤
      finePacketConnectedRateProfiledTerminalSkeletonContractedMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace := by
  refine Q'.le_trans' _ _ _
    (finePacketConnectedRateProfiledTerminalCodeMass_le_terminalSkeletonRowFiberMass
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace) ?_
  unfold finePacketConnectedRateProfiledTerminalSkeletonContractedMass
  apply listQSum_le_termwise_local
  intro row hrow
  exact
    finePacketConnectedRateProfiledTerminalSkeletonRowFiberWeight_le_contracted
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row hrow

#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowFirstStructural?
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowFirstStructural?_exists_of_mem
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowResidual
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowResidual_eq_of_selected
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowResidual_nonnegative
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowFiberWeight_le_contracted
#print axioms finePacketConnectedRateProfiledTerminalSkeletonContractedMass
#print axioms finePacketConnectedRateProfiledTerminalCodeMass_le_terminalSkeletonContractedMass

end YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowContraction
