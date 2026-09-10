/-
# Extract spatial distance from the strict terminal-skeleton row contraction

The complete terminal-code mass is already bounded by terminal/skeleton rows
carrying `(8/25)^profileMass`.  Every realized row has a constructively chosen
expanded-witness representative.  The four-counter profile mass of that
representative is exactly the four-counter mass stored in the row, and the
connected-component geometry proves that this mass dominates the
observable-to-source distance.

Since `8/25` lies in `[0,1]`, power antitonicity therefore replaces the row
profile exponent by the selected physical distance.  The normalized
lowering-row residual remains explicit; its exact Gibbs normalization is the
next frontier.

Constructive contract: finite first-element search, exact compiler projection,
and rational power antitonicity only; no classical choice, proof hole, trusted
external computation, computability escape, heartbeat increase, or new trusted
principle.
-/

import YMGap.Continuum.HeatKernelConvGen
import YMGap.Continuum.Z4DyadicConnectedWitnessRateProfileMassFloor
import YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowContraction

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowDistanceContraction

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentHeatBudget
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfileMassFloor
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalCompiler
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralFiberRow
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralRowFubini
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalCodeMass
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowContraction
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFubini

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

/-! ## 1. The physical distance selected by a realized row -/

/-- The observable-to-source distance of the same first expanded witness used
to define the row residual.  Unrealized rows receive distance zero. -/
def finePacketConnectedRateProfiledTerminalSkeletonRowDistance
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) : Nat :=
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
          finePacketGlobalNonzeroConnectedEntryDistance
            S orientation observableFaceId hobservableFace reference.1

theorem finePacketConnectedRateProfiledTerminalSkeletonRowDistance_eq_of_selected
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
    finePacketConnectedRateProfiledTerminalSkeletonRowDistance
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace row =
      finePacketGlobalNonzeroConnectedEntryDistance
        S orientation observableFaceId hobservableFace reference.1 := by
  unfold finePacketConnectedRateProfiledTerminalSkeletonRowDistance
  simp only [hstructural, hreference]

/-! ## 2. The row profile pays the selected distance -/

theorem finePacketConnectedRateProfiledTerminalSkeletonRowDistance_le_profileMass
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
    finePacketConnectedRateProfiledTerminalSkeletonRowDistance
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace row ≤
      (row.fineExterior + row.fineCore) +
        (row.coarseExterior + row.coarseCore) := by
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
  have hcompiledRow :=
    finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_eq_of_mem_row
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row structural hstructural
  have hfineExterior := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.fineExterior
      hcompiledRow
  have hfineCore := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.fineCore hcompiledRow
  have hcoarseExterior := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.coarseExterior
      hcompiledRow
  have hcoarseCore := congrArg
    FinePacketConnectedRateProfiledTerminalSkeletonRowCode.coarseCore
      hcompiledRow
  have hfineExterior' : structural.fineProfile.2.2.1 = row.fineExterior := by
    simpa only [
      finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_fineExterior]
      using hfineExterior
  have hfineCore' : structural.fineProfile.2.2.2 = row.fineCore := by
    simpa only [
      finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_fineCore]
      using hfineCore
  have hcoarseExterior' : structural.coarseProfile.2.2.1 =
      row.coarseExterior := by
    simpa only [
      finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_coarseExterior]
      using hcoarseExterior
  have hcoarseCore' : structural.coarseProfile.2.2.2 = row.coarseCore := by
    simpa only [
      finePacketConnectedRateProfiledTerminalSkeletonRowCompiler_coarseCore]
      using hcoarseCore
  have hmassStructural :
      finePacketConnectedFourEntryRateProfiledCompilerCodeMass
          (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledTerminalCode
            S rate hrate0 orientation observableFaceId hobservableFace reference) =
        (structural.fineProfile.2.2.1 + structural.fineProfile.2.2.2) +
          (structural.coarseProfile.2.2.1 +
            structural.coarseProfile.2.2.2) := by
    rw [hreferenceStructural]
    rfl
  have hmass :
      finePacketConnectedFourEntryRateProfiledCompilerCodeMass
          (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledTerminalCode
            S rate hrate0 orientation observableFaceId hobservableFace reference) =
        (row.fineExterior + row.fineCore) +
          (row.coarseExterior + row.coarseCore) := by
    rw [hmassStructural, hfineExterior', hfineCore', hcoarseExterior',
      hcoarseCore']
  rw [finePacketConnectedRateProfiledTerminalSkeletonRowDistance_eq_of_selected
    S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
      hobservableFace row structural hfirst reference hreference]
  have hdistance :=
    finePacketGlobalNonzeroConnectedExpandedWitness_distance_le_rateTotalProfileMass
      S rate hrate0 orientation observableFaceId hobservableFace reference
  rw [← finePacketConnectedFourEntryRateProfiledCompilerCodeMass_compiler
    S rate hrate0 orientation observableFaceId hobservableFace reference]
    at hdistance
  simpa only [
    finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledTerminalCode]
    using hmass ▸ hdistance

/-! ## 3. Replace profile mass by physical distance in the complete sum -/

theorem finePacketConnectedRateProfiledTerminalSkeletonRowContractedTerm_le_distanceTerm
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
    (Q'.mkPos 8 25 (by decide)) ^
          ((row.fineExterior + row.fineCore) +
            (row.coarseExterior + row.coarseCore)) *
        finePacketConnectedRateProfiledTerminalSkeletonRowResidual
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace row ≤
      (Q'.mkPos 8 25 (by decide)) ^
          (finePacketConnectedRateProfiledTerminalSkeletonRowDistance
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace row) *
        finePacketConnectedRateProfiledTerminalSkeletonRowResidual
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace row := by
  have hpower := YMGap.Continuum.HKConvGen.pow_base_antitone
    (r := Q'.mkPos 8 25 (by decide)) (by decide) (by decide)
    (finePacketConnectedRateProfiledTerminalSkeletonRowDistance_le_profileMass
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row hrow)
  exact Q'.mul_le_mul_of_nonneg_right _ _ _ hpower
    (finePacketConnectedRateProfiledTerminalSkeletonRowResidual_nonnegative
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row)

/-- The remaining selected residual rows, now weighted by the actual
observable-to-source distance rather than their larger compiler profile. -/
def finePacketConnectedRateProfiledTerminalSkeletonDistanceContractedMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) : Q' :=
  listQSum
    (fun row =>
      (Q'.mkPos 8 25 (by decide)) ^
          (finePacketConnectedRateProfiledTerminalSkeletonRowDistance
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace row) *
        finePacketConnectedRateProfiledTerminalSkeletonRowResidual
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace row)
    (finePacketConnectedRateProfiledTerminalSkeletonRowCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)

theorem finePacketConnectedRateProfiledTerminalSkeletonContractedMass_le_distanceContractedMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketConnectedRateProfiledTerminalSkeletonContractedMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace ≤
      finePacketConnectedRateProfiledTerminalSkeletonDistanceContractedMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace := by
  unfold finePacketConnectedRateProfiledTerminalSkeletonContractedMass
    finePacketConnectedRateProfiledTerminalSkeletonDistanceContractedMass
  apply listQSum_le_termwise_local
  intro row hrow
  exact
    finePacketConnectedRateProfiledTerminalSkeletonRowContractedTerm_le_distanceTerm
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row hrow

/-- Complete finite spatial contraction: the profiled terminal-code mass is
bounded by selected normalized rows carrying `(8/25)^distance`. -/
theorem finePacketConnectedRateProfiledTerminalCodeMass_le_terminalSkeletonDistanceContractedMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketConnectedRateProfiledTerminalCodeMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace ≤
      finePacketConnectedRateProfiledTerminalSkeletonDistanceContractedMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace := by
  exact Q'.le_trans' _ _ _
    (finePacketConnectedRateProfiledTerminalCodeMass_le_terminalSkeletonContractedMass
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)
    (finePacketConnectedRateProfiledTerminalSkeletonContractedMass_le_distanceContractedMass
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)

#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowDistance
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowDistance_eq_of_selected
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowDistance_le_profileMass
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowContractedTerm_le_distanceTerm
#print axioms finePacketConnectedRateProfiledTerminalSkeletonDistanceContractedMass
#print axioms finePacketConnectedRateProfiledTerminalSkeletonContractedMass_le_distanceContractedMass
#print axioms finePacketConnectedRateProfiledTerminalCodeMass_le_terminalSkeletonDistanceContractedMass

end YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowDistanceContraction
