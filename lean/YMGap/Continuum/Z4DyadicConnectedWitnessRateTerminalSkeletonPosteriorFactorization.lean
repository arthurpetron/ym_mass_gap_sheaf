/-
# Expose the terminal-row residual as a lowering multiplicity times a posterior

The terminal-skeleton contraction currently leaves one selected residual per
row.  That residual is not an opaque constant: the structural lowering-row
weight is constant over the exact oriented four-word carrier.  Consequently
the residual is exactly

  oriented lowering multiplicity * beta-dependent terminal posterior weight.

This factorization identifies the two pieces that the next weighted history
argument must treat differently.  The finite SU(2) lowering multiplicity is
combinatorial, while the terminal posterior retains the exact source-row
normalization and all coupling dependence.  No bound on either factor and no
uniformity claim is made here.

Constructive contract: literal finite lists, finite search, and exact rational
setoid algebra only; no classical choice, proof hole, trusted external
computation, computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonNormalizationRigidity

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonPosteriorFactorization

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledNormalizedTerminalCompiler
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralFiberRow
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralLoweringCarrier
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledStructuralRowFubini
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowAdaptiveAnchor
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowContraction
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFubini
open YMGap.Continuum.Z4DyadicConnectedWitnessRateSpatialTerminalResidual
open YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonNormalizationRigidity

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_const_local {A : Type} (constant : Q') :
    forall items : List A,
      listQSum (fun _item => constant) items ≈
        Q'.ofNat items.length * constant
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv constant)
  | _head :: tail => by
      refine Q'.eqv_trans _
        (constant + Q'.ofNat tail.length * constant) _ ?_ ?_
      · exact Q'.add_eqv_congr_left constant _ _
          (listQSum_const_local constant tail)
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _
        ((Q'.ofNat tail.length + 1) * constant) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ constant
          (Q'.ofNat_add_eqv tail.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat tail.length * constant + (1 : Q') * constant) _
        (Q'.add_mul_eqv (Q'.ofNat tail.length) 1 constant) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat tail.length * constant + constant) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv constant))
        (Q'.add_comm_eqv _ constant)

/-! ## 1. The two exact factors selected by a realized row -/

/-- Number of literal four-word lowering witnesses in the selected physical
row.  The same finite search used by the existing row residual is reused, so
unrealized rows receive zero. -/
def finePacketConnectedRateProfiledTerminalSkeletonRowLoweringMultiplicity
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
          (finePacketGlobalNonzeroConnectedExpandedWitnessLoweringCodeCarrier
            S orientation observableFaceId reference).length

/-- The selected terminal accepted-state weight divided by the exact product
of the two physical source-row normalizations.  In particular this factor is
explicitly coupling-dependent through `S`, `rate`, and both positivity
witnesses. -/
def finePacketConnectedRateProfiledTerminalSkeletonRowTerminalPosterior
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
          finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalResidual
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace reference

/-! ## 2. Exact posterior factorization -/

/-- Before selecting a row representative, the literal lowering-row residual
is already exactly its carrier cardinality times the normalized terminal
weight. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowResidual_eqv_multiplicity_mul_terminalResidual
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (reference : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowResidual
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace reference ≈
      Q'.ofNat
          (finePacketGlobalNonzeroConnectedExpandedWitnessLoweringCodeCarrier
            S orientation observableFaceId reference).length *
        finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalResidual
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace reference := by
  unfold
    finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowResidual
    finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowResidualWeight
  refine Q'.eqv_trans _ _ _
    (listQSum_const_local
      (finePacketConnectedFourEntryRateProfiledCompilerCodeNormalizedTerminalResidual
        S hfineCutoff hcoarseCoupling rate hrate0
          (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledTerminalCode
            S rate hrate0 orientation observableFaceId hobservableFace reference))
      (finePacketGlobalNonzeroConnectedExpandedWitnessLoweringCodeCarrier
        S orientation observableFaceId reference)) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (finePacketConnectedFourEntryRateProfiledCompilerCodeNormalizedTerminalResidual_compiler
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace reference)

theorem finePacketConnectedRateProfiledTerminalSkeletonRowLoweringMultiplicity_eq_of_selected
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
    finePacketConnectedRateProfiledTerminalSkeletonRowLoweringMultiplicity
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace row =
      (finePacketGlobalNonzeroConnectedExpandedWitnessLoweringCodeCarrier
        S orientation observableFaceId reference).length := by
  unfold
    finePacketConnectedRateProfiledTerminalSkeletonRowLoweringMultiplicity
  simp only [hstructural, hreference]

theorem finePacketConnectedRateProfiledTerminalSkeletonRowTerminalPosterior_eq_of_selected
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
    finePacketConnectedRateProfiledTerminalSkeletonRowTerminalPosterior
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace row =
      finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalResidual
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace reference := by
  unfold finePacketConnectedRateProfiledTerminalSkeletonRowTerminalPosterior
  simp only [hstructural, hreference]

/-- For the representatives selected by the constructive row search, the
row residual therefore splits into the explicit lowering multiplicity and
the beta-dependent terminal posterior. -/
theorem finePacketConnectedRateProfiledTerminalSkeletonRowResidual_eqv_loweringMultiplicity_mul_terminalPosterior_of_selected
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
          hobservableFace row ≈
      Q'.ofNat
          (finePacketConnectedRateProfiledTerminalSkeletonRowLoweringMultiplicity
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace row) *
        finePacketConnectedRateProfiledTerminalSkeletonRowTerminalPosterior
          S hfineCutoff hcoarseCoupling rate hrate0 orientation
            observableFaceId hobservableFace row := by
  rw [finePacketConnectedRateProfiledTerminalSkeletonRowResidual_eq_of_selected
    S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
      hobservableFace row structural hstructural reference hreference]
  rw [finePacketConnectedRateProfiledTerminalSkeletonRowLoweringMultiplicity_eq_of_selected
    S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
      hobservableFace row structural hstructural reference hreference]
  rw [finePacketConnectedRateProfiledTerminalSkeletonRowTerminalPosterior_eq_of_selected
    S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
      hobservableFace row structural hstructural reference hreference]
  exact
    finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowResidual_eqv_multiplicity_mul_terminalResidual
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace reference

/-- The terminal posterior selected by any row is nonnegative. -/
theorem finePacketConnectedRateProfiledTerminalSkeletonRowTerminalPosterior_nonnegative
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) :
    (0 : Q') ≤
      finePacketConnectedRateProfiledTerminalSkeletonRowTerminalPosterior
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace row := by
  unfold finePacketConnectedRateProfiledTerminalSkeletonRowTerminalPosterior
  split
  · exact Q'.le_refl' 0
  · rename_i structural hstructural
    split
    · exact Q'.le_refl' 0
    · rename_i reference hreference
      exact
        finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalResidual_nonnegative
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace reference

#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowLoweringMultiplicity
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowTerminalPosterior
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessStructuralLoweringRowResidual_eqv_multiplicity_mul_terminalResidual
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowLoweringMultiplicity_eq_of_selected
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowTerminalPosterior_eq_of_selected
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowResidual_eqv_loweringMultiplicity_mul_terminalPosterior_of_selected
#print axioms finePacketConnectedRateProfiledTerminalSkeletonRowTerminalPosterior_nonnegative

end YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonPosteriorFactorization
