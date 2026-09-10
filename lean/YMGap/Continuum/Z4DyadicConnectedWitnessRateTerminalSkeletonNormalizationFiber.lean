/-
# Separate terminal-row history entropy from Gibbs normalization coordinates

After reserving physical distance, a terminal/skeleton row carries the weight

  (8/25)^distance * (8/25)^profileSurplus * rowResidual.

The distance and residual depend only on the source rows, physical target
rows, and accepted terminal states, not on the retained skeleton history.
This module makes that separation literal.  It compiles each row to a finite
normalization key retaining precisely those coordinates (as well as the
already-computed distance and residual), reindexes the complete row sum by
exact finite Fubini, and factors each inverse fiber as

  (8/25)^distance * historyFugacity * rowResidual.

Thus the next frontier is the explicit history fugacity of one normalization
fiber.  No normalization ceiling is assumed here.

Constructive contract: decidable finite images, exact fiber Fubini, and
rational distributivity only; no classical choice, proof hole, trusted
external computation, computability escape, heartbeat increase, or new
trusted principle.
-/

import YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowDistanceSurplus

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonNormalizationFiber

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowContraction
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowDistanceContraction
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowDistanceSurplus
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFubini

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

private theorem listQSum_mul_right_local {A : Type}
    (weight : A → Q') (factor : Q') (items : List A) :
    listQSum (fun item => weight item * factor) items ≈
      listQSum weight items * factor := by
  have hcommute :
      listQSum (fun item => weight item * factor) items ≈
        listQSum (fun item => factor * weight item) items :=
    listQSum_congr (fun item => Q'.mul_comm_eqv _ _) _
  exact Q'.eqv_trans _ _ _ hcommute
    (Q'.eqv_trans _ _ _
      (listQSum_mul_left factor weight items)
      (Q'.mul_comm_eqv factor (listQSum weight items)))

/-! ## 1. The exact normalization key -/

/-- Geometric coordinates on which the selected row residual and physical
distance are constant.  Skeletons and the four profile counters are absent. -/
structure FinePacketConnectedRateTerminalSkeletonNormalizationKey : Type where
  leftSource : List Nat
  rightSource : List Nat
  leftTarget : List Nat
  rightTarget : List Nat
  fineTerminal : SlabExpandedFineTargetKey × SlabExpandedFineTargetKey
  coarseTerminal : SlabExpandedFineTargetKey × SlabExpandedFineTargetKey
deriving DecidableEq

/-- Keep distance and residual in a shallow first coordinate so their
compiler projections do not normalize the larger geometric key. -/
abbrev FinePacketConnectedRateTerminalSkeletonNormalizationCode :=
  (Nat × Q') × FinePacketConnectedRateTerminalSkeletonNormalizationKey

namespace FinePacketConnectedRateTerminalSkeletonNormalizationCode

def distance (code : FinePacketConnectedRateTerminalSkeletonNormalizationCode) :=
  code.1.1
def residual (code : FinePacketConnectedRateTerminalSkeletonNormalizationCode) :=
  code.1.2
def key (code : FinePacketConnectedRateTerminalSkeletonNormalizationCode) :=
  code.2

end FinePacketConnectedRateTerminalSkeletonNormalizationCode

/-- Shallow constructor kept separate so scalar projections never force the
normalization geometry. -/
def terminalSkeletonNormalizationCode {A : Type}
    (distance : A → Nat) (residual : A → Q')
    (key : A → FinePacketConnectedRateTerminalSkeletonNormalizationKey)
    (item : A) : FinePacketConnectedRateTerminalSkeletonNormalizationCode :=
  ((distance item, residual item), key item)

theorem terminalSkeletonNormalizationCode_distance {A : Type}
    (distance : A → Nat) (residual : A → Q')
    (key : A → FinePacketConnectedRateTerminalSkeletonNormalizationKey)
    (item : A) :
    (terminalSkeletonNormalizationCode distance residual key item).distance =
      distance item := by
  rfl

theorem terminalSkeletonNormalizationCode_residual {A : Type}
    (distance : A → Nat) (residual : A → Q')
    (key : A → FinePacketConnectedRateTerminalSkeletonNormalizationKey)
    (item : A) :
    (terminalSkeletonNormalizationCode distance residual key item).residual =
      residual item := by
  rfl

def finePacketConnectedRateTerminalSkeletonNormalizationKeyCompiler
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) :
    FinePacketConnectedRateTerminalSkeletonNormalizationKey where
  leftSource := row.leftSource
  rightSource := row.rightSource
  leftTarget := row.leftTarget
  rightTarget := row.rightTarget
  fineTerminal := row.fineTerminal
  coarseTerminal := row.coarseTerminal

def finePacketConnectedRateTerminalSkeletonNormalizationCompiler
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) :
    FinePacketConnectedRateTerminalSkeletonNormalizationCode :=
  terminalSkeletonNormalizationCode
    (finePacketConnectedRateProfiledTerminalSkeletonRowDistance
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)
    (finePacketConnectedRateProfiledTerminalSkeletonRowResidual
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)
    finePacketConnectedRateTerminalSkeletonNormalizationKeyCompiler row

theorem finePacketConnectedRateTerminalSkeletonNormalizationCompiler_distance
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) :
    FinePacketConnectedRateTerminalSkeletonNormalizationCode.distance
      (finePacketConnectedRateTerminalSkeletonNormalizationCompiler
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row) =
      finePacketConnectedRateProfiledTerminalSkeletonRowDistance
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace row := by
  simpa only [finePacketConnectedRateTerminalSkeletonNormalizationCompiler]
    using terminalSkeletonNormalizationCode_distance
      (finePacketConnectedRateProfiledTerminalSkeletonRowDistance
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace)
      (finePacketConnectedRateProfiledTerminalSkeletonRowResidual
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace)
      finePacketConnectedRateTerminalSkeletonNormalizationKeyCompiler row

theorem finePacketConnectedRateTerminalSkeletonNormalizationCompiler_residual
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) :
    FinePacketConnectedRateTerminalSkeletonNormalizationCode.residual
      (finePacketConnectedRateTerminalSkeletonNormalizationCompiler
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row) =
      finePacketConnectedRateProfiledTerminalSkeletonRowResidual
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace row := by
  simpa only [finePacketConnectedRateTerminalSkeletonNormalizationCompiler]
    using terminalSkeletonNormalizationCode_residual
      (finePacketConnectedRateProfiledTerminalSkeletonRowDistance
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace)
      (finePacketConnectedRateProfiledTerminalSkeletonRowResidual
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace)
      finePacketConnectedRateTerminalSkeletonNormalizationKeyCompiler row

def finePacketConnectedRateTerminalSkeletonNormalizationCodes
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    List FinePacketConnectedRateTerminalSkeletonNormalizationCode :=
  ((finePacketConnectedRateProfiledTerminalSkeletonRowCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace).map
    (finePacketConnectedRateTerminalSkeletonNormalizationCompiler
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)).eraseDups

theorem finePacketConnectedRateTerminalSkeletonNormalizationCodes_nodup
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    (finePacketConnectedRateTerminalSkeletonNormalizationCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace).Nodup := by
  unfold finePacketConnectedRateTerminalSkeletonNormalizationCodes
  exact eraseDupsNodupLocal _

theorem finePacketConnectedRateTerminalSkeletonNormalizationCompiler_mem
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
    finePacketConnectedRateTerminalSkeletonNormalizationCompiler
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace row ∈
      finePacketConnectedRateTerminalSkeletonNormalizationCodes
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace := by
  apply List.mem_eraseDups.mpr
  exact List.mem_map.mpr ⟨row, hrow, rfl⟩

/-! ## 2. The history fugacity in one normalization fiber -/

def finePacketConnectedRateTerminalSkeletonHistoryFugacityWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) : Q' :=
  (Q'.mkPos 8 25 (by decide)) ^
    (finePacketConnectedRateProfiledTerminalSkeletonRowProfileSurplus
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace row)

def finePacketConnectedRateTerminalSkeletonHistoryFugacity
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (code : FinePacketConnectedRateTerminalSkeletonNormalizationCode) : Q' :=
  fiberWeight
    (finePacketConnectedRateProfiledTerminalSkeletonRowCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)
    (finePacketConnectedRateTerminalSkeletonHistoryFugacityWeight
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)
    (finePacketConnectedRateTerminalSkeletonNormalizationCompiler
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)
    code

/-- The complete distance/surplus summand, named for exact fiber Fubini. -/
def finePacketConnectedRateTerminalSkeletonDistanceSurplusWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode) : Q' :=
  (Q'.mkPos 8 25 (by decide)) ^
      (finePacketConnectedRateProfiledTerminalSkeletonRowDistance
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace row) *
    ((Q'.mkPos 8 25 (by decide)) ^
        (finePacketConnectedRateProfiledTerminalSkeletonRowProfileSurplus
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace row) *
      finePacketConnectedRateProfiledTerminalSkeletonRowResidual
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace row)

theorem finePacketConnectedRateTerminalSkeletonDistanceSurplusFiber_eqv_normalizedHistory
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (code : FinePacketConnectedRateTerminalSkeletonNormalizationCode) :
    fiberWeight
        (finePacketConnectedRateProfiledTerminalSkeletonRowCodes
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace)
        (finePacketConnectedRateTerminalSkeletonDistanceSurplusWeight
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace)
        (finePacketConnectedRateTerminalSkeletonNormalizationCompiler
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace)
        code ≈
      (Q'.mkPos 8 25 (by decide)) ^ code.distance *
        (finePacketConnectedRateTerminalSkeletonHistoryFugacity
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace code *
          code.residual) := by
  let rows := finePacketConnectedRateProfiledTerminalSkeletonRowCodes
    S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
      hobservableFace
  let compiler := finePacketConnectedRateTerminalSkeletonNormalizationCompiler
    S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
      hobservableFace
  let history := finePacketConnectedRateTerminalSkeletonHistoryFugacityWeight
    S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
      hobservableFace
  let selected := rows.filter (fun row => decide (code = compiler row))
  have hagree :
      listQSum
          (finePacketConnectedRateTerminalSkeletonDistanceSurplusWeight
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace)
          selected ≈
        listQSum
          (fun row =>
            (Q'.mkPos 8 25 (by decide)) ^ code.distance *
              (history row * code.residual))
          selected := by
    apply listQSum_congr_on
    intro row hrow
    have hparts := List.mem_filter.mp hrow
    have hcode : code = compiler row := of_decide_eq_true hparts.2
    have hdistance := congrArg
      FinePacketConnectedRateTerminalSkeletonNormalizationCode.distance hcode
    have hresidual := congrArg
      FinePacketConnectedRateTerminalSkeletonNormalizationCode.residual hcode
    rw [finePacketConnectedRateTerminalSkeletonNormalizationCompiler_distance]
      at hdistance
    rw [finePacketConnectedRateTerminalSkeletonNormalizationCompiler_residual]
      at hresidual
    unfold
      finePacketConnectedRateTerminalSkeletonDistanceSurplusWeight
      history
      finePacketConnectedRateTerminalSkeletonHistoryFugacityWeight
    rw [← hdistance, ← hresidual]
    exact Q'.eqv_refl _
  have hleft := listQSum_mul_left
    ((Q'.mkPos 8 25 (by decide)) ^ code.distance)
    (fun row => history row * code.residual) selected
  have hright := listQSum_mul_right_local history code.residual selected
  unfold fiberWeight
  change listQSum _ selected ≈ _
  refine Q'.eqv_trans _ _ _ hagree ?_
  refine Q'.eqv_trans _ _ _ hleft ?_
  exact Q'.mul_eqv_congr_left _ _ _ (by
    unfold finePacketConnectedRateTerminalSkeletonHistoryFugacity
      fiberWeight
    simpa only [rows, compiler, history, selected] using hright)

/-! ## 3. Exact normalization-fiber Fubini -/

def finePacketConnectedRateTerminalSkeletonNormalizationMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) : Q' :=
  listQSum
    (fun code =>
      (Q'.mkPos 8 25 (by decide)) ^ code.distance *
        (finePacketConnectedRateTerminalSkeletonHistoryFugacity
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace code *
          code.residual))
    (finePacketConnectedRateTerminalSkeletonNormalizationCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)

theorem finePacketConnectedRateProfiledTerminalSkeletonDistanceSurplusMass_eqv_normalizationMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketConnectedRateProfiledTerminalSkeletonDistanceSurplusMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace ≈
      finePacketConnectedRateTerminalSkeletonNormalizationMass
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace := by
  let rows := finePacketConnectedRateProfiledTerminalSkeletonRowCodes
    S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
      hobservableFace
  let weight := finePacketConnectedRateTerminalSkeletonDistanceSurplusWeight
    S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
      hobservableFace
  let compiler := finePacketConnectedRateTerminalSkeletonNormalizationCompiler
    S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
      hobservableFace
  let codes := finePacketConnectedRateTerminalSkeletonNormalizationCodes
    S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
      hobservableFace
  have hfubini := fiberWeight_total rows weight compiler codes
    (finePacketConnectedRateTerminalSkeletonNormalizationCodes_nodup
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)
    (fun row hrow =>
      finePacketConnectedRateTerminalSkeletonNormalizationCompiler_mem
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace row hrow)
  have hfibers :
      listQSum (fiberWeight rows weight compiler) codes ≈
        finePacketConnectedRateTerminalSkeletonNormalizationMass
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace := by
    unfold finePacketConnectedRateTerminalSkeletonNormalizationMass
    apply listQSum_congr_on
    intro code _hcode
    exact
      finePacketConnectedRateTerminalSkeletonDistanceSurplusFiber_eqv_normalizedHistory
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace code
  refine Q'.eqv_trans _ (listQSum weight rows) _ ?_ ?_
  · unfold
      finePacketConnectedRateProfiledTerminalSkeletonDistanceSurplusMass
      finePacketConnectedRateProfiledTerminalSkeletonRowSpatialResidual
      weight
      finePacketConnectedRateTerminalSkeletonDistanceSurplusWeight
    exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hfubini) hfibers

#print axioms FinePacketConnectedRateTerminalSkeletonNormalizationKey
#print axioms FinePacketConnectedRateTerminalSkeletonNormalizationCode
#print axioms terminalSkeletonNormalizationCode
#print axioms terminalSkeletonNormalizationCode_distance
#print axioms terminalSkeletonNormalizationCode_residual
#print axioms finePacketConnectedRateTerminalSkeletonNormalizationKeyCompiler
#print axioms finePacketConnectedRateTerminalSkeletonNormalizationCompiler
#print axioms finePacketConnectedRateTerminalSkeletonNormalizationCompiler_distance
#print axioms finePacketConnectedRateTerminalSkeletonNormalizationCompiler_residual
#print axioms finePacketConnectedRateTerminalSkeletonNormalizationCodes
#print axioms finePacketConnectedRateTerminalSkeletonNormalizationCodes_nodup
#print axioms finePacketConnectedRateTerminalSkeletonNormalizationCompiler_mem
#print axioms finePacketConnectedRateTerminalSkeletonHistoryFugacityWeight
#print axioms finePacketConnectedRateTerminalSkeletonHistoryFugacity
#print axioms finePacketConnectedRateTerminalSkeletonDistanceSurplusWeight
#print axioms finePacketConnectedRateTerminalSkeletonDistanceSurplusFiber_eqv_normalizedHistory
#print axioms finePacketConnectedRateTerminalSkeletonNormalizationMass
#print axioms finePacketConnectedRateProfiledTerminalSkeletonDistanceSurplusMass_eqv_normalizationMass

end YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonNormalizationFiber
