/-
# Expose the exact mass distribution of one terminal-history fiber

The two-rate normalization leaves one explicit history fugacity

  sum_{rows in one normalization fiber} historyRate^(profileMass row).

This module partitions that finite sum by the exact natural profile mass.  If
`N(code,mass)` is the number of realized rows in the normalization fiber with
that mass, exact finite Fubini gives

  historyFugacity(code)
    = sum_mass N(code,mass) * historyRate^mass.

This is deliberately an identity, not an entropy estimate.  It exposes the
precise coefficient that the canonical-peeling inverse compiler must bound.

Constructive contract: decidable finite images, list cardinalities, and exact
rational finite sums only; no classical choice, proof hole, trusted external
computation, computability escape, heartbeat increase, or new trusted
principle.
-/

import YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonTwoRateNormalizationFiber

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonHistoryMassFiber

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowDistanceSurplus
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFubini
open YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonNormalizationFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonTwoRateNormalizationFiber

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

private theorem listQSum_const_local {A : Type} (constant : Q') :
    ∀ items : List A,
      listQSum (fun _item => constant) items ≈
        Q'.ofNat items.length * constant
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv constant)
  | _first :: rest => by
      refine Q'.eqv_trans _
        (constant + Q'.ofNat rest.length * constant) _ ?_ ?_
      · exact Q'.add_eqv_congr_left constant _ _
          (listQSum_const_local constant rest)
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _
        ((Q'.ofNat rest.length + 1) * constant) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ constant
          (Q'.ofNat_add_eqv rest.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat rest.length * constant + (1 : Q') * constant) _
        (Q'.add_mul_eqv (Q'.ofNat rest.length) 1 constant) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat rest.length * constant + constant) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv constant))
        (Q'.add_comm_eqv
          (Q'.ofNat rest.length * constant) constant)

/-! ## 1. The realized rows and masses in one normalization fiber -/

def finePacketConnectedRateTerminalSkeletonRowsAtNormalizationCode
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (code : FinePacketConnectedRateTerminalSkeletonNormalizationCode) :
    List FinePacketConnectedRateProfiledTerminalSkeletonRowCode :=
  (finePacketConnectedRateProfiledTerminalSkeletonRowCodes
    S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
      hobservableFace).filter
    (fun row => decide
      (code = finePacketConnectedRateTerminalSkeletonNormalizationCompiler
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace row))

theorem finePacketConnectedRateTerminalSkeletonRowsAtNormalizationCode_nodup
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (code : FinePacketConnectedRateTerminalSkeletonNormalizationCode) :
    (finePacketConnectedRateTerminalSkeletonRowsAtNormalizationCode
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace code).Nodup := by
  unfold finePacketConnectedRateTerminalSkeletonRowsAtNormalizationCode
  exact List.filter_sublist.nodup
    (finePacketConnectedRateProfiledTerminalSkeletonRowCodes_nodup
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)

def finePacketConnectedRateTerminalSkeletonHistoryMassCodes
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (code : FinePacketConnectedRateTerminalSkeletonNormalizationCode) :
    List Nat :=
  ((finePacketConnectedRateTerminalSkeletonRowsAtNormalizationCode
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace code).map
    finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass).eraseDups

theorem finePacketConnectedRateTerminalSkeletonHistoryMassCodes_nodup
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (code : FinePacketConnectedRateTerminalSkeletonNormalizationCode) :
    (finePacketConnectedRateTerminalSkeletonHistoryMassCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace code).Nodup := by
  unfold finePacketConnectedRateTerminalSkeletonHistoryMassCodes
  exact eraseDupsNodupLocal _

theorem finePacketConnectedRateTerminalSkeletonHistoryMass_mem
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (code : FinePacketConnectedRateTerminalSkeletonNormalizationCode)
    (row : FinePacketConnectedRateProfiledTerminalSkeletonRowCode)
    (hrow : row ∈
      finePacketConnectedRateTerminalSkeletonRowsAtNormalizationCode
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace code) :
    finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass row ∈
      finePacketConnectedRateTerminalSkeletonHistoryMassCodes
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace code := by
  apply List.mem_eraseDups.mpr
  exact List.mem_map.mpr ⟨row, hrow, rfl⟩

def finePacketConnectedRateTerminalSkeletonHistoryMassMultiplicity
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (code : FinePacketConnectedRateTerminalSkeletonNormalizationCode)
    (mass : Nat) : Nat :=
  ((finePacketConnectedRateTerminalSkeletonRowsAtNormalizationCode
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace code).filter
    (fun row => decide
      (mass =
        finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass row))).length

/-! ## 2. Exact weighted mass generating function -/

theorem finePacketConnectedRateTerminalSkeletonHistoryMassFiber_eqv_multiplicity
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (historyRate : Q')
    (code : FinePacketConnectedRateTerminalSkeletonNormalizationCode)
    (mass : Nat) :
    fiberWeight
        (finePacketConnectedRateTerminalSkeletonRowsAtNormalizationCode
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace code)
        (finePacketConnectedRateTerminalSkeletonHistoryPowerWeight historyRate)
        finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass
        mass ≈
      Q'.ofNat
          (finePacketConnectedRateTerminalSkeletonHistoryMassMultiplicity
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace code mass) *
        historyRate ^ mass := by
  let rows :=
    finePacketConnectedRateTerminalSkeletonRowsAtNormalizationCode
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace code
  let selected := rows.filter (fun row => decide
    (mass = finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass row))
  have hagree :
      listQSum
          (finePacketConnectedRateTerminalSkeletonHistoryPowerWeight historyRate)
          selected ≈
        listQSum (fun _row => historyRate ^ mass) selected := by
    apply listQSum_congr_on
    intro row hrow
    have hmass : mass =
        finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass row :=
      of_decide_eq_true (List.mem_filter.mp hrow).2
    unfold finePacketConnectedRateTerminalSkeletonHistoryPowerWeight
    rw [← hmass]
    exact Q'.eqv_refl _
  unfold fiberWeight
  change listQSum _ selected ≈ _
  refine Q'.eqv_trans _ _ _ hagree ?_
  simpa only [rows, selected,
    finePacketConnectedRateTerminalSkeletonHistoryMassMultiplicity] using
      listQSum_const_local (historyRate ^ mass) selected

def finePacketConnectedRateTerminalSkeletonHistoryMassGeneratingFunction
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (historyRate : Q')
    (code : FinePacketConnectedRateTerminalSkeletonNormalizationCode) : Q' :=
  listQSum
    (fun mass =>
      Q'.ofNat
          (finePacketConnectedRateTerminalSkeletonHistoryMassMultiplicity
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace code mass) *
        historyRate ^ mass)
    (finePacketConnectedRateTerminalSkeletonHistoryMassCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace code)

theorem finePacketConnectedRateTerminalSkeletonHistoryPowerFugacity_eqv_massGeneratingFunction
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (historyRate : Q')
    (code : FinePacketConnectedRateTerminalSkeletonNormalizationCode) :
    finePacketConnectedRateTerminalSkeletonHistoryPowerFugacity
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace historyRate code ≈
      finePacketConnectedRateTerminalSkeletonHistoryMassGeneratingFunction
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace historyRate code := by
  let rows :=
    finePacketConnectedRateTerminalSkeletonRowsAtNormalizationCode
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace code
  let weight :=
    finePacketConnectedRateTerminalSkeletonHistoryPowerWeight historyRate
  let masses :=
    finePacketConnectedRateTerminalSkeletonHistoryMassCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace code
  have hfubini := fiberWeight_total rows weight
    finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass masses
    (finePacketConnectedRateTerminalSkeletonHistoryMassCodes_nodup
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace code)
    (fun row hrow =>
      finePacketConnectedRateTerminalSkeletonHistoryMass_mem
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace code row hrow)
  have hfibers :
      listQSum
          (fiberWeight rows weight
            finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass)
          masses ≈
        finePacketConnectedRateTerminalSkeletonHistoryMassGeneratingFunction
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace historyRate code := by
    unfold
      finePacketConnectedRateTerminalSkeletonHistoryMassGeneratingFunction
    apply listQSum_congr_on
    intro mass _hmass
    exact
      finePacketConnectedRateTerminalSkeletonHistoryMassFiber_eqv_multiplicity
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace historyRate code mass
  unfold finePacketConnectedRateTerminalSkeletonHistoryPowerFugacity
    fiberWeight
  change listQSum weight rows ≈ _
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hfubini) hfibers

#print axioms finePacketConnectedRateTerminalSkeletonRowsAtNormalizationCode
#print axioms finePacketConnectedRateTerminalSkeletonRowsAtNormalizationCode_nodup
#print axioms finePacketConnectedRateTerminalSkeletonHistoryMassCodes
#print axioms finePacketConnectedRateTerminalSkeletonHistoryMassCodes_nodup
#print axioms finePacketConnectedRateTerminalSkeletonHistoryMass_mem
#print axioms finePacketConnectedRateTerminalSkeletonHistoryMassMultiplicity
#print axioms finePacketConnectedRateTerminalSkeletonHistoryMassFiber_eqv_multiplicity
#print axioms finePacketConnectedRateTerminalSkeletonHistoryMassGeneratingFunction
#print axioms finePacketConnectedRateTerminalSkeletonHistoryPowerFugacity_eqv_massGeneratingFunction

end YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonHistoryMassFiber
