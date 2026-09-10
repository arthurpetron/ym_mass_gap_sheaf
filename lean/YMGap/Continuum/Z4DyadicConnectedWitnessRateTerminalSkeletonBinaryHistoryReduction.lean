/-
# Reduce terminal-history summation to a binary inverse compiler

For one fixed normalization code and profile mass `M`, a binary inverse
compiler sends every realized terminal/skeleton row injectively to a word in
`allSeqs 2 M`.  Such a compiler gives the sharp cardinality bound

  N(code,M) <= 2^M.

At the retained history rate `2/5`, the complete mass contribution is then

  N(code,M) * (2/5)^M <= (4/5)^M,

and the full finite history fugacity is at most `5`.  This module proves that
entire analytic implication.  The certificate type is intentionally left as
explicit data: constructing its encoder from canonical paired peeling is the
next geometric frontier.

Constructive contract: Type-valued compiler data, duplicate-free finite
injection, and exact rational geometric summation only; no classical choice,
proof hole, trusted external computation, computability escape, heartbeat
increase, or new trusted principle.
-/

import YMGap.Constructive.CharacterTail
import YMGap.Continuum.CayleyPruferInjection
import YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonHistoryMassFiber

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonBinaryHistoryReduction

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.CharacterTail
open YMGap.Constructive.RationalTail
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.FiniteBoolGraphSimplePaths
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowDistanceSurplus
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalSkeletonRowFubini
open YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonHistoryMassFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonNormalizationFiber
open YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonTwoRateNormalizationFiber

local infix:50 " ≈ " => Q'.eqv

private theorem nodup_map_of_injOn_local {A B : Type}
    (encode : A → B) : ∀ (items : List A),
    items.Nodup →
    (∀ left, left ∈ items → ∀ right, right ∈ items →
      encode left = encode right → left = right) →
    (items.map encode).Nodup
  | [], _, _ => List.nodup_nil
  | head :: tail, hitems, hinjective => by
      have hparts := List.nodup_cons.mp hitems
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨item, hitem, heq⟩ := List.mem_map.mp hmem
        have hsame := hinjective head List.mem_cons_self item
          (List.mem_cons_of_mem head hitem) heq.symm
        exact hparts.1 (hsame ▸ hitem)
      · exact nodup_map_of_injOn_local encode tail hparts.2
          (fun left hleft right hright heq =>
            hinjective left (List.mem_cons_of_mem head hleft)
              right (List.mem_cons_of_mem head hright) heq)

private theorem listQSum_range_eqv_finSum_local (value : Nat → Q') :
    ∀ count : Nat,
      listQSum value (List.range count) ≈ finSum value count
  | 0 => Q'.eqv_refl 0
  | count + 1 => by
      rw [List.range_succ, finSum_succ]
      exact Q'.eqv_trans _
        (listQSum value (List.range count) + listQSum value [count]) _
        (listQSum_append value (List.range count) [count])
        (Q'.add_eqv_congr'
          (listQSum_range_eqv_finSum_local value count)
          (Q'.eqv_of_eq (Q'.add_zero' (value count))))

private def listNatMax : List Nat → Nat
  | [] => 0
  | head :: tail => Nat.max head (listNatMax tail)

private theorem le_listNatMax_of_mem :
    ∀ {values : List Nat} {value : Nat},
      value ∈ values → value ≤ listNatMax values
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, value, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst value
        exact Nat.le_max_left _ _
      · exact Nat.le_trans (le_listNatMax_of_mem htail)
          (Nat.le_max_right _ _)

private theorem ofNat_pow_eqv_local (base : Nat) : ∀ exponent : Nat,
    Q'.ofNat (base ^ exponent) ≈ (Q'.ofNat base) ^ exponent
  | 0 => Q'.eqv_refl 1
  | exponent + 1 => by
      rw [Nat.pow_succ, Q'.pow_succ]
      refine Q'.eqv_trans _
        (Q'.ofNat (base ^ exponent) * Q'.ofNat base) _ ?_ ?_
      · exact
          YMGap.Continuum.HeatKernelRGStep.ofNat_mul_eqv
            (base ^ exponent) base
      · refine Q'.eqv_trans _
          ((Q'.ofNat base) ^ exponent * Q'.ofNat base) _ ?_ ?_
        · exact Q'.mul_eqv_congr_right _ _ _
            (ofNat_pow_eqv_local base exponent)
        · exact Q'.mul_comm_eqv _ _

private theorem mul_pow_eqv_local (left right : Q') : ∀ exponent : Nat,
    (left * right) ^ exponent ≈ left ^ exponent * right ^ exponent
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv 1)
  | exponent + 1 => by
      have hinductive := mul_pow_eqv_local left right exponent
      show
        (left * right) * (left * right) ^ exponent ≈
          (left * left ^ exponent) * (right * right ^ exponent)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (left * right) _ _ hinductive) ?_
      calc
        (left * right) * (left ^ exponent * right ^ exponent) ≈
            left * (right * (left ^ exponent * right ^ exponent)) :=
          Q'.mul_assoc_eqv _ _ _
        _ ≈ left * ((right * left ^ exponent) * right ^ exponent) :=
          Q'.mul_eqv_congr_left _ _ _
            (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
        _ ≈ left * ((left ^ exponent * right) * right ^ exponent) :=
          Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _))
        _ ≈ left * (left ^ exponent * (right * right ^ exponent)) :=
          Q'.mul_eqv_congr_left _ _ _ (Q'.mul_assoc_eqv _ _ _)
        _ ≈ (left * left ^ exponent) *
              (right * right ^ exponent) :=
          Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

private theorem pow_eqv_congr_local {left right : Q'}
    (h : left ≈ right) : ∀ exponent : Nat,
    left ^ exponent ≈ right ^ exponent
  | 0 => Q'.eqv_refl 1
  | exponent + 1 =>
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right left right (left ^ exponent) h)
        (Q'.mul_eqv_congr_left right _ _
          (pow_eqv_congr_local h exponent))

/-! ## 1. Explicit binary inverse data -/

/-- A mass-indexed, length-exact binary encoder for all rows in one
normalization fiber.  The injectivity field is scoped to one fixed mass, which
is precisely what the history generating function requires. -/
structure FinePacketConnectedRateTerminalSkeletonBinaryHistoryCertificate
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (code : FinePacketConnectedRateTerminalSkeletonNormalizationCode) :
    Type where
  encode : Nat → FinePacketConnectedRateProfiledTerminalSkeletonRowCode →
    List Nat
  encode_mem : ∀ mass row,
    row ∈ finePacketConnectedRateTerminalSkeletonRowsAtNormalizationCode
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace code →
    finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass row = mass →
    encode mass row ∈ allSeqs 2 mass
  injectiveAtMass : ∀ mass left,
    left ∈ finePacketConnectedRateTerminalSkeletonRowsAtNormalizationCode
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace code →
    finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass left = mass →
    ∀ right,
    right ∈ finePacketConnectedRateTerminalSkeletonRowsAtNormalizationCode
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace code →
    finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass right = mass →
    encode mass left = encode mass right → left = right

theorem finePacketConnectedRateTerminalSkeletonHistoryMassMultiplicity_le_binary
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (code : FinePacketConnectedRateTerminalSkeletonNormalizationCode)
    (certificate :
      FinePacketConnectedRateTerminalSkeletonBinaryHistoryCertificate
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace code)
    (mass : Nat) :
    finePacketConnectedRateTerminalSkeletonHistoryMassMultiplicity
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace code mass ≤
      2 ^ mass := by
  let rows :=
    finePacketConnectedRateTerminalSkeletonRowsAtNormalizationCode
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace code
  let selected := rows.filter (fun row => decide
    (mass = finePacketConnectedRateProfiledTerminalSkeletonRowProfileMass row))
  let encode := certificate.encode mass
  have hselectedNodup : selected.Nodup :=
    List.filter_sublist.nodup
      (finePacketConnectedRateTerminalSkeletonRowsAtNormalizationCode_nodup
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace code)
  have hencodeNodup : (selected.map encode).Nodup := by
    apply nodup_map_of_injOn_local encode selected hselectedNodup
    intro left hleft right hright hencoded
    have hleftParts := List.mem_filter.mp hleft
    have hrightParts := List.mem_filter.mp hright
    exact certificate.injectiveAtMass mass left hleftParts.1
      (of_decide_eq_true hleftParts.2).symm right hrightParts.1
      (of_decide_eq_true hrightParts.2).symm hencoded
  have hsubset : ∀ word, word ∈ selected.map encode →
      word ∈ allSeqs 2 mass := by
    intro word hword
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hword
    have hparts := List.mem_filter.mp hrow
    exact certificate.encode_mem mass row hparts.1
      (of_decide_eq_true hparts.2).symm
  have hlength := FiniteListBound.nodup_subset_length_le
    (selected.map encode) (allSeqs 2 mass) hencodeNodup hsubset
  rw [List.length_map, length_allSeqs] at hlength
  simpa only [rows, selected,
    finePacketConnectedRateTerminalSkeletonHistoryMassMultiplicity] using
      hlength

/-! ## 2. Binary multiplicity is paid by the retained history rate -/

theorem binaryMultiplicity_twoFifths_eqv_fourFifths (mass : Nat) :
    Q'.ofNat (2 ^ mass) * (Q'.mkPos 2 5 (by decide)) ^ mass ≈
      (Q'.mkPos 4 5 (by decide)) ^ mass := by
  refine Q'.eqv_trans _
    ((Q'.ofNat 2) ^ mass * (Q'.mkPos 2 5 (by decide)) ^ mass) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ (ofNat_pow_eqv_local 2 mass)
  refine Q'.eqv_trans _
    ((Q'.ofNat 2 * Q'.mkPos 2 5 (by decide)) ^ mass) _ ?_ ?_
  · exact Q'.eqv_symm
      (mul_pow_eqv_local (Q'.ofNat 2) (Q'.mkPos 2 5 (by decide)) mass)
  · exact pow_eqv_congr_local (by decide) mass

theorem finePacketConnectedRateTerminalSkeletonHistoryMassTerm_le_fourFifths
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (code : FinePacketConnectedRateTerminalSkeletonNormalizationCode)
    (certificate :
      FinePacketConnectedRateTerminalSkeletonBinaryHistoryCertificate
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace code)
    (mass : Nat) :
    Q'.ofNat
          (finePacketConnectedRateTerminalSkeletonHistoryMassMultiplicity
            S hfineCutoff hcoarseCoupling rate hrate0 orientation
              observableFaceId hobservableFace code mass) *
        (Q'.mkPos 2 5 (by decide)) ^ mass ≤
      (Q'.mkPos 4 5 (by decide)) ^ mass := by
  have hcount :=
    finePacketConnectedRateTerminalSkeletonHistoryMassMultiplicity_le_binary
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace code certificate mass
  have hcast := Q'.ofNat_le_ofNat hcount
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _ hcast
    (Q'.pow_nonneg (Q'.mkPos 2 5 (by decide)) (by decide) mass)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv (binaryMultiplicity_twoFifths_eqv_fourFifths mass))

private theorem fourFifthsFiniteGeometricSum_le_five (count : Nat) :
    listQSum
        (fun mass => (Q'.mkPos 4 5 (by decide)) ^ mass)
        (List.range count) ≤ Q'.ofNat 5 := by
  have hfinite : finSum
      (fun mass => (Q'.mkPos 4 5 (by decide)) ^ mass) count ≤
        Q'.ofNat 5 := by
    apply geom_series_le
      (fun mass => (Q'.mkPos 4 5 (by decide)) ^ mass)
      1 (Q'.mkPos 4 5 (by decide)) (Q'.ofNat 5)
    · decide
    · decide
    · rw [Q'.pow_zero]
      exact Q'.le_refl' 1
    · intro mass
      rw [Q'.pow_succ]
      exact Q'.le_refl' _
    · decide
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (listQSum_range_eqv_finSum_local
        (fun mass => (Q'.mkPos 4 5 (by decide)) ^ mass) count))
    hfinite

theorem finePacketConnectedRateTerminalSkeletonHistoryMassGeneratingFunction_le_five
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (code : FinePacketConnectedRateTerminalSkeletonNormalizationCode)
    (certificate :
      FinePacketConnectedRateTerminalSkeletonBinaryHistoryCertificate
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace code) :
    finePacketConnectedRateTerminalSkeletonHistoryMassGeneratingFunction
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace (Q'.mkPos 2 5 (by decide)) code ≤
      Q'.ofNat 5 := by
  let masses :=
    finePacketConnectedRateTerminalSkeletonHistoryMassCodes
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace code
  let ceiling := listNatMax masses + 1
  let sourceWeight : Nat → Q' := fun mass =>
    Q'.ofNat
        (finePacketConnectedRateTerminalSkeletonHistoryMassMultiplicity
          S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
            hobservableFace code mass) *
      (Q'.mkPos 2 5 (by decide)) ^ mass
  let targetWeight : Nat → Q' := fun mass =>
    (Q'.mkPos 4 5 (by decide)) ^ mass
  have hsubset : listQSum sourceWeight masses ≤
      listQSum targetWeight (List.range ceiling) := by
    apply YMGap.Continuum.FiniteWeightedCartesianInjection.listQSum_le_of_injective
      masses (List.range ceiling) sourceWeight targetWeight (fun mass => mass)
      (finePacketConnectedRateTerminalSkeletonHistoryMassCodes_nodup
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace code)
    · intro mass hmass
      apply List.mem_range.mpr
      have hle := le_listNatMax_of_mem hmass
      omega
    · intro left _ right _ heq
      exact heq
    · intro mass _hmass
      exact
        finePacketConnectedRateTerminalSkeletonHistoryMassTerm_le_fourFifths
          S hfineCutoff hcoarseCoupling rate hrate0 orientation
            observableFaceId hobservableFace code certificate mass
    · intro mass _hmass
      exact Q'.pow_nonneg _ (by decide) mass
  unfold finePacketConnectedRateTerminalSkeletonHistoryMassGeneratingFunction
  change listQSum sourceWeight masses ≤ Q'.ofNat 5
  exact Q'.le_trans' _ _ _ hsubset
    (fourFifthsFiniteGeometricSum_le_five ceiling)

theorem finePacketConnectedRateTerminalSkeletonHistoryPowerFugacity_le_five_of_binaryCertificate
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (code : FinePacketConnectedRateTerminalSkeletonNormalizationCode)
    (certificate :
      FinePacketConnectedRateTerminalSkeletonBinaryHistoryCertificate
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace code) :
    finePacketConnectedRateTerminalSkeletonHistoryPowerFugacity
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace (Q'.mkPos 2 5 (by decide)) code ≤
      Q'.ofNat 5 := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (finePacketConnectedRateTerminalSkeletonHistoryPowerFugacity_eqv_massGeneratingFunction
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace (Q'.mkPos 2 5 (by decide)) code))
    (finePacketConnectedRateTerminalSkeletonHistoryMassGeneratingFunction_le_five
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace code certificate)

#print axioms FinePacketConnectedRateTerminalSkeletonBinaryHistoryCertificate
#print axioms finePacketConnectedRateTerminalSkeletonHistoryMassMultiplicity_le_binary
#print axioms binaryMultiplicity_twoFifths_eqv_fourFifths
#print axioms finePacketConnectedRateTerminalSkeletonHistoryMassTerm_le_fourFifths
#print axioms finePacketConnectedRateTerminalSkeletonHistoryMassGeneratingFunction_le_five
#print axioms finePacketConnectedRateTerminalSkeletonHistoryPowerFugacity_le_five_of_binaryCertificate

end YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalSkeletonBinaryHistoryReduction
