/-
# One-attached original-residual consumer

The switched-component residual is not the correct carrier for parallel
one-attached children.  This module works on the original exceptional source
pair.  It identifies path-cleared right occurrences having exactly one
canonical-path neighbour, proves the exact source factorization through the
two original cleared residuals, and consumes right-only residual source
regions through the ordinary occurrence target.

The complete submask block remains available: under the one-attachment
exhaustion condition its cardinality is exactly `2^k`, where `k` is the
number of graph-theoretically identified residual children.
-/

import YMGap.Continuum.XiExceptionalParallelSubmaskCount
import YMGap.Continuum.XiExceptionalPathBitWeight
import YMGap.Continuum.XiExceptionalFullSourceBound

namespace YMGap.Continuum.XiExceptionalOneAttachedResidualConsumer

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiAvoidanceChainBound
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalPathMaskAlgebra
open YMGap.Continuum.XiExceptionalPathBitWeight
open YMGap.Continuum.XiExceptionalParallelExternalFamily
open YMGap.Continuum.XiExceptionalParallelResidualBlock
open YMGap.Continuum.XiExceptionalParallelSubmaskCount
open YMGap.Continuum.XiExceptionalPathSafeSummation
open YMGap.Continuum.XiExceptionalFullSourceBound

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The two original-source cleared residuals -/

def leftPathResidual
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OccBitVec Gamma.length :=
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  residualBits
    (pathOccurrenceBits Gamma.length path.indexWalk.vertices) pair.1

theorem leftPathResidual_at
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (i : Nat) (hi : i < Gamma.length) :
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
    (leftPathResidual Gamma qP b1 b2 entry).at i =
      ((!decide (i ∈ path.indexWalk.vertices)) && entry.1.1.at i) := by
  dsimp only
  unfold leftPathResidual
  rw [residualBits_at _ _ i hi]
  rw [pathOccurrenceBits_at Gamma.length _ i hi]

theorem exceptional_pathBits_original_exclusive
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    ∀ i, bitMask pathBits i = true →
      differentBits (bitMask pair.1 i) (bitMask pair.2 i) = true := by
  dsimp only
  intro i hpathBit
  have hi : i < Gamma.length := by
    cases hlt : decide (i < Gamma.length) with
    | true => exact of_decide_eq_true hlt
    | false =>
        have hnlt : ¬ i < Gamma.length := of_decide_eq_false hlt
        have hfalse := bitVec_at_false_of_ge
          (pathOccurrenceBits Gamma.length
            (sourceExceptionalPath Gamma qP b1 b2 entry.1
              (exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1
                entry.2)).indexWalk.vertices)
          i (by omega)
        change (pathOccurrenceBits Gamma.length _).at i = true at hpathBit
        rw [hfalse] at hpathBit
        cases hpathBit
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
  have hiPath : i ∈ path.indexWalk.vertices := by
    change (pathOccurrenceBits Gamma.length path.indexWalk.vertices).at i =
      true at hpathBit
    rw [pathOccurrenceBits_at Gamma.length path.indexWalk.vertices i hi]
      at hpathBit
    exact of_decide_eq_true hpathBit
  exact walk_vertices_different_of_seed Gamma.length (incAtDistinct Gamma)
    (bitMask entry.1.1) (bitMask entry.1.2) (predAt Gamma b2)
    path.indexWalk path.seed_true i hiPath

private theorem residual_maskWeight_eq
    (w : Q') (Gamma : List (Polymer L))
    (label : L.Plaquette → Rep)
    (path bits : OccBitVec Gamma.length) :
    maskWeight w Gamma label (bitMask (residualBits path bits)) =
      maskWeight w Gamma label
        (residualMask (bitMask path) (bitMask bits)) := by
  apply maskWeight_congr_on
  intro i hi
  change (residualBits path bits).at i =
    residualMask (bitMask path) (bitMask bits) i
  rw [residualBits_at path bits i hi]
  rfl

/-- Exact factorization of the original source pair into the canonical path
and the two path-cleared original residual families. -/
theorem occurrencePairWeight_eqv_original_path_residuals
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    occurrencePairWeight w qP b1 b2 Gamma label pair ≈
      path.polymerWalk.activityWeight w label *
        (familyActivity w
            (selectByBits Gamma
              (leftPathResidual Gamma qP b1 b2 entry)) label *
          familyActivity w
            (selectByBits Gamma
              (rightPathResidual Gamma qP b1 b2 entry)) label) := by
  dsimp only
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
  let leftResidual := leftPathResidual Gamma qP b1 b2 entry
  let rightResidual := rightPathResidual Gamma qP b1 b2 entry
  have hsourceEq := occurrencePairWeight_eq_source_activity_of_mem
    w qP b1 b2 Gamma label pair entry.2
  have hleftOriginal := maskWeight_eqv_familyActivity w Gamma label
    (bitMask pair.1)
  have hrightOriginal := maskWeight_eqv_familyActivity w Gamma label
    (bitMask pair.2)
  rw [maskFamily_toMask_eq_selectByBits] at hleftOriginal hrightOriginal
  have hsourceToOriginal :
      occurrencePairWeight w qP b1 b2 Gamma label pair ≈
        maskWeight w Gamma label (bitMask pair.1) *
          maskWeight w Gamma label (bitMask pair.2) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_of_eq hsourceEq)
      (mul_eqv_congr_both (Q'.eqv_symm hleftOriginal)
        (Q'.eqv_symm hrightOriginal))
  have hpartition := maskWeight_path_partition w Gamma label
    (bitMask pathBits) (bitMask pair.1) (bitMask pair.2)
    (exceptional_pathBits_original_exclusive Gamma qP b1 b2 entry)
  have hleftResidualEq := residual_maskWeight_eq w Gamma label
    pathBits pair.1
  have hrightResidualEq := residual_maskWeight_eq w Gamma label
    pathBits pair.2
  change maskWeight w Gamma label (bitMask leftResidual) =
      maskWeight w Gamma label
        (residualMask (bitMask pathBits) (bitMask pair.1))
      at hleftResidualEq
  change maskWeight w Gamma label (bitMask rightResidual) =
      maskWeight w Gamma label
        (residualMask (bitMask pathBits) (bitMask pair.2))
      at hrightResidualEq
  rw [← hleftResidualEq, ← hrightResidualEq] at hpartition
  have hpath := pathOccurrenceMaskWeight_eqv_walk w Gamma label path
  have hleftResidual := maskWeight_eqv_familyActivity w Gamma label
    (bitMask leftResidual)
  have hrightResidual := maskWeight_eqv_familyActivity w Gamma label
    (bitMask rightResidual)
  rw [maskFamily_toMask_eq_selectByBits] at hleftResidual hrightResidual
  exact Q'.eqv_trans _ _ _ hsourceToOriginal
    (Q'.eqv_trans _ _ _ hpartition
      (mul_eqv_congr_both hpath
        (mul_eqv_congr_both hleftResidual hrightResidual)))

/-! ## 2. Graph-theoretic one-attachment identification -/

/-- Occurrence indices on the canonical path adjacent to occurrence `i`. -/
def pathNeighborBits
    (Gamma : List (Polymer L)) (vertices : List Nat) (i : Nat) :
    OccBitVec Gamma.length :=
  bitsFromMask Gamma.length
    (fun j => decide (j ∈ vertices) && incAtDistinct Gamma i j) 0

theorem pathNeighborBits_at
    (Gamma : List (Polymer L)) (vertices : List Nat)
    (i j : Nat) (hj : j < Gamma.length) :
    (pathNeighborBits Gamma vertices i).at j =
      (decide (j ∈ vertices) && incAtDistinct Gamma i j) := by
  unfold pathNeighborBits
  simpa using bitsFromMask_at Gamma.length
    (fun k => decide (k ∈ vertices) && incAtDistinct Gamma i k) 0 j hj

/-- The right cleared occurrences having exactly one conflict edge back to
the canonical path.  Since they lie on one admissible source side, distinct
selected children are mutually compatible. -/
def oneAttachedRightChildren
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OccBitVec Gamma.length :=
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
  bitsFromMask Gamma.length (fun i =>
    (rightPathResidual Gamma qP b1 b2 entry).at i &&
      decide (occurrenceBitCount
        (pathNeighborBits Gamma path.indexWalk.vertices i) = 1)) 0

theorem oneAttachedRightChildren_at
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (i : Nat) (hi : i < Gamma.length) :
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
    (oneAttachedRightChildren Gamma qP b1 b2 entry).at i =
      ((rightPathResidual Gamma qP b1 b2 entry).at i &&
        decide (occurrenceBitCount
          (pathNeighborBits Gamma path.indexWalk.vertices i) = 1)) := by
  dsimp only
  unfold oneAttachedRightChildren
  simpa using bitsFromMask_at Gamma.length _ 0 i hi

structure OneAttachedRightResidualFacts
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Prop where
  one_attachment :
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
    ∀ i, i < Gamma.length →
      (rightPathResidual Gamma qP b1 b2 entry).at i = true →
      occurrenceBitCount
        (pathNeighborBits Gamma path.indexWalk.vertices i) = 1

/-- Under the one-attachment exhaustion hypothesis, the graph-selected child
mask is exactly the already-cleared residual mask. -/
theorem oneAttachedRightChildren_eq_rightPathResidual
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hattach : OneAttachedRightResidualFacts Gamma qP b1 b2 entry) :
    oneAttachedRightChildren Gamma qP b1 b2 entry =
      rightPathResidual Gamma qP b1 b2 entry := by
  apply BitVec.ext
  intro i
  cases hlt : decide (i < Gamma.length) with
  | true =>
      have hi : i < Gamma.length := of_decide_eq_true hlt
      rw [oneAttachedRightChildren_at Gamma qP b1 b2 entry i hi]
      cases hres : (rightPathResidual Gamma qP b1 b2 entry).at i with
      | false => rfl
      | true =>
          rw [hattach.one_attachment i hi hres]
          rfl
  | false =>
      have hnlt : ¬ i < Gamma.length := of_decide_eq_false hlt
      rw [bitVec_at_false_of_ge
        (oneAttachedRightChildren Gamma qP b1 b2 entry) i (by omega)]
      rw [bitVec_at_false_of_ge
        (rightPathResidual Gamma qP b1 b2 entry) i (by omega)]

/-- The graph-selected child family is compatible because it is a submask of
the original admissible right source side. -/
theorem oneAttachedRightChildren_compatible
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    familyCompatibleB
      (selectByBits Gamma
        (oneAttachedRightChildren Gamma qP b1 b2 entry)) = true := by
  apply YMGap.Continuum.XiExceptionalParallelSourceSide.exceptional_right_submask_compatible
  intro i hchild
  cases hlt : decide (i < Gamma.length) with
  | true =>
      have hi : i < Gamma.length := of_decide_eq_true hlt
      rw [oneAttachedRightChildren_at Gamma qP b1 b2 entry i hi] at hchild
      have hres := ((Bool.and_eq_true _ _).mp hchild).1
      exact rightPathResidual_submask_right Gamma qP b1 b2 entry i hres
  | false =>
      have hnlt : ¬ i < Gamma.length := of_decide_eq_false hlt
      have hout := bitVec_at_false_of_ge
        (oneAttachedRightChildren Gamma qP b1 b2 entry) i (by omega)
      rw [hchild] at hout
      cases hout

/-- The already constructed multicode block has exact `2^k` size, now with
`k` identified as the number of one-attached residual children. -/
theorem rightResidualParallelCodes_length_of_oneAttached
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hattach : OneAttachedRightResidualFacts Gamma qP b1 b2 entry) :
    (rightResidualParallelCodes Gamma qP b1 b2 entry).length =
      2 ^ occurrenceBitCount
        (oneAttachedRightChildren Gamma qP b1 b2 entry) := by
  rw [rightResidualParallelCodes_length]
  rw [oneAttachedRightChildren_eq_rightPathResidual Gamma qP b1 b2 entry
    hattach]

/-! ## 3. Exact right-only residual allocation -/

theorem rightPathResidual_mem_external_masks
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    rightPathResidual Gamma qP b1 b2 entry ∈
      rightResidualExternalMasks Gamma qP b1 b2 entry := by
  apply (mem_rightResidualExternalMasks_iff Gamma qP b1 b2 entry _).mpr
  intro _ h
  exact h

/-- If the left cleared residual is empty, the maximal right residual code
has exactly the original exceptional source weight. -/
theorem rightOnlyResidualCode_weight_eqv_source
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hleftEmpty : selectByBits Gamma
      (leftPathResidual Gamma qP b1 b2 entry) = []) :
    occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
        (parallelExternalCarrierCode Gamma qP b1 b2 entry
          (rightPathResidual Gamma qP b1 b2 entry)) ≈
      occurrencePairWeight w qP b1 b2 Gamma label entry.1 := by
  have hcode := rightResidualParallelCode_weight_eqv
    w qP b1 b2 Gamma label entry
    (rightPathResidual Gamma qP b1 b2 entry)
    (rightPathResidual_mem_external_masks Gamma qP b1 b2 entry)
  have hsource := occurrencePairWeight_eqv_original_path_residuals
    w qP b1 b2 Gamma label entry
  dsimp only at hcode hsource
  rw [hleftEmpty] at hsource
  simp only [familyActivity_nil] at hsource
  have hsourceReduced := Q'.eqv_trans _ _ _ hsource
    (Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv _))
  exact Q'.eqv_trans _ _ _ hcode (Q'.eqv_symm hsourceReduced)

/-- A duplicate-free right-only residual source region injects into the
ordinary occurrence target via its maximal cleared residual mask. -/
theorem rightOnlyResidual_region_global_bound
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (source : List (ExceptionalSourceEntry Gamma qP b1 b2))
    (hsource : source.Nodup)
    (hleftEmpty : ∀ entry, entry ∈ source →
      selectByBits Gamma (leftPathResidual Gamma qP b1 b2 entry) = [])
    (hresidualInjective : ∀ a, a ∈ source → ∀ b, b ∈ source →
      rightPathResidual Gamma qP b1 b2 a =
        rightPathResidual Gamma qP b1 b2 b → a = b) :
    qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
        entry.1) source ≤
      qListSum (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
        (occurrenceCarrierXiCodes Gamma) := by
  apply parallelExternal_global_bound w hw qP b1 b2 Gamma label
    (fun entry => entry)
    (fun entry => rightPathResidual Gamma qP b1 b2 entry)
    source
    (fun entry => occurrencePairWeight w qP b1 b2 Gamma label entry.1)
    hsource hresidualInjective
  intro entry hentry
  exact Q'.le_of_eqv (Q'.eqv_symm
    (rightOnlyResidualCode_weight_eqv_source w qP b1 b2 Gamma label
      entry (hleftEmpty entry hentry)))

/-- Full exceptional-source closure for a one-attached/right-only residual
region.  This is the ordinary chain-times-`XiR` consumer used by the
one-ended bound. -/
theorem full_exceptional_source_le_chain_mul_XiR_of_rightOnlyResidual
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (hleftEmpty : ∀ entry,
      entry ∈ fullExceptionalSource Gamma qP b1 b2 →
      selectByBits Gamma (leftPathResidual Gamma qP b1 b2 entry) = [])
    (hresidualInjective : ∀ a,
      a ∈ fullExceptionalSource Gamma qP b1 b2 → ∀ b,
      b ∈ fullExceptionalSource Gamma qP b1 b2 →
      rightPathResidual Gamma qP b1 b2 a =
        rightPathResidual Gamma qP b1 b2 b → a = b) :
    qListSum (occurrencePairWeight w qP b1 b2 Gamma label)
        (exceptionalSourceCodes Gamma qP b1 b2) ≤
      connectingChainMajorant w qP b1 b2 Gamma label *
        XiR w qP Gamma label := by
  have hglobal := rightOnlyResidual_region_global_bound hw Gamma qP b1 b2
    label (fullExceptionalSource Gamma qP b1 b2)
    (fullExceptionalSource_nodup Gamma qP b1 b2)
    hleftEmpty hresidualInjective
  change qListSum (pathSafeSourceWeight w qP b1 b2 Gamma label)
      (fullExceptionalSource Gamma qP b1 b2) ≤ _ at hglobal
  rw [fullExceptionalSource_weight_eq] at hglobal
  exact Q'.le_trans' _ _ _ hglobal
    (Q'.le_of_eqv
      (occurrenceCarrierXiCodes_sum_eqv_carrier_mul_XiR
        w qP b1 b2 Gamma label))

#print axioms leftPathResidual_at
#print axioms exceptional_pathBits_original_exclusive
#print axioms occurrencePairWeight_eqv_original_path_residuals
#print axioms pathNeighborBits_at
#print axioms oneAttachedRightChildren_at
#print axioms oneAttachedRightChildren_eq_rightPathResidual
#print axioms oneAttachedRightChildren_compatible
#print axioms rightResidualParallelCodes_length_of_oneAttached
#print axioms rightPathResidual_mem_external_masks
#print axioms rightOnlyResidualCode_weight_eqv_source
#print axioms rightOnlyResidual_region_global_bound
#print axioms full_exceptional_source_le_chain_mul_XiR_of_rightOnlyResidual

end YMGap.Continuum.XiExceptionalOneAttachedResidualConsumer
