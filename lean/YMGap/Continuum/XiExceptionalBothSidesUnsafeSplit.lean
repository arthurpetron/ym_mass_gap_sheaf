/-
# Exact split leaving only both-sides-path-unsafe sources

Finite Boolean checks decide whether each original residual side is compatible
with the canonical path.  The branch code uses the canonical payload
orientation when left is safe and the symmetric orientation otherwise.  On
the covered filter, right is then safe.  Cross-orientation disjointness makes
this one injective exact-weight allocation.  A filter partition leaves exactly
the sources with explicit unsafe witnesses on both original residual sides.
-/

import YMGap.Continuum.XiExceptionalTwoSidedOrientationDisjoint

namespace YMGap.Continuum.XiExceptionalBothSidesUnsafeSplit

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalFiberwiseInjection
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalTargetBlocks
open YMGap.Continuum.XiExceptionalParallelResidualBlock
open YMGap.Continuum.XiExceptionalOneAttachedResidualConsumer
open YMGap.Continuum.XiExceptionalUnsafeSideExclusion
open YMGap.Continuum.XiExceptionalFullSourceBound
open YMGap.Continuum.XiExceptionalTwoSidedOriginalCarrier
open YMGap.Continuum.XiExceptionalSymmetricTwoSidedCarrier
open YMGap.Continuum.XiExceptionalTwoSidedOrientationDisjoint

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

private theorem occurrenceIndices_sound : ∀ {n i : Nat},
    i ∈ occurrenceIndices n → i < n
  | 0, _, hi => by cases hi
  | n + 1, 0, _ => by omega
  | n + 1, i + 1, hi => by
      have ht : i ∈ occurrenceIndices n := by
        rcases List.mem_cons.mp hi with hzero | htail
        · cases hzero
        · obtain ⟨j, hj, hji⟩ := List.mem_map.mp htail
          injection hji with h
          subst j
          exact hj
      have := occurrenceIndices_sound ht
      omega

private theorem exists_false_of_all_false (f : a → Bool) :
    ∀ xs : List a, xs.all f = false → ∃ x, x ∈ xs ∧ f x = false
  | [], h => by cases h
  | x :: xs, h => by
      cases hx : f x with
      | false => exact ⟨x, List.mem_cons_self, hx⟩
      | true =>
          have ht : xs.all f = false := by
            simp only [List.all_cons, hx, Bool.true_and] at h
            exact h
          obtain ⟨y, hy, hfy⟩ := exists_false_of_all_false f xs ht
          exact ⟨y, List.mem_cons_of_mem x hy, hfy⟩

def leftResidualPathSafeB
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Bool :=
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
  (occurrenceIndices Gamma.length).all (fun i =>
    !(leftPathResidual Gamma qP b1 b2 entry).at i ||
      pathSafe Gamma path.indexWalk.vertices i)

def rightResidualPathSafeB
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Bool :=
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
  (occurrenceIndices Gamma.length).all (fun i =>
    !(rightPathResidual Gamma qP b1 b2 entry).at i ||
      pathSafe Gamma path.indexWalk.vertices i)

private theorem residualSafeB_pointwise
    (Gamma : List (Polymer L)) (vertices : List Nat)
    (residual : OccBitVec Gamma.length)
    (hcheck : (occurrenceIndices Gamma.length).all (fun i =>
      !residual.at i || pathSafe Gamma vertices i) = true) :
    ∀ i, i < Gamma.length → residual.at i = true →
      pathSafe Gamma vertices i = true := by
  intro i hi hres
  have hall := List.all_eq_true.mp hcheck i (occurrenceIndices_complete hi)
  cases hs : pathSafe Gamma vertices i <;> simp_all

private theorem residualSafeB_backgroundPath
    (Gamma : List (Polymer L)) (vertices : List Nat)
    (residual : OccBitVec Gamma.length)
    (hcheck : (occurrenceIndices Gamma.length).all (fun i =>
      !residual.at i || pathSafe Gamma vertices i) = true)
    (hoff : ∀ i, i < Gamma.length → residual.at i = true →
      i ∉ vertices) :
    ∀ X, X ∈ (vertices.map (polyAt Gamma)) →
      ∀ T, T ∈ selectByBits Gamma residual →
        compatibleB X T = true := by
  intro X hX T hT
  obtain ⟨j, hj, hjX⟩ := List.mem_map.mp hX
  have hTmask : T ∈ maskFamily Gamma (bitMask residual) := by
    rw [maskFamily_toMask_eq_selectByBits]
    exact hT
  obtain ⟨i, hi, hres, hiT⟩ :=
    mem_maskFamily_occurrence Gamma (bitMask residual) hTmask
  have hsafe := residualSafeB_pointwise Gamma vertices residual hcheck
    i hi hres
  unfold pathSafe at hsafe
  have hnotConflict := List.all_eq_true.mp hsafe j hj
  have hconflict : symConflict (incAtDistinct Gamma) j i = false :=
    eq_false_of_not_true hnotConflict
  have hji : j ≠ i := by
    intro h
    subst j
    exact (hoff i hi hres) hj
  rw [← hjX, ← hiT]
  exact compatibleB_of_incAtDistinct_symConflict_false Gamma hji hconflict

theorem leftResidualPathSafeB_true
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hsafe : leftResidualPathSafeB Gamma qP b1 b2 entry = true) :
    OriginalLeftResidualPathSafe Gamma qP b1 b2 entry := by
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
  have hcheck : (occurrenceIndices Gamma.length).all (fun i =>
      !(leftPathResidual Gamma qP b1 b2 entry).at i ||
        pathSafe Gamma path.indexWalk.vertices i) = true := by
    simpa [leftResidualPathSafeB, facts, path] using hsafe
  intro X hX T hT
  rw [path.polymer_vertices] at hX
  exact residualSafeB_backgroundPath Gamma path.indexWalk.vertices
    (leftPathResidual Gamma qP b1 b2 entry) hcheck (by
      intro i hi hres himem
      rw [leftPathResidual_at Gamma qP b1 b2 entry i hi] at hres
      have hparts := (Bool.and_eq_true _ _).mp hres
      have hnot : ¬ i ∈
          (sourceExceptionalPath Gamma qP b1 b2 entry.1
            (exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1
              entry.2)).indexWalk.vertices := by
        simpa using hparts.1
      exact hnot (by simpa [path, facts] using himem)) X hX T hT

theorem rightResidualPathSafeB_true
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hsafe : rightResidualPathSafeB Gamma qP b1 b2 entry = true) :
    OriginalRightResidualPathSafe Gamma qP b1 b2 entry := by
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
  have hcheck : (occurrenceIndices Gamma.length).all (fun i =>
      !(rightPathResidual Gamma qP b1 b2 entry).at i ||
        pathSafe Gamma path.indexWalk.vertices i) = true := by
    simpa [rightResidualPathSafeB, facts, path] using hsafe
  intro X hX T hT
  rw [path.polymer_vertices] at hX
  exact residualSafeB_backgroundPath Gamma path.indexWalk.vertices
    (rightPathResidual Gamma qP b1 b2 entry) hcheck (by
      intro i hi hres himem
      rw [rightPathResidual_at Gamma qP b1 b2 entry i hi] at hres
      have hparts := (Bool.and_eq_true _ _).mp hres
      have hnot : ¬ i ∈
          (sourceExceptionalPath Gamma qP b1 b2 entry.1
            (exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1
              entry.2)).indexWalk.vertices := by
        simpa using hparts.1
      exact hnot (by simpa [path, facts] using himem)) X hX T hT

private theorem residualSafeB_false_witness
    (Gamma : List (Polymer L)) (vertices : List Nat)
    (residual : OccBitVec Gamma.length)
    (hcheck : (occurrenceIndices Gamma.length).all (fun i =>
      !residual.at i || pathSafe Gamma vertices i) = false) :
    ∃ i, i < Gamma.length ∧ residual.at i = true ∧
      pathSafe Gamma vertices i = false := by
  obtain ⟨i, himem, hfalse⟩ := exists_false_of_all_false
    (fun i => !residual.at i || pathSafe Gamma vertices i)
    (occurrenceIndices Gamma.length) hcheck
  have hi := occurrenceIndices_sound himem
  refine ⟨i, hi, ?_, ?_⟩
  · cases hr : residual.at i <;> cases hs : pathSafe Gamma vertices i <;>
      simp_all
  · cases hr : residual.at i <;> cases hs : pathSafe Gamma vertices i <;>
      simp_all

theorem leftResidualPathSafeB_false
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hunsafe : leftResidualPathSafeB Gamma qP b1 b2 entry = false) :
    OriginalLeftResidualPathUnsafe Gamma qP b1 b2 entry := by
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
  have hcheck : (occurrenceIndices Gamma.length).all (fun i =>
      !(leftPathResidual Gamma qP b1 b2 entry).at i ||
        pathSafe Gamma path.indexWalk.vertices i) = false := by
    simpa only [leftResidualPathSafeB] using hunsafe
  exact residualSafeB_false_witness Gamma path.indexWalk.vertices
    (leftPathResidual Gamma qP b1 b2 entry) hcheck

def OriginalRightResidualPathUnsafe
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Prop :=
  ∃ i, i < Gamma.length ∧
    (rightPathResidual Gamma qP b1 b2 entry).at i = true ∧
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
    pathSafe Gamma path.indexWalk.vertices i = false

theorem rightResidualPathSafeB_false
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hunsafe : rightResidualPathSafeB Gamma qP b1 b2 entry = false) :
    OriginalRightResidualPathUnsafe Gamma qP b1 b2 entry := by
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
  have hcheck : (occurrenceIndices Gamma.length).all (fun i =>
      !(rightPathResidual Gamma qP b1 b2 entry).at i ||
        pathSafe Gamma path.indexWalk.vertices i) = false := by
    simpa only [rightResidualPathSafeB] using hunsafe
  exact residualSafeB_false_witness Gamma path.indexWalk.vertices
    (rightPathResidual Gamma qP b1 b2 entry) hcheck

/-! ## Computable branch allocation and exact remaining source -/

def twoSidedCoveredB
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Bool :=
  leftResidualPathSafeB Gamma qP b1 b2 entry ||
    rightResidualPathSafeB Gamma qP b1 b2 entry

def twoSidedCoveredSource
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :=
  (fullExceptionalSource Gamma qP b1 b2).filter
    (twoSidedCoveredB Gamma qP b1 b2)

def bothSidesPathUnsafeSource
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) :=
  (fullExceptionalSource Gamma qP b1 b2).filter
    (fun entry => !(twoSidedCoveredB Gamma qP b1 b2 entry))

def twoSidedBranchCode
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OccCarrierXiCodeAt Gamma :=
  if leftResidualPathSafeB Gamma qP b1 b2 entry then
    originalTwoSidedCarrierCode Gamma qP b1 b2 entry
  else originalSymmetricTwoSidedCarrierCode Gamma qP b1 b2 entry

theorem twoSidedBranchCode_mem
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    twoSidedBranchCode Gamma qP b1 b2 entry ∈
      occurrenceCarrierXiCodes Gamma := by
  unfold twoSidedBranchCode
  split
  · exact originalTwoSidedCarrierCode_mem Gamma qP b1 b2 entry
  · exact originalSymmetricTwoSidedCarrierCode_mem Gamma qP b1 b2 entry

theorem twoSidedBranchCode_weight_eqv_source
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hcovered : entry ∈ twoSidedCoveredSource Gamma qP b1 b2) :
    occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
        (twoSidedBranchCode Gamma qP b1 b2 entry) ≈
      occurrencePairWeight w qP b1 b2 Gamma label entry.1 := by
  have hcover := (List.mem_filter.mp hcovered).2
  unfold twoSidedCoveredB at hcover
  cases hleft : leftResidualPathSafeB Gamma qP b1 b2 entry with
  | true =>
      rw [show twoSidedBranchCode Gamma qP b1 b2 entry =
          originalTwoSidedCarrierCode Gamma qP b1 b2 entry by
        simp [twoSidedBranchCode, hleft]]
      exact originalTwoSidedCarrierCode_weight_eqv_source
        w qP b1 b2 Gamma label entry
        (leftResidualPathSafeB_true Gamma qP b1 b2 entry hleft)
  | false =>
      have hright : rightResidualPathSafeB Gamma qP b1 b2 entry = true := by
        simpa [hleft] using hcover
      rw [show twoSidedBranchCode Gamma qP b1 b2 entry =
          originalSymmetricTwoSidedCarrierCode Gamma qP b1 b2 entry by
        simp [twoSidedBranchCode, hleft]]
      exact originalSymmetricTwoSidedCarrierCode_weight_eqv_source
        w qP b1 b2 Gamma label entry
        (rightResidualPathSafeB_true Gamma qP b1 b2 entry hright)

theorem twoSidedBranchCode_injective_on_covered
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (a b : ExceptionalSourceEntry Gamma qP b1 b2)
    (ha : a ∈ twoSidedCoveredSource Gamma qP b1 b2)
    (hb : b ∈ twoSidedCoveredSource Gamma qP b1 b2)
    (hcode : twoSidedBranchCode Gamma qP b1 b2 a =
      twoSidedBranchCode Gamma qP b1 b2 b) : a = b := by
  unfold twoSidedBranchCode at hcode
  cases hleftA : leftResidualPathSafeB Gamma qP b1 b2 a <;>
    cases hleftB : leftResidualPathSafeB Gamma qP b1 b2 b <;>
    simp only [hleftA, hleftB, if_true, if_false] at hcode
  · exact originalSymmetricTwoSidedCarrierCode_injective
      Gamma qP b1 b2 a b hcode
  · exact False.elim ((original_twoSided_cross_orientation_ne
      Gamma qP b1 b2 b a
      (leftResidualPathSafeB_false Gamma qP b1 b2 a hleftA)) hcode.symm)
  · exact False.elim ((original_twoSided_cross_orientation_ne
      Gamma qP b1 b2 a b
      (leftResidualPathSafeB_false Gamma qP b1 b2 b hleftB)) hcode)
  · exact originalTwoSidedCarrierCode_injective
      Gamma qP b1 b2 a b hcode

theorem twoSidedCoveredSource_global_bound
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) :
    qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
        entry.1) (twoSidedCoveredSource Gamma qP b1 b2) ≤
      qListSum (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
        (occurrenceCarrierXiCodes Gamma) := by
  let source := twoSidedCoveredSource Gamma qP b1 b2
  apply qListSum_le_of_disjoint_blocks source
    (occurrenceCarrierXiCodes Gamma)
    (fun entry => occurrencePairWeight w qP b1 b2 Gamma label entry.1)
    (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
    (fun entry => [twoSidedBranchCode Gamma qP b1 b2 entry])
  · rw [show source.flatMap (fun entry =>
        [twoSidedBranchCode Gamma qP b1 b2 entry]) =
      source.map (twoSidedBranchCode Gamma qP b1 b2) by
        induction source with
        | nil => rfl
        | cons x xs ih =>
            simp only [List.flatMap_cons, List.map_cons,
              List.singleton_append]
            rw [ih]]
    apply nodup_map_of_injOn _ source
      (nodup_filter_bool _ _ (fullExceptionalSource_nodup Gamma qP b1 b2))
    intro a ha b hb hcode
    exact twoSidedBranchCode_injective_on_covered Gamma qP b1 b2
      a b ha hb hcode
  · intro code hmem
    obtain ⟨entry, _, hsingleton⟩ := List.mem_flatMap.mp hmem
    rw [List.mem_singleton] at hsingleton
    subst code
    exact twoSidedBranchCode_mem Gamma qP b1 b2 entry
  · intro entry hentry
    simp only [qListSum_cons, qListSum_nil, Q'.add_zero']
    exact Q'.ge_of_eqv (twoSidedBranchCode_weight_eqv_source
      w Gamma qP b1 b2 label entry hentry)
  · intro code _
    exact occurrenceCarrierXiCodeWeight_nonnegative hw
      qP b1 b2 Gamma label code

theorem exceptionalSource_twoSided_unsafe_partition
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) (label : L.Plaquette → Rep) :
    qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
        entry.1) (fullExceptionalSource Gamma qP b1 b2) ≈
      qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
          entry.1) (twoSidedCoveredSource Gamma qP b1 b2) +
        qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
          entry.1) (bothSidesPathUnsafeSource Gamma qP b1 b2) := by
  exact qListSum_filter_partition
    (fun entry => occurrencePairWeight w qP b1 b2 Gamma label entry.1)
    (twoSidedCoveredB Gamma qP b1 b2)
    (fullExceptionalSource Gamma qP b1 b2)

theorem bothSidesPathUnsafeSource_witnesses
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hentry : entry ∈ bothSidesPathUnsafeSource Gamma qP b1 b2) :
    OriginalLeftResidualPathUnsafe Gamma qP b1 b2 entry ∧
      OriginalRightResidualPathUnsafe Gamma qP b1 b2 entry := by
  have hnot := (List.mem_filter.mp hentry).2
  unfold twoSidedCoveredB at hnot
  cases hl : leftResidualPathSafeB Gamma qP b1 b2 entry <;>
    cases hr : rightResidualPathSafeB Gamma qP b1 b2 entry <;>
    simp [hl, hr] at hnot
  exact ⟨leftResidualPathSafeB_false Gamma qP b1 b2 entry hl,
    rightResidualPathSafeB_false Gamma qP b1 b2 entry hr⟩

#print axioms leftResidualPathSafeB_true
#print axioms rightResidualPathSafeB_true
#print axioms leftResidualPathSafeB_false
#print axioms rightResidualPathSafeB_false
#print axioms twoSidedBranchCode_weight_eqv_source
#print axioms twoSidedBranchCode_injective_on_covered
#print axioms twoSidedCoveredSource_global_bound
#print axioms exceptionalSource_twoSided_unsafe_partition
#print axioms bothSidesPathUnsafeSource_witnesses

end YMGap.Continuum.XiExceptionalBothSidesUnsafeSplit
