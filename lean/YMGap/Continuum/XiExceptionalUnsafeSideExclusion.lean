/-
# Source-admissible exclusion of the unsafe router collision

For a decoded exceptional path, call an ambient occurrence safe when its
polymer has no conflict with any path occurrence.  If it is unsafe, a
conflicting path vertex exists.  The path vertex is occupied on exactly one
switched side.  Same-side compatibility then forbids an unsafe residual bit
on that side.

Consequently two exceptional entries with the same decoded path cannot
realize the left-versus-right collision of the fixed-path router.  This is a
source theorem, not a cardinality assumption: the raw Boolean collision is
real, but its two endpoints cannot both be admissible exceptional sources.
-/

import YMGap.Continuum.XiExceptionalSwitchedCompatibility

namespace YMGap.Continuum.XiExceptionalUnsafeSideExclusion

open YMGap.Continuum.PolymerModel
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalPathMaskAlgebra
open YMGap.Continuum.XiExceptionalRoutedExactWeight
open YMGap.Continuum.XiExceptionalPathSideDecoder
open YMGap.Continuum.XiExceptionalSwitchedCompatibility

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

def pathSafe (Gamma : List (Polymer L)) (vertices : List Nat)
    (i : Nat) : Bool :=
  vertices.all (fun j => !(symConflict (incAtDistinct Gamma) j i))

private theorem exists_false_of_all_false (f : a → Bool) :
    ∀ xs : List a, xs.all f = false → ∃ x, x ∈ xs ∧ f x = false
  | [], h => by cases h
  | x :: xs, h => by
      cases hx : f x with
      | false => exact ⟨x, List.mem_cons_self, hx⟩
      | true =>
          have htail : xs.all f = false := by
            simp only [List.all_cons, hx, Bool.true_and] at h
            exact h
          obtain ⟨y, hy, hfy⟩ := exists_false_of_all_false f xs htail
          exact ⟨y, List.mem_cons_of_mem x hy, hfy⟩

private theorem switchedCode_at_left
    (Gamma : List (Polymer L)) (b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length) (i : Nat) (hi : i < Gamma.length) :
    (switchedBranchCode Gamma b2 pair).1.at i =
      switchedLeft Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i := by
  unfold switchedBranchCode
  simpa using bitsFromMask_at Gamma.length _ 0 i hi

private theorem switchedCode_at_right
    (Gamma : List (Polymer L)) (b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length) (i : Nat) (hi : i < Gamma.length) :
    (switchedBranchCode Gamma b2 pair).2.at i =
      switchedRight Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i := by
  unfold switchedBranchCode
  simpa using bitsFromMask_at Gamma.length _ 0 i hi

private theorem first_side_of_walk
    {edge : Nat → Nat → Bool} {i j : Nat}
    (walk : CWalk edge i j) (left right : Nat → Bool)
    (hfirst : left i = true ∧ right i = false) :
    match walk.vertices with
    | [] => False
    | k :: _ => left k = true ∧ right k = false := by
  cases walk <;> exact hfirst

private theorem exceptional_first_side
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let left := switchedLeft Gamma.length (incAtDistinct Gamma)
      (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2)
    let right := switchedRight Gamma.length (incAtDistinct Gamma)
      (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2)
    match path.indexWalk.vertices with
    | [] => False
    | i :: _ => left i = true ∧ right i = false := by
  dsimp only
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  have hs := exceptional_switched_path_start_left Gamma qP b1 b2 entry
  exact first_side_of_walk path.indexWalk _ _ hs

private theorem path_vertex_lt
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    ∀ i, i ∈ path.indexWalk.vertices → i < Gamma.length := by
  dsimp only
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  have hseed := (forwardSeed_parts Gamma.length
    (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2)
    path.seed_true).1
  exact walk_vertices_lt_of_seed Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) path.indexWalk hseed

/-- The raw left/right unsafe collision is unreachable by two admissible
exceptional entries once their carrier chains decode to the same path. -/
theorem exceptional_unsafe_cross_side_impossible
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry1 entry2 : ExceptionalSourceEntry Gamma qP b1 b2)
    (hvertices :
      let pair1 := entry1.1
      let pair2 := entry2.1
      let facts1 := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair1 entry1.2
      let facts2 := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair2 entry2.2
      let path1 := sourceExceptionalPath Gamma qP b1 b2 pair1 facts1
      let path2 := sourceExceptionalPath Gamma qP b1 b2 pair2 facts2
      path1.indexWalk.vertices = path2.indexWalk.vertices)
    (i : Nat) (hi : i < Gamma.length)
    (hunsafe :
      let pair1 := entry1.1
      let facts1 := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair1 entry1.2
      let path1 := sourceExceptionalPath Gamma qP b1 b2 pair1 facts1
      pathSafe Gamma path1.indexWalk.vertices i = false)
    (hleft1 :
      let pair1 := entry1.1
      let facts1 := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair1 entry1.2
      let path1 := sourceExceptionalPath Gamma qP b1 b2 pair1 facts1
      let pathBits1 := pathOccurrenceBits Gamma.length path1.indexWalk.vertices
      let switched1 := switchedBranchCode Gamma b2 pair1
      (residualBits pathBits1 switched1.1).at i = true)
    (hright2 :
      let pair2 := entry2.1
      let facts2 := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair2 entry2.2
      let path2 := sourceExceptionalPath Gamma qP b1 b2 pair2 facts2
      let pathBits2 := pathOccurrenceBits Gamma.length path2.indexWalk.vertices
      let switched2 := switchedBranchCode Gamma b2 pair2
      (residualBits pathBits2 switched2.2).at i = true) : False := by
  let pair1 := entry1.1
  let pair2 := entry2.1
  let facts1 := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair1 entry1.2
  let facts2 := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair2 entry2.2
  let path1 := sourceExceptionalPath Gamma qP b1 b2 pair1 facts1
  let path2 := sourceExceptionalPath Gamma qP b1 b2 pair2 facts2
  let pathBits1 := pathOccurrenceBits Gamma.length path1.indexWalk.vertices
  let pathBits2 := pathOccurrenceBits Gamma.length path2.indexWalk.vertices
  let switched1 := switchedBranchCode Gamma b2 pair1
  let switched2 := switchedBranchCode Gamma b2 pair2
  dsimp only at hvertices hunsafe hleft1 hright2
  unfold pathSafe at hunsafe
  obtain ⟨j, hjPath1, hjFalse⟩ := exists_false_of_all_false
    (fun j => !(symConflict (incAtDistinct Gamma) j i))
    path1.indexWalk.vertices hunsafe
  have hconf : symConflict (incAtDistinct Gamma) j i = true := by
    cases h : symConflict (incAtDistinct Gamma) j i with
    | true => rfl
    | false => simp [h] at hjFalse
  have hjPath2 : j ∈ path2.indexWalk.vertices := by
    rw [← hvertices]
    exact hjPath1
  have hjN1 : j < Gamma.length := path_vertex_lt Gamma qP b1 b2 entry1 j hjPath1
  have hjN2 : j < Gamma.length := path_vertex_lt Gamma qP b1 b2 entry2 j hjPath2
  have hleft1At : switched1.1.at i = true := by
    rw [residualBits_at pathBits1 switched1.1 i hi] at hleft1
    cases hp : pathBits1.at i <;> simp_all
  have hright2At : switched2.2.at i = true := by
    rw [residualBits_at pathBits2 switched2.2 i hi] at hright2
    cases hp : pathBits2.at i <;> simp_all
  have hleft1F : switchedLeft Gamma.length (incAtDistinct Gamma)
      (bitMask pair1.1) (bitMask pair1.2) (predAt Gamma b2) i = true := by
    rw [← switchedCode_at_left Gamma b2 pair1 i hi]
    exact hleft1At
  have hright2F : switchedRight Gamma.length (incAtDistinct Gamma)
      (bitMask pair2.1) (bitMask pair2.2) (predAt Gamma b2) i = true := by
    rw [← switchedCode_at_right Gamma b2 pair2 i hi]
    exact hright2At
  let leftF1 := switchedLeft Gamma.length (incAtDistinct Gamma)
    (bitMask pair1.1) (bitMask pair1.2) (predAt Gamma b2)
  let rightF1 := switchedRight Gamma.length (incAtDistinct Gamma)
    (bitMask pair1.1) (bitMask pair1.2) (predAt Gamma b2)
  let leftF2 := switchedLeft Gamma.length (incAtDistinct Gamma)
    (bitMask pair2.1) (bitMask pair2.2) (predAt Gamma b2)
  let rightF2 := switchedRight Gamma.length (incAtDistinct Gamma)
    (bitMask pair2.1) (bitMask pair2.2) (predAt Gamma b2)
  have halt1 := exceptional_switched_path_alternating Gamma qP b1 b2 entry1
  have halt2 := exceptional_switched_path_alternating Gamma qP b1 b2 entry2
  change AlternatingSides leftF1 rightF1 path1.indexWalk.vertices at halt1
  change AlternatingSides leftF2 rightF2 path2.indexWalk.vertices at halt2
  rw [← hvertices] at halt2
  have hfirst1 := exceptional_first_side Gamma qP b1 b2 entry1
  have hfirst2 := exceptional_first_side Gamma qP b1 b2 entry2
  change (match path1.indexWalk.vertices with
    | [] => False
    | k :: _ => leftF1 k = true ∧ rightF1 k = false) at hfirst1
  change (match path2.indexWalk.vertices with
    | [] => False
    | k :: _ => leftF2 k = true ∧ rightF2 k = false) at hfirst2
  have hfirst : match path1.indexWalk.vertices with
      | [] => True
      | k :: _ => leftF1 k = leftF2 k ∧ rightF1 k = rightF2 k := by
    cases hv : path1.indexWalk.vertices with
    | nil => exact True.intro
    | cons k rest =>
        rw [hv] at hfirst1
        rw [← hvertices, hv] at hfirst2
        exact ⟨hfirst1.1.trans hfirst2.1.symm,
          hfirst1.2.trans hfirst2.2.symm⟩
  have hsides := alternatingSides_unique leftF1 rightF1 leftF2 rightF2
    path1.indexWalk.vertices halt1 halt2 hfirst j hjPath1
  have hexclusive := exceptional_pathBits_switched_exclusive
    Gamma qP b1 b2 entry1
  have hjPathBit :
      bitMask (pathOccurrenceBits Gamma.length path1.indexWalk.vertices) j = true := by
    change (pathOccurrenceBits Gamma.length path1.indexWalk.vertices).at j = true
    rw [pathOccurrenceBits_at Gamma.length path1.indexWalk.vertices j hjN1]
    exact decide_eq_true hjPath1
  have hjExclusive := hexclusive j hjPathBit
  change differentBits (switched1.1.at j) (switched1.2.at j) = true at hjExclusive
  rw [switchedCode_at_left Gamma b2 pair1 j hjN1,
    switchedCode_at_right Gamma b2 pair1 j hjN1] at hjExclusive
  change differentBits (leftF1 j) (rightF1 j) = true at hjExclusive
  cases hlj : leftF1 j <;> cases hrj : rightF1 j <;>
      simp [hlj, hrj, differentBits] at hjExclusive
  · have hguard := switchedRight_sameSide_guard Gamma.length
      (incAtDistinct Gamma) (bitMask pair2.1) (bitMask pair2.2)
      (predAt Gamma b2)
      (sameSide_guard_incAtDistinct Gamma (bitMask pair2.1)
        facts2.left_pairwise)
      (sameSide_guard_incAtDistinct Gamma (bitMask pair2.2)
        facts2.right_pairwise)
      j i hjN2 hi (by simpa [rightF2] using hsides.2.symm.trans hrj)
      hright2F
    rw [hconf] at hguard
    cases hguard
  · have hguard := switchedLeft_sameSide_guard Gamma.length
      (incAtDistinct Gamma) (bitMask pair1.1) (bitMask pair1.2)
      (predAt Gamma b2)
      (sameSide_guard_incAtDistinct Gamma (bitMask pair1.1)
        facts1.left_pairwise)
      (sameSide_guard_incAtDistinct Gamma (bitMask pair1.2)
        facts1.right_pairwise)
      j i hjN1 hi (by simpa [leftF1] using hlj) hleft1F
    rw [hconf] at hguard
    cases hguard

#print axioms pathSafe
#print axioms exists_false_of_all_false
#print axioms switchedCode_at_left
#print axioms exceptional_first_side
#print axioms path_vertex_lt
#print axioms exceptional_unsafe_cross_side_impossible

end YMGap.Continuum.XiExceptionalUnsafeSideExclusion
