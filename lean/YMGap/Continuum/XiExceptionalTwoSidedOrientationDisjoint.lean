/-
# Disjoint two-orientation original-residual carrier

Use the canonical payload orientation when the left residual is path-safe.
If the left residual is explicitly path-unsafe but the right residual is
path-safe, use the symmetric payload orientation.  Equality across the two
orientations would put the same unsafe occurrence on original right in the
canonical source and original left in the symmetric source.  The common
decoded path then contradicts same-side compatibility at a conflicting path
vertex.  Thus the two exact carrier regions combine into one duplicate-free
target allocation.
-/

import YMGap.Continuum.XiExceptionalSymmetricTwoSidedCarrier

namespace YMGap.Continuum.XiExceptionalTwoSidedOrientationDisjoint

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalCustomCarrier
open YMGap.Continuum.XiExceptionalPathMaskAlgebra
open YMGap.Continuum.XiExceptionalPathSideDecoder
open YMGap.Continuum.XiExceptionalTargetBlocks
open YMGap.Continuum.XiExceptionalParallelResidualBlock
open YMGap.Continuum.XiExceptionalOneAttachedResidualConsumer
open YMGap.Continuum.XiExceptionalOriginalResidualInjection
open YMGap.Continuum.XiExceptionalUnsafeSideExclusion
open YMGap.Continuum.XiExceptionalTwoSidedOriginalCarrier
open YMGap.Continuum.XiExceptionalSymmetricTwoSidedCarrier

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

def OriginalLeftResidualPathUnsafe
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Prop :=
  ∃ i, i < Gamma.length ∧
    (leftPathResidual Gamma qP b1 b2 entry).at i = true ∧
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
    pathSafe Gamma path.indexWalk.vertices i = false

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

private theorem symConflict_true_compatible_false
    (Gamma : List (Polymer L)) {i j : Nat} (hij : i ≠ j)
    (hconf : symConflict (incAtDistinct Gamma) i j = true) :
    compatibleB (polyAt Gamma i) (polyAt Gamma j) = false := by
  cases hc : compatibleB (polyAt Gamma i) (polyAt Gamma j) with
  | false => rfl
  | true =>
      have hrev : compatibleB (polyAt Gamma j) (polyAt Gamma i) = true := by
        rw [compatibleB_symm]
        exact hc
      unfold symConflict incAtDistinct at hconf
      simp [decide_eq_true hij, decide_eq_true hij.symm, hc, hrev] at hconf

/-- Cross-orientation equality is impossible once the symmetric source has
an explicit unsafe original-left occurrence. -/
theorem original_twoSided_cross_orientation_ne
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (canonical symmetric : ExceptionalSourceEntry Gamma qP b1 b2)
    (hunsafe : OriginalLeftResidualPathUnsafe Gamma qP b1 b2 symmetric) :
    originalTwoSidedCarrierCode Gamma qP b1 b2 canonical ≠
      originalSymmetricTwoSidedCarrierCode Gamma qP b1 b2 symmetric := by
  intro hcode
  let pair1 := canonical.1
  let pair2 := symmetric.1
  let facts1 := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair1 canonical.2
  let facts2 := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair2 symmetric.2
  let path1 := sourceExceptionalPath Gamma qP b1 b2 pair1 facts1
  let path2 := sourceExceptionalPath Gamma qP b1 b2 pair2 facts2
  have hverticesRaw := congrArg
    (fun code => occurrenceChainVertices code.carrier.start code.carrier.chain)
    hcode
  have hvertices : path1.indexWalk.vertices = path2.indexWalk.vertices := by
    simpa [originalTwoSidedCarrierCode,
      originalSymmetricTwoSidedCarrierCode, exceptionalCustomCarrierCode,
      occurrenceChainVertices_ofWalk] using hverticesRaw
  have hseedRaw := congrArg
    (fun code => occurrenceChainEnd code.carrier.start code.carrier.chain)
    hcode
  have hseed : path1.seed = path2.seed := by
    simpa [originalTwoSidedCarrierCode,
      originalSymmetricTwoSidedCarrierCode, exceptionalCustomCarrierCode,
      occurrenceChainEnd_ofWalk] using hseedRaw
  have hcrossResidual : rightPathResidual Gamma qP b1 b2 canonical =
      leftPathResidual Gamma qP b1 b2 symmetric := by
    simpa [originalTwoSidedCarrierCode,
      originalSymmetricTwoSidedCarrierCode, exceptionalCustomCarrierCode]
      using congrArg (fun code => code.external) hcode
  obtain ⟨i, hi, hleft2, hunsafeI⟩ := hunsafe
  have hright1 :
      (rightPathResidual Gamma qP b1 b2 canonical).at i = true := by
    rw [hcrossResidual]
    exact hleft2
  have hpairLeft2 : pair2.1.at i = true :=
    leftPathResidual_submask_left Gamma qP b1 b2 symmetric i hleft2
  have hpairRight1 : pair1.2.at i = true :=
    rightPathResidual_submask_right Gamma qP b1 b2 canonical i hright1
  have hiNotPath2 : i ∉ path2.indexWalk.vertices := by
    rw [leftPathResidual_at Gamma qP b1 b2 symmetric i hi] at hleft2
    have hnotDecide := ((Bool.and_eq_true _ _).mp hleft2).1
    exact of_decide_eq_false (eq_false_of_not_true hnotDecide)
  have hiNotPath1 : i ∉ path1.indexWalk.vertices := by
    intro hipath
    apply hiNotPath2
    rw [← hvertices]
    exact hipath
  unfold pathSafe at hunsafeI
  obtain ⟨j, hjPath2, hjNot⟩ := exists_false_of_all_false
    (fun j => !(symConflict (incAtDistinct Gamma) j i))
    path2.indexWalk.vertices hunsafeI
  have hjPath1 : j ∈ path1.indexWalk.vertices := by
    rw [hvertices]
    exact hjPath2
  have hji : j ≠ i := by
    intro h
    subst j
    exact hiNotPath2 hjPath2
  have hconf : symConflict (incAtDistinct Gamma) j i = true := by
    cases hc : symConflict (incAtDistinct Gamma) j i with
    | true => rfl
    | false => simp [hc] at hjNot
  have hcompatFalse :
      compatibleB (polyAt Gamma j) (polyAt Gamma i) = false :=
    symConflict_true_compatible_false Gamma hji hconf
  let leftF1 := bitMask pair1.1
  let rightF1 := bitMask pair1.2
  let leftF2 := bitMask pair2.1
  let rightF2 := bitMask pair2.2
  have halt1 := alternatingSides_of_disagreementWalk Gamma.length
    (incAtDistinct Gamma) leftF1 rightF1 path1.indexWalk
  have halt2 := alternatingSides_of_disagreementWalk Gamma.length
    (incAtDistinct Gamma) leftF2 rightF2 path2.indexWalk
  rw [← hvertices] at halt2
  have hseedParts1 := forwardSeed_parts Gamma.length leftF1 rightF1
    (predAt Gamma b2) path1.seed_true
  have hseedParts2 := forwardSeed_parts Gamma.length leftF2 rightF2
    (predAt Gamma b2) path2.seed_true
  rw [← hseed] at hseedParts2
  have hseedSides :
      leftF1 path1.seed = leftF2 path1.seed ∧
        rightF1 path1.seed = rightF2 path1.seed :=
    ⟨hseedParts1.2.1.trans hseedParts2.2.1.symm,
      hseedParts1.2.2.1.trans hseedParts2.2.2.1.symm⟩
  have hend := endSameSides_of_walk leftF1 rightF1 leftF2 rightF2
    path1.indexWalk hseedSides
  have hpathSides := alternatingSides_unique_from_end
    leftF1 rightF1 leftF2 rightF2 path1.indexWalk.vertices halt1 halt2 hend
  have hsides := hpathSides j hjPath1
  have hseedN := (forwardSeed_parts Gamma.length
    (bitMask pair2.1) (bitMask pair2.2) (predAt Gamma b2)
    path2.seed_true).1
  have hjN : j < Gamma.length :=
    walk_vertices_lt_of_seed Gamma.length (incAtDistinct Gamma)
      (bitMask pair2.1) (bitMask pair2.2) path2.indexWalk
      hseedN j hjPath2
  have hjBit : bitMask
      (pathOccurrenceBits Gamma.length path2.indexWalk.vertices) j = true := by
    change (pathOccurrenceBits Gamma.length path2.indexWalk.vertices).at j = true
    rw [pathOccurrenceBits_at Gamma.length path2.indexWalk.vertices j hjN]
    exact decide_eq_true hjPath2
  have hexclusive := exceptional_pathBits_original_exclusive
    Gamma qP b1 b2 symmetric j hjBit
  change differentBits (pair2.1.at j) (pair2.2.at j) = true at hexclusive
  cases hlj : pair2.1.at j <;> cases hrj : pair2.2.at j <;>
      simp [hlj, hrj, differentBits] at hexclusive
  · have hsame := facts1.right_pairwise j i hji
        (hsides.2.trans hrj) hpairRight1
    rw [hcompatFalse] at hsame
    cases hsame
  · have hsame := facts2.left_pairwise j i hji hlj hpairLeft2
    rw [hcompatFalse] at hsame
    cases hsame

/-! ## A single combined exact allocation -/

inductive PathSafeOrientedEntry
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool) : Type
  | canonical (entry : ExceptionalSourceEntry Gamma qP b1 b2)
      (safe : OriginalLeftResidualPathSafe Gamma qP b1 b2 entry)
  | symmetric (entry : ExceptionalSourceEntry Gamma qP b1 b2)
      (hunsafe : OriginalLeftResidualPathUnsafe Gamma qP b1 b2 entry)
      (safe : OriginalRightResidualPathSafe Gamma qP b1 b2 entry)

namespace PathSafeOrientedEntry

variable {Gamma : List (Polymer L)}
variable {qP b1 b2 : Polymer L → Bool}

def entry : PathSafeOrientedEntry Gamma qP b1 b2 →
    ExceptionalSourceEntry Gamma qP b1 b2
  | .canonical entry _ => entry
  | .symmetric entry _ _ => entry

def code : PathSafeOrientedEntry Gamma qP b1 b2 →
    OccCarrierXiCodeAt Gamma
  | .canonical entry _ =>
      originalTwoSidedCarrierCode Gamma qP b1 b2 entry
  | .symmetric entry _ _ =>
      originalSymmetricTwoSidedCarrierCode Gamma qP b1 b2 entry

theorem code_mem (oriented : PathSafeOrientedEntry Gamma qP b1 b2) :
    oriented.code ∈ occurrenceCarrierXiCodes Gamma := by
  cases oriented with
  | canonical entry _ =>
      exact originalTwoSidedCarrierCode_mem Gamma qP b1 b2 entry
  | symmetric entry _ _ =>
      exact originalSymmetricTwoSidedCarrierCode_mem Gamma qP b1 b2 entry

theorem code_weight_eqv_source
    (w : Q') (label : L.Plaquette → Rep)
    (oriented : PathSafeOrientedEntry Gamma qP b1 b2) :
    occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label oriented.code ≈
      occurrencePairWeight w qP b1 b2 Gamma label oriented.entry.1 := by
  cases oriented with
  | canonical entry safe =>
      exact originalTwoSidedCarrierCode_weight_eqv_source
        w qP b1 b2 Gamma label entry safe
  | symmetric entry _ safe =>
      exact originalSymmetricTwoSidedCarrierCode_weight_eqv_source
        w qP b1 b2 Gamma label entry safe

theorem code_injective (a b : PathSafeOrientedEntry Gamma qP b1 b2)
    (hcode : a.code = b.code) : a = b := by
  cases a with
  | canonical entryA safeA =>
      cases b with
      | canonical entryB safeB =>
          have hentry := originalTwoSidedCarrierCode_injective
            Gamma qP b1 b2 entryA entryB hcode
          subst entryB
          rfl
      | symmetric entryB unsafeB safeB =>
          exact False.elim ((original_twoSided_cross_orientation_ne
            Gamma qP b1 b2 entryA entryB unsafeB) hcode)
  | symmetric entryA unsafeA safeA =>
      cases b with
      | canonical entryB safeB =>
          exact False.elim ((original_twoSided_cross_orientation_ne
            Gamma qP b1 b2 entryB entryA unsafeA) hcode.symm)
      | symmetric entryB unsafeB safeB =>
          have hentry := originalSymmetricTwoSidedCarrierCode_injective
            Gamma qP b1 b2 entryA entryB hcode
          subst entryB
          rfl

end PathSafeOrientedEntry

private theorem flatMap_singleton_eq_map {alpha beta : Type}
    (f : alpha → beta) : ∀ xs : List alpha,
    xs.flatMap (fun x => [f x]) = xs.map f
  | [] => rfl
  | x :: xs => by
      simp only [List.flatMap_cons, List.map_cons, List.singleton_append]
      rw [flatMap_singleton_eq_map f xs]

theorem twoSided_oriented_region_global_bound
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (source : List (PathSafeOrientedEntry Gamma qP b1 b2))
    (hsource : source.Nodup) :
    qListSum (fun oriented => occurrencePairWeight w qP b1 b2 Gamma label
        oriented.entry.1) source ≤
      qListSum (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
        (occurrenceCarrierXiCodes Gamma) := by
  apply qListSum_le_of_disjoint_blocks source
    (occurrenceCarrierXiCodes Gamma)
    (fun oriented => occurrencePairWeight w qP b1 b2 Gamma label
      oriented.entry.1)
    (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
    (fun oriented => [oriented.code])
  · rw [flatMap_singleton_eq_map]
    apply nodup_map_of_injOn _ source hsource
    intro a _ b _ hcode
    exact PathSafeOrientedEntry.code_injective a b hcode
  · intro code hcode
    obtain ⟨oriented, _, hsingleton⟩ := List.mem_flatMap.mp hcode
    rw [List.mem_singleton] at hsingleton
    subst code
    exact oriented.code_mem
  · intro oriented _
    simp only [qListSum_cons, qListSum_nil, Q'.add_zero']
    exact Q'.ge_of_eqv (oriented.code_weight_eqv_source w label)
  · intro code _
    exact occurrenceCarrierXiCodeWeight_nonnegative hw
      qP b1 b2 Gamma label code

#print axioms original_twoSided_cross_orientation_ne
#print axioms PathSafeOrientedEntry.code_mem
#print axioms PathSafeOrientedEntry.code_weight_eqv_source
#print axioms PathSafeOrientedEntry.code_injective
#print axioms twoSided_oriented_region_global_bound

end YMGap.Continuum.XiExceptionalTwoSidedOrientationDisjoint
