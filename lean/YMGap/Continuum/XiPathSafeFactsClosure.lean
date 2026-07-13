/-
# Discharge the path-safe target facts forced by admissibility

Four fields of `PathSafeRoutedFacts` are consequences of the already-proved
source and path invariants.  The background is a safe subfamily of switched
left, hence compatible, `qP`-admissible, and compatible with every path
vertex.  Both residual switched sides are `qP`-admissible, so their routed
external union is `qP`-admissible.  Only internal compatibility of that
external union remains a separate routing question; the frozen package is
assembled unchanged from precisely that field.
-/

import YMGap.Continuum.XiOneEndedInfluenceBound

namespace YMGap.Continuum.XiPathSafeFactsClosure

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
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
open YMGap.Continuum.XiExceptionalBranchRouter
open YMGap.Continuum.XiExceptionalPathMaskAlgebra
open YMGap.Continuum.XiExceptionalPathSafeInjection
open YMGap.Continuum.XiExceptionalPathSafeExactWeight
open YMGap.Continuum.XiExceptionalUnsafeSideExclusion
open YMGap.Continuum.XiAdmissibleSourceSwitch
open YMGap.Continuum.XiNonexceptionalTargetValidity

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

private theorem switchedLeft_q
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length)
    (facts : AdmissibleSourceFacts Gamma qP b1 b2 pair)
    (i : Nat) (hi : i < Gamma.length)
    (hout : switchedLeft Gamma.length (incAtDistinct Gamma)
      (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i = true) :
    qP (polyAt Gamma i) = true := by
  cases hcut : forwardComponent Gamma.length (incAtDistinct Gamma)
      (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i with
  | false =>
      have hleft : pair.1.at i = true := by
        simpa [switchedLeft, swapLeftMask, hcut, bitMask] using hout
      exact facts.left_q i hi hleft
  | true =>
      have hright : pair.2.at i = true := by
        simpa [switchedLeft, swapLeftMask, hcut, bitMask] using hout
      exact facts.right_q i hi hright

private theorem routedBackground_sub_switchedLeft
    (Gamma : List (Polymer L)) (safe : Nat → Bool)
    (pathBits : OccBitVec Gamma.length)
    (switched : MaskPair Gamma.length) :
    ∀ i, i < Gamma.length →
      (routedBackground safe (residualBits pathBits switched.1)).at i = true →
        switched.1.at i = true := by
  intro i hi hbg
  rw [routedBackground_at safe (residualBits pathBits switched.1) i hi] at hbg
  have hres := ((Bool.and_eq_true _ _).mp hbg).2
  rw [residualBits_at pathBits switched.1 i hi] at hres
  cases hp : pathBits.at i <;> simp_all

private theorem routedExternal_from_residual
    (Gamma : List (Polymer L)) (safe : Nat → Bool)
    (pathBits : OccBitVec Gamma.length)
    (switched : MaskPair Gamma.length) :
    ∀ i, i < Gamma.length →
      (routedExternal safe (residualBits pathBits switched.1)
        (residualBits pathBits switched.2)).at i = true →
      switched.1.at i = true ∨ switched.2.at i = true := by
  intro i hi hext
  rw [routedExternal_at safe (residualBits pathBits switched.1)
      (residualBits pathBits switched.2) i hi] at hext
  rcases (Bool.or_eq_true _ _).mp hext with hleft | hright
  · have hres := ((Bool.and_eq_true _ _).mp hleft).2
    rw [residualBits_at pathBits switched.1 i hi] at hres
    cases hp : pathBits.at i <;> simp_all
  · rw [residualBits_at pathBits switched.2 i hi] at hright
    cases hp : pathBits.at i <;> simp_all

theorem pathSafe_backgroundCompatible
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma b2 pair
    let leftResidual := residualBits pathBits switched.1
    familyCompatibleB (selectByBits Gamma
      (routedBackground (exceptionalPathSafe Gamma qP b1 b2 entry)
        leftResidual)) = true := by
  dsimp only
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let afacts := admissibleSourceFactsOfTrue Gamma qP b1 b2 pair
    facts.source_admissible
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
  let switched := switchedBranchCode Gamma b2 pair
  let leftResidual := residualBits pathBits switched.1
  let safe := exceptionalPathSafe Gamma qP b1 b2 entry
  have hsub : (selectByBits Gamma (routedBackground safe leftResidual)).Sublist
      (leftFamily Gamma switched) := by
    rw [← maskFamily_toMask_eq_selectByBits]
    unfold leftFamily
    rw [← maskFamily_toMask_eq_selectByBits]
    apply maskFamily_sublist_of_submask
    intro i hbg
    cases hi : decide (i < Gamma.length) with
    | true =>
        have hiN := of_decide_eq_true hi
        exact routedBackground_sub_switchedLeft Gamma safe pathBits switched
          i hiN hbg
    | false =>
        have hnlt : ¬ i < Gamma.length := of_decide_eq_false hi
        have hout := bitVec_at_false_of_ge
          (routedBackground safe leftResidual) i (by omega)
        have hbgAt : (routedBackground safe leftResidual).at i = true := hbg
        rw [hout] at hbgAt
        cases hbgAt
  exact familyCompatibleB_of_sublist hsub
    (switched_left_family_compatible Gamma qP b1 b2 pair afacts)

theorem pathSafe_backgroundQ
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma b2 pair
    let leftResidual := residualBits pathBits switched.1
    (selectByBits Gamma
      (routedBackground (exceptionalPathSafe Gamma qP b1 b2 entry)
        leftResidual)).all qP = true := by
  dsimp only
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let afacts := admissibleSourceFactsOfTrue Gamma qP b1 b2 pair
    facts.source_admissible
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
  let switched := switchedBranchCode Gamma b2 pair
  let leftResidual := residualBits pathBits switched.1
  let safe := exceptionalPathSafe Gamma qP b1 b2 entry
  rw [← maskFamily_toMask_eq_selectByBits]
  apply maskFamily_all_of_pointwise
  intro i hi hbg
  have hswitched := routedBackground_sub_switchedLeft Gamma safe pathBits
    switched i hi hbg
  have hout : switchedLeft Gamma.length (incAtDistinct Gamma)
      (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i = true := by
    rw [← switchedCode_at_left Gamma b2 pair i hi]
    exact hswitched
  exact switchedLeft_q Gamma qP b1 b2 pair afacts i hi hout

theorem pathSafe_backgroundPath
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma b2 pair
    let leftResidual := residualBits pathBits switched.1
    ∀ X, X ∈ path.polymerWalk.vertices →
      ∀ T, T ∈ selectByBits Gamma
        (routedBackground (exceptionalPathSafe Gamma qP b1 b2 entry)
          leftResidual) → compatibleB X T = true := by
  dsimp only
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
  let switched := switchedBranchCode Gamma b2 pair
  let leftResidual := residualBits pathBits switched.1
  let safe := exceptionalPathSafe Gamma qP b1 b2 entry
  intro X hX T hT
  rw [path.polymer_vertices] at hX
  obtain ⟨j, hjPath, hjX⟩ := List.mem_map.mp hX
  have hTmask : T ∈ maskFamily Gamma
      (bitMask (routedBackground safe leftResidual)) := by
    rw [maskFamily_toMask_eq_selectByBits]
    exact hT
  obtain ⟨i, hi, hbg, hiT⟩ := mem_maskFamily_occurrence Gamma
    (bitMask (routedBackground safe leftResidual)) hTmask
  have hbgAt : (routedBackground safe leftResidual).at i = true := hbg
  rw [routedBackground_at safe leftResidual i hi] at hbgAt
  have hparts := (Bool.and_eq_true _ _).mp hbgAt
  have hsafe : pathSafe Gamma path.indexWalk.vertices i = true := by
    simpa [safe, exceptionalPathSafe] using hparts.1
  have hres := hparts.2
  have hpathFalse : pathBits.at i = false := by
    rw [residualBits_at pathBits switched.1 i hi] at hres
    cases hp : pathBits.at i <;> simp_all
  have hji : j ≠ i := by
    intro h
    subst j
    have hpathTrue : pathBits.at i = true := by
      rw [pathOccurrenceBits_at Gamma.length path.indexWalk.vertices i hi]
      exact decide_eq_true hjPath
    rw [hpathTrue] at hpathFalse
    cases hpathFalse
  unfold pathSafe at hsafe
  have hnotConflict := List.all_eq_true.mp hsafe j hjPath
  have hconflict : symConflict (incAtDistinct Gamma) j i = false :=
    eq_false_of_not_true hnotConflict
  rw [← hjX, ← hiT]
  exact compatibleB_of_incAtDistinct_symConflict_false Gamma hji hconflict

theorem pathSafe_externalQ
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma b2 pair
    let leftResidual := residualBits pathBits switched.1
    let rightResidual := residualBits pathBits switched.2
    (selectByBits Gamma
      (routedExternal (exceptionalPathSafe Gamma qP b1 b2 entry)
        leftResidual rightResidual)).all qP = true := by
  dsimp only
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let afacts := admissibleSourceFactsOfTrue Gamma qP b1 b2 pair
    facts.source_admissible
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
  let switched := switchedBranchCode Gamma b2 pair
  let leftResidual := residualBits pathBits switched.1
  let rightResidual := residualBits pathBits switched.2
  let safe := exceptionalPathSafe Gamma qP b1 b2 entry
  rw [← maskFamily_toMask_eq_selectByBits]
  apply maskFamily_all_of_pointwise
  intro i hi hext
  rcases routedExternal_from_residual Gamma safe pathBits switched i hi hext with
    hleft | hright
  · have hout : switchedLeft Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i = true := by
      rw [← switchedCode_at_left Gamma b2 pair i hi]
      exact hleft
    exact switchedLeft_q Gamma qP b1 b2 pair afacts i hi hout
  · have hout : switchedRight Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i = true := by
      rw [← switchedCode_at_right Gamma b2 pair i hi]
      exact hright
    exact switchedRight_q Gamma qP b1 b2 pair afacts i hi hout

/-- The exact remaining path-safe field, without changing the frozen target
package. -/
structure PathSafeExternalCompatibility
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Type where
  compatible :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma b2 pair
    let leftResidual := residualBits pathBits switched.1
    let rightResidual := residualBits pathBits switched.2
    familyCompatibleB (selectByBits Gamma
      (routedExternal (exceptionalPathSafe Gamma qP b1 b2 entry)
        leftResidual rightResidual)) = true

def pathSafeRoutedFactsOfExternalCompatibility
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hexternal : PathSafeExternalCompatibility Gamma qP b1 b2 entry) :
    PathSafeRoutedFacts Gamma qP b1 b2 entry :=
  { backgroundCompatible := pathSafe_backgroundCompatible Gamma qP b1 b2 entry
    backgroundQ := pathSafe_backgroundQ Gamma qP b1 b2 entry
    backgroundPath := pathSafe_backgroundPath Gamma qP b1 b2 entry
    externalCompatible := hexternal.compatible
    externalQ := pathSafe_externalQ Gamma qP b1 b2 entry }

#print axioms pathSafe_backgroundCompatible
#print axioms pathSafe_backgroundQ
#print axioms pathSafe_backgroundPath
#print axioms pathSafe_externalQ
#print axioms pathSafeRoutedFactsOfExternalCompatibility

end YMGap.Continuum.XiPathSafeFactsClosure
