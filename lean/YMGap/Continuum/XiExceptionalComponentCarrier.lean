/-
# Source-specific residual-component carrier

This lifts the residual-component router to an actual exceptional occurrence
carrier.  On the branch where every residual switched-right occurrence is
path-safe, component switching moves each unsafe-left component as a unit.
The resulting terminal background is compatible with the carrier path, both
finite target families are internally compatible and `qP`-admissible, and the
code belongs to the unchanged occurrence-carrier enumeration.
-/

import YMGap.Continuum.XiExceptionalComponentRouter

namespace YMGap.Continuum.XiExceptionalComponentCarrier

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
open YMGap.Continuum.XiExceptionalCustomCarrier
open YMGap.Continuum.XiExceptionalPathMaskAlgebra
open YMGap.Continuum.XiExceptionalRoutedExactWeight
open YMGap.Continuum.XiExceptionalUnsafeSideExclusion
open YMGap.Continuum.XiExceptionalPathSafeInjection
open YMGap.Continuum.XiAdmissibleSourceSwitch
open YMGap.Continuum.XiNonexceptionalTargetValidity
open YMGap.Continuum.XiExceptionalComponentRouter

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

def componentRightSafe
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Prop :=
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
  let switched := switchedBranchCode Gamma b2 pair
  let rightResidual := residualBits pathBits switched.2
  ∀ i, i < Gamma.length → rightResidual.at i = true →
    exceptionalPathSafe Gamma qP b1 b2 entry i = true

def exceptionalComponentCarrierCode
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OccCarrierXiCodeAt Gamma :=
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
  let switched := switchedBranchCode Gamma b2 pair
  let leftResidual := residualBits pathBits switched.1
  let rightResidual := residualBits pathBits switched.2
  let safe := exceptionalPathSafe Gamma qP b1 b2 entry
  exceptionalCustomCarrierCode Gamma qP b1 b2 entry
    (componentBackground Gamma safe leftResidual rightResidual)
    (componentExternal Gamma safe leftResidual rightResidual)

theorem exceptionalComponentCarrierCode_mem
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    exceptionalComponentCarrierCode Gamma qP b1 b2 entry ∈
      occurrenceCarrierXiCodes Gamma := by
  unfold exceptionalComponentCarrierCode
  exact exceptionalCustomCarrierCode_mem Gamma qP b1 b2 entry _ _

private theorem residual_sub_switched
    (Gamma : List (Polymer L)) (path bits : OccBitVec Gamma.length) :
    (selectByBits Gamma (residualBits path bits)).Sublist
      (selectByBits Gamma bits) := by
  rw [← maskFamily_toMask_eq_selectByBits]
  rw [← maskFamily_toMask_eq_selectByBits]
  apply maskFamily_sublist_of_submask
  intro i hres
  cases hi : decide (i < Gamma.length) with
  | true =>
      have hiN := of_decide_eq_true hi
      have hresAt : (residualBits path bits).at i = true := hres
      rw [residualBits_at path bits i hiN] at hresAt
      exact ((Bool.and_eq_true _ _).mp hresAt).2
  | false =>
      have hnlt := of_decide_eq_false hi
      have hout := bitVec_at_false_of_ge (residualBits path bits) i (by omega)
      have hresAt : (residualBits path bits).at i = true := hres
      rw [hout] at hresAt
      cases hresAt

private theorem residual_pair_compatible
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma b2 pair
    familyCompatibleB
        (selectByBits Gamma (residualBits pathBits switched.1)) = true ∧
      familyCompatibleB
        (selectByBits Gamma (residualBits pathBits switched.2)) = true := by
  dsimp only
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let afacts := admissibleSourceFactsOfTrue Gamma qP b1 b2 pair
    facts.source_admissible
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
  let switched := switchedBranchCode Gamma b2 pair
  constructor
  · exact familyCompatibleB_of_sublist
      (residual_sub_switched Gamma pathBits switched.1)
      (switched_left_family_compatible Gamma qP b1 b2 pair afacts)
  · exact familyCompatibleB_of_sublist
      (residual_sub_switched Gamma pathBits switched.2)
      (switched_right_family_compatible Gamma qP b1 b2 pair afacts)

private theorem switchedLeft_q
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length)
    (facts : AdmissibleSourceFacts Gamma qP b1 b2 pair)
    (i : Nat) (hi : i < Gamma.length)
    (hout : (switchedBranchCode Gamma b2 pair).1.at i = true) :
    qP (polyAt Gamma i) = true := by
  rw [switchedCode_at_left Gamma b2 pair i hi] at hout
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

private theorem component_output_origin
    (Gamma : List (Polymer L)) (safe : Nat → Bool)
    (left right : OccBitVec Gamma.length) (i : Nat) (hi : i < Gamma.length) :
    (componentBackground Gamma safe left right).at i = true →
        left.at i = true ∨ right.at i = true := by
  intro hout
  rw [componentBackground_at Gamma safe left right i hi] at hout
  unfold switchedLeft swapLeftMask bitMask at hout
  cases hcut : forwardComponent Gamma.length (incAtDistinct Gamma)
      (fun j => left.at j) (fun j => right.at j) (unsafeMask safe) i
  · exact Or.inl (by simpa [hcut] using hout)
  · exact Or.inr (by simpa [hcut] using hout)

private theorem component_external_origin
    (Gamma : List (Polymer L)) (safe : Nat → Bool)
    (left right : OccBitVec Gamma.length) (i : Nat) (hi : i < Gamma.length) :
    (componentExternal Gamma safe left right).at i = true →
        left.at i = true ∨ right.at i = true := by
  intro hout
  rw [componentExternal_at Gamma safe left right i hi] at hout
  unfold switchedRight swapRightMask bitMask at hout
  cases hcut : forwardComponent Gamma.length (incAtDistinct Gamma)
      (fun j => left.at j) (fun j => right.at j) (unsafeMask safe) i
  · exact Or.inr (by simpa [hcut] using hout)
  · exact Or.inl (by simpa [hcut] using hout)

private theorem component_output_q
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma b2 pair
    let leftResidual := residualBits pathBits switched.1
    let rightResidual := residualBits pathBits switched.2
    let safe := exceptionalPathSafe Gamma qP b1 b2 entry
    (selectByBits Gamma
        (componentBackground Gamma safe leftResidual rightResidual)).all qP = true ∧
      (selectByBits Gamma
        (componentExternal Gamma safe leftResidual rightResidual)).all qP = true := by
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
  have hresQ : ∀ i, i < Gamma.length →
      (leftResidual.at i = true ∨ rightResidual.at i = true) →
      qP (polyAt Gamma i) = true := by
    intro i hi hside
    rcases hside with hleft | hright
    · have hswitched : switched.1.at i = true := by
        rw [residualBits_at pathBits switched.1 i hi] at hleft
        exact ((Bool.and_eq_true _ _).mp hleft).2
      exact switchedLeft_q Gamma qP b1 b2 pair afacts i hi hswitched
    · have hswitched : switched.2.at i = true := by
        rw [residualBits_at pathBits switched.2 i hi] at hright
        exact ((Bool.and_eq_true _ _).mp hright).2
      rw [switchedCode_at_right Gamma b2 pair i hi] at hswitched
      exact switchedRight_q Gamma qP b1 b2 pair afacts i hi hswitched
  constructor <;> rw [← maskFamily_toMask_eq_selectByBits] <;>
    apply maskFamily_all_of_pointwise <;> intro i hi hout
  · exact hresQ i hi
      (component_output_origin Gamma safe leftResidual rightResidual i hi hout)
  · exact hresQ i hi
      (component_external_origin Gamma safe leftResidual rightResidual i hi hout)

structure ComponentCarrierFacts
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Type where
  backgroundCompatible :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma b2 pair
    let leftResidual := residualBits pathBits switched.1
    let rightResidual := residualBits pathBits switched.2
    let safe := exceptionalPathSafe Gamma qP b1 b2 entry
    familyCompatibleB (selectByBits Gamma
      (componentBackground Gamma safe leftResidual rightResidual)) = true
  backgroundQ :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma b2 pair
    let leftResidual := residualBits pathBits switched.1
    let rightResidual := residualBits pathBits switched.2
    let safe := exceptionalPathSafe Gamma qP b1 b2 entry
    (selectByBits Gamma
      (componentBackground Gamma safe leftResidual rightResidual)).all qP = true
  backgroundPath :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma b2 pair
    let leftResidual := residualBits pathBits switched.1
    let rightResidual := residualBits pathBits switched.2
    let safe := exceptionalPathSafe Gamma qP b1 b2 entry
    ∀ X, X ∈ path.polymerWalk.vertices →
      ∀ T, T ∈ selectByBits Gamma
        (componentBackground Gamma safe leftResidual rightResidual) →
        compatibleB X T = true
  externalCompatible :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma b2 pair
    let leftResidual := residualBits pathBits switched.1
    let rightResidual := residualBits pathBits switched.2
    let safe := exceptionalPathSafe Gamma qP b1 b2 entry
    familyCompatibleB (selectByBits Gamma
      (componentExternal Gamma safe leftResidual rightResidual)) = true
  externalQ :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma b2 pair
    let leftResidual := residualBits pathBits switched.1
    let rightResidual := residualBits pathBits switched.2
    let safe := exceptionalPathSafe Gamma qP b1 b2 entry
    (selectByBits Gamma
      (componentExternal Gamma safe leftResidual rightResidual)).all qP = true

def componentCarrierFacts_of_rightSafe
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hrightSafe : componentRightSafe Gamma qP b1 b2 entry) :
    ComponentCarrierFacts Gamma qP b1 b2 entry := by
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
  let switched := switchedBranchCode Gamma b2 pair
  let leftResidual := residualBits pathBits switched.1
  let rightResidual := residualBits pathBits switched.2
  let safe := exceptionalPathSafe Gamma qP b1 b2 entry
  have hcompat := residual_pair_compatible Gamma qP b1 b2 entry
  change familyCompatibleB (selectByBits Gamma leftResidual) = true ∧
    familyCompatibleB (selectByBits Gamma rightResidual) = true at hcompat
  have houtputs := component_families_compatible Gamma safe
    leftResidual rightResidual hcompat.1 hcompat.2
  have hright : ∀ i, i < Gamma.length → rightResidual.at i = true →
      safe i = true := by
    simpa [componentRightSafe, pair, facts, path, pathBits, switched,
      rightResidual, safe] using hrightSafe
  have hunsafeExclusive : ∀ i, i < Gamma.length → safe i = false →
      leftResidual.at i = true → rightResidual.at i = false := by
    intro i hi hunsafe hleft
    cases hrightAt : rightResidual.at i with
    | false => rfl
    | true =>
        exact False.elim (exceptional_unsafe_cross_side_impossible
          Gamma qP b1 b2 entry entry rfl i hi
          (by simpa [safe, exceptionalPathSafe] using hunsafe) hleft hrightAt)
  have hbackgroundSafe := component_background_safe_of_right_safe
    Gamma safe leftResidual rightResidual hunsafeExclusive hright
  have hq := component_output_q Gamma qP b1 b2 entry
  change
    (selectByBits Gamma
        (componentBackground Gamma safe leftResidual rightResidual)).all qP = true ∧
      (selectByBits Gamma
        (componentExternal Gamma safe leftResidual rightResidual)).all qP = true at hq
  refine
    { backgroundCompatible := houtputs.1
      backgroundQ := hq.1
      backgroundPath := ?_
      externalCompatible := houtputs.2
      externalQ := hq.2 }
  dsimp only
  intro X hX T hT
  rw [path.polymer_vertices] at hX
  obtain ⟨j, hjPath, hjX⟩ := List.mem_map.mp hX
  have hTmask : T ∈ maskFamily Gamma
      (bitMask (componentBackground Gamma safe leftResidual rightResidual)) := by
    rw [maskFamily_toMask_eq_selectByBits]
    exact hT
  obtain ⟨i, hi, hbg, hiT⟩ := mem_maskFamily_occurrence Gamma
    (bitMask (componentBackground Gamma safe leftResidual rightResidual)) hTmask
  have hbgAt : (componentBackground Gamma safe leftResidual rightResidual).at i =
      true := hbg
  have hsafe := hbackgroundSafe i hi hbgAt
  have hresSide := component_output_origin Gamma safe leftResidual rightResidual
    i hi hbgAt
  have hpathFalse : pathBits.at i = false := by
    rcases hresSide with hleft | hrightAt
    · rw [residualBits_at pathBits switched.1 i hi] at hleft
      cases hp : pathBits.at i <;> simp_all
    · rw [residualBits_at pathBits switched.2 i hi] at hrightAt
      cases hp : pathBits.at i <;> simp_all
  have hji : j ≠ i := by
    intro h
    subst j
    have hpathTrue : pathBits.at i = true := by
      rw [pathOccurrenceBits_at Gamma.length path.indexWalk.vertices i hi]
      exact decide_eq_true hjPath
    rw [hpathTrue] at hpathFalse
    cases hpathFalse
  unfold safe exceptionalPathSafe pathSafe at hsafe
  have hnotConflict := List.all_eq_true.mp hsafe j hjPath
  have hconflict : symConflict (incAtDistinct Gamma) j i = false :=
    eq_false_of_not_true hnotConflict
  rw [← hjX, ← hiT]
  exact compatibleB_of_incAtDistinct_symConflict_false Gamma hji hconflict

theorem componentCarrier_externalCompatible_of_rightSafe
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hrightSafe : componentRightSafe Gamma qP b1 b2 entry) :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma b2 pair
    let leftResidual := residualBits pathBits switched.1
    let rightResidual := residualBits pathBits switched.2
    let safe := exceptionalPathSafe Gamma qP b1 b2 entry
    familyCompatibleB (selectByBits Gamma
      (componentExternal Gamma safe leftResidual rightResidual)) = true :=
  (componentCarrierFacts_of_rightSafe Gamma qP b1 b2 entry
    hrightSafe).externalCompatible

#print axioms exceptionalComponentCarrierCode_mem
#print axioms componentCarrier_externalCompatible_of_rightSafe

end YMGap.Continuum.XiExceptionalComponentCarrier
