/-
# Unconditional path-safe residual routing

The router's Boolean collision is excluded by exceptional-source
admissibility once the common decoded path is known.  This file packages the
path-derived safety predicate into the target code and removes the previous
`rightSafe` hypothesis from the residual decoder and source injection.
-/

import YMGap.Continuum.XiExceptionalUnsafeSideExclusion

namespace YMGap.Continuum.XiExceptionalPathSafeInjection

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
open YMGap.Continuum.XiExceptionalCustomCarrier
open YMGap.Continuum.XiExceptionalBranchRouter
open YMGap.Continuum.XiExceptionalPathMaskAlgebra
open YMGap.Continuum.XiExceptionalRoutedExactWeight
open YMGap.Continuum.XiExceptionalPathSideDecoder
open YMGap.Continuum.XiExceptionalUnsafeSideExclusion

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

/-! ## 1. Router injection under source-derived cross-side exclusion -/

theorem routedMaskPair_injective_of_unsafe_cross
    (safe : Nat → Bool)
    (left1 right1 left2 right2 : OccBitVec n)
    (hcross12 : ∀ i, i < n → safe i = false →
      left1.at i = true → right2.at i = true → False)
    (hcross21 : ∀ i, i < n → safe i = false →
      left2.at i = true → right1.at i = true → False)
    (hroute : routedMaskPair safe left1 right1 =
      routedMaskPair safe left2 right2) :
    (left1, right1) = (left2, right2) := by
  have hbackground : routedBackground safe left1 =
      routedBackground safe left2 := congrArg Prod.fst hroute
  have hexternal : routedExternal safe left1 right1 =
      routedExternal safe left2 right2 := congrArg Prod.snd hroute
  apply Prod.ext
  · change left1 = left2
    apply BitVec.ext
    intro i
    by_cases hi : i < n
    · have hbg := congrArg (fun bits => bits.at i) hbackground
      have hext := congrArg (fun bits => bits.at i) hexternal
      change (routedBackground safe left1).at i =
        (routedBackground safe left2).at i at hbg
      change (routedExternal safe left1 right1).at i =
        (routedExternal safe left2 right2).at i at hext
      rw [routedBackground_at safe left1 i hi,
        routedBackground_at safe left2 i hi] at hbg
      rw [routedExternal_at safe left1 right1 i hi,
        routedExternal_at safe left2 right2 i hi] at hext
      cases hsafe : safe i <;>
        cases hl1 : left1.at i <;> cases hr1 : right1.at i <;>
        cases hl2 : left2.at i <;> cases hr2 : right2.at i <;>
        simp_all
    · have hge : n ≤ i := by omega
      exact (bitVec_at_false_of_ge left1 i hge).trans
        (bitVec_at_false_of_ge left2 i hge).symm
  · change right1 = right2
    apply BitVec.ext
    intro i
    by_cases hi : i < n
    · have hbg := congrArg (fun bits => bits.at i) hbackground
      have hext := congrArg (fun bits => bits.at i) hexternal
      change (routedBackground safe left1).at i =
        (routedBackground safe left2).at i at hbg
      change (routedExternal safe left1 right1).at i =
        (routedExternal safe left2 right2).at i at hext
      rw [routedBackground_at safe left1 i hi,
        routedBackground_at safe left2 i hi] at hbg
      rw [routedExternal_at safe left1 right1 i hi,
        routedExternal_at safe left2 right2 i hi] at hext
      cases hsafe : safe i <;>
        cases hl1 : left1.at i <;> cases hr1 : right1.at i <;>
        cases hl2 : left2.at i <;> cases hr2 : right2.at i <;>
        simp_all
    · have hge : n ≤ i := by omega
      exact (bitVec_at_false_of_ge right1 i hge).trans
        (bitVec_at_false_of_ge right2 i hge).symm

/-! ## 2. The source-specific path-safe code -/

def exceptionalPathSafe
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Nat → Bool :=
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  pathSafe Gamma path.indexWalk.vertices

def exceptionalPathSafeCarrierCode
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OccCarrierXiCodeAt Gamma :=
  exceptionalResidualRoutedCarrierCode Gamma qP b1 b2
    (exceptionalPathSafe Gamma qP b1 b2 entry) entry

theorem exceptionalPathSafeCarrierCode_mem
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    exceptionalPathSafeCarrierCode Gamma qP b1 b2 entry ∈
      occurrenceCarrierXiCodes Gamma :=
  exceptionalResidualRoutedCarrierCode_mem Gamma qP b1 b2
    (exceptionalPathSafe Gamma qP b1 b2 entry) entry

private theorem switched_at_left
    (Gamma : List (Polymer L)) (b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length) (i : Nat) (hi : i < Gamma.length) :
    (switchedBranchCode Gamma b2 pair).1.at i =
      switchedLeft Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i := by
  unfold switchedBranchCode
  simpa using bitsFromMask_at Gamma.length _ 0 i hi

private theorem switched_at_right
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

private theorem exceptional_switched_path_first_left
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    let pair := entry.1
    let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
    let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
    let leftF := switchedLeft Gamma.length (incAtDistinct Gamma)
      (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2)
    let rightF := switchedRight Gamma.length (incAtDistinct Gamma)
      (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2)
    match path.indexWalk.vertices with
    | [] => False
    | i :: _ => leftF i = true ∧ rightF i = false := by
  dsimp only
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  have hs := exceptional_switched_path_start_left Gamma qP b1 b2 entry
  exact first_side_of_walk path.indexWalk _ _ hs

/-! ## 3. Unconditional decoder and injection -/

theorem exceptionalPathSafeCarrierCode_injective
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry1 entry2 : ExceptionalSourceEntry Gamma qP b1 b2)
    (hcode : exceptionalPathSafeCarrierCode Gamma qP b1 b2 entry1 =
      exceptionalPathSafeCarrierCode Gamma qP b1 b2 entry2) :
    entry1 = entry2 := by
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
  let leftResidual1 := residualBits pathBits1 switched1.1
  let leftResidual2 := residualBits pathBits2 switched2.1
  let rightResidual1 := residualBits pathBits1 switched1.2
  let rightResidual2 := residualBits pathBits2 switched2.2
  let safe1 := exceptionalPathSafe Gamma qP b1 b2 entry1
  let safe2 := exceptionalPathSafe Gamma qP b1 b2 entry2
  have hverticesRaw := congrArg
    (fun code => occurrenceChainVertices code.carrier.start code.carrier.chain)
    hcode
  have hvertices : path1.indexWalk.vertices = path2.indexWalk.vertices := by
    simpa [exceptionalPathSafeCarrierCode,
      exceptionalResidualRoutedCarrierCode, exceptionalCustomCarrierCode,
      occurrenceChainVertices_ofWalk] using hverticesRaw
  have hsafe : safe1 = safe2 := by
    unfold safe1 safe2 exceptionalPathSafe
    dsimp only
    funext i
    rw [hvertices]
  have hbackgroundRaw := congrArg
    (fun code => terminalBackground code.carrier.chain) hcode
  have hbackground : routedBackground safe1 leftResidual1 =
      routedBackground safe2 leftResidual2 := by
    simpa [exceptionalPathSafeCarrierCode,
      exceptionalResidualRoutedCarrierCode, exceptionalCustomCarrierCode,
      terminalBackground_occurrenceChainCodeOfWalk] using hbackgroundRaw
  have hexternal : routedExternal safe1 leftResidual1 rightResidual1 =
      routedExternal safe2 leftResidual2 rightResidual2 := by
    simpa [exceptionalPathSafeCarrierCode,
      exceptionalResidualRoutedCarrierCode, exceptionalCustomCarrierCode]
      using congrArg (fun code => code.external) hcode
  rw [← hsafe] at hbackground hexternal
  have hroute : routedMaskPair safe1 leftResidual1 rightResidual1 =
      routedMaskPair safe1 leftResidual2 rightResidual2 :=
    Prod.ext hbackground hexternal
  have hcross12 : ∀ i, i < Gamma.length → safe1 i = false →
      leftResidual1.at i = true → rightResidual2.at i = true → False := by
    intro i hi hunsafe hleft hright
    exact exceptional_unsafe_cross_side_impossible Gamma qP b1 b2
      entry1 entry2 hvertices i hi
      (by simpa [safe1, exceptionalPathSafe] using hunsafe) hleft hright
  have hcross21 : ∀ i, i < Gamma.length → safe1 i = false →
      leftResidual2.at i = true → rightResidual1.at i = true → False := by
    intro i hi hunsafe hleft hright
    have hunsafe2 : pathSafe Gamma path2.indexWalk.vertices i = false := by
      rw [← hvertices]
      simpa [safe1, exceptionalPathSafe] using hunsafe
    exact exceptional_unsafe_cross_side_impossible Gamma qP b1 b2
      entry2 entry1 hvertices.symm i hi hunsafe2 hleft hright
  have hresidualPair := routedMaskPair_injective_of_unsafe_cross safe1
    leftResidual1 rightResidual1 leftResidual2 rightResidual2
    hcross12 hcross21 hroute
  have hleftResidual : leftResidual1 = leftResidual2 :=
    congrArg Prod.fst hresidualPair
  have hrightResidual : rightResidual1 = rightResidual2 :=
    congrArg Prod.snd hresidualPair
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
  have hfirst1 := exceptional_switched_path_first_left Gamma qP b1 b2 entry1
  have hfirst2 := exceptional_switched_path_first_left Gamma qP b1 b2 entry2
  change (match path1.indexWalk.vertices with
    | [] => False
    | i :: _ => leftF1 i = true ∧ rightF1 i = false) at hfirst1
  change (match path2.indexWalk.vertices with
    | [] => False
    | i :: _ => leftF2 i = true ∧ rightF2 i = false) at hfirst2
  have hfirst : match path1.indexWalk.vertices with
      | [] => True
      | i :: _ => leftF1 i = leftF2 i ∧ rightF1 i = rightF2 i := by
    cases hv : path1.indexWalk.vertices with
    | nil => exact True.intro
    | cons i rest =>
        rw [hv] at hfirst1
        rw [← hvertices, hv] at hfirst2
        exact ⟨hfirst1.1.trans hfirst2.1.symm,
          hfirst1.2.trans hfirst2.2.symm⟩
  have hpathSides := alternatingSides_unique leftF1 rightF1 leftF2 rightF2
    path1.indexWalk.vertices halt1 halt2 hfirst
  have hswitchedAt : ∀ i, i < Gamma.length →
      switched1.1.at i = switched2.1.at i ∧
        switched1.2.at i = switched2.2.at i := by
    intro i hi
    cases hipath : decide (i ∈ path1.indexWalk.vertices) with
    | true =>
        have hiPath : i ∈ path1.indexWalk.vertices := of_decide_eq_true hipath
        have hsides := hpathSides i hiPath
        rw [switched_at_left Gamma b2 pair1 i hi,
          switched_at_left Gamma b2 pair2 i hi,
          switched_at_right Gamma b2 pair1 i hi,
          switched_at_right Gamma b2 pair2 i hi]
        exact hsides
    | false =>
        have hiNotPath : ¬ i ∈ path1.indexWalk.vertices :=
          of_decide_eq_false hipath
        have hiNotPath2 : ¬ i ∈ path2.indexWalk.vertices := by
          intro hi2
          apply hiNotPath
          rw [hvertices]
          exact hi2
        have hleftAt := congrArg (fun bits => bits.at i) hleftResidual
        have hrightAt := congrArg (fun bits => bits.at i) hrightResidual
        change (residualBits pathBits1 switched1.1).at i =
          (residualBits pathBits2 switched2.1).at i at hleftAt
        change (residualBits pathBits1 switched1.2).at i =
          (residualBits pathBits2 switched2.2).at i at hrightAt
        rw [residualBits_at pathBits1 switched1.1 i hi,
          residualBits_at pathBits2 switched2.1 i hi] at hleftAt
        rw [residualBits_at pathBits1 switched1.2 i hi,
          residualBits_at pathBits2 switched2.2 i hi] at hrightAt
        have hp1 : pathBits1.at i = false := by
          unfold pathBits1
          rw [pathOccurrenceBits_at Gamma.length path1.indexWalk.vertices i hi]
          exact decide_eq_false hiNotPath
        have hp2 : pathBits2.at i = false := by
          unfold pathBits2
          rw [pathOccurrenceBits_at Gamma.length path2.indexWalk.vertices i hi]
          exact decide_eq_false hiNotPath2
        simpa [hp1, hp2] using And.intro hleftAt hrightAt
  have hswitch : switched1 = switched2 := by
    apply Prod.ext
    · apply BitVec.ext
      intro i
      by_cases hi : i < Gamma.length
      · exact (hswitchedAt i hi).1
      · have hge : Gamma.length ≤ i := by omega
        exact (bitVec_at_false_of_ge switched1.1 i hge).trans
          (bitVec_at_false_of_ge switched2.1 i hge).symm
    · apply BitVec.ext
      intro i
      by_cases hi : i < Gamma.length
      · exact (hswitchedAt i hi).2
      · have hge : Gamma.length ≤ i := by omega
        exact (bitVec_at_false_of_ge switched1.2 i hge).trans
          (bitVec_at_false_of_ge switched2.2 i hge).symm
  have hpairs := switchedBranchCode_injective_on_source Gamma qP b1 b2
    pair1 pair2 entry1.2 entry2.2 hswitch
  exact Subtype.ext hpairs

#print axioms routedMaskPair_injective_of_unsafe_cross
#print axioms exceptionalPathSafeCarrierCode_mem
#print axioms exceptionalPathSafeCarrierCode_injective

end YMGap.Continuum.XiExceptionalPathSafeInjection
