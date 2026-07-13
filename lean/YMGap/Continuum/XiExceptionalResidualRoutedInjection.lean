/-
# Injectivity of the exact-weight residual router

The routed masks recover every off-path switched bit.  The carrier chain
recovers the ordered path, and its alternating-side decoder recovers the
cleared on-path bits.  Together these reconstruct the complete switched pair
and hence the original exceptional source entry.
-/

import YMGap.Continuum.XiExceptionalPathSideDecoder

namespace YMGap.Continuum.XiExceptionalResidualRoutedInjection

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

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

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

theorem exceptionalResidualRoutedCarrierCode_injective
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (safe : Nat → Bool)
    (entry1 entry2 : ExceptionalSourceEntry Gamma qP b1 b2)
    (hrightSafe1 :
      let pair := entry1.1
      let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry1.2
      let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
      let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
      let switched := switchedBranchCode Gamma b2 pair
      let rightResidual := residualBits pathBits switched.2
      ∀ i, i < Gamma.length → rightResidual.at i = true → safe i = true)
    (hrightSafe2 :
      let pair := entry2.1
      let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry2.2
      let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
      let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
      let switched := switchedBranchCode Gamma b2 pair
      let rightResidual := residualBits pathBits switched.2
      ∀ i, i < Gamma.length → rightResidual.at i = true → safe i = true)
    (hcode :
      exceptionalResidualRoutedCarrierCode Gamma qP b1 b2 safe entry1 =
        exceptionalResidualRoutedCarrierCode Gamma qP b1 b2 safe entry2) :
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
  dsimp only at hrightSafe1 hrightSafe2
  have hverticesRaw := congrArg
    (fun code => occurrenceChainVertices code.carrier.start code.carrier.chain)
    hcode
  have hvertices : path1.indexWalk.vertices = path2.indexWalk.vertices := by
    simpa [exceptionalResidualRoutedCarrierCode,
      exceptionalCustomCarrierCode, occurrenceChainVertices_ofWalk] using
      hverticesRaw
  have hbackgroundRaw := congrArg
    (fun code => terminalBackground code.carrier.chain) hcode
  have hbackground :
      routedBackground safe leftResidual1 =
        routedBackground safe leftResidual2 := by
    simpa [exceptionalResidualRoutedCarrierCode,
      exceptionalCustomCarrierCode,
      terminalBackground_occurrenceChainCodeOfWalk] using hbackgroundRaw
  have hexternal :
      routedExternal safe leftResidual1 rightResidual1 =
        routedExternal safe leftResidual2 rightResidual2 := by
    simpa [exceptionalResidualRoutedCarrierCode,
      exceptionalCustomCarrierCode] using
      congrArg (fun code => code.external) hcode
  have hroute : routedMaskPair safe leftResidual1 rightResidual1 =
      routedMaskPair safe leftResidual2 rightResidual2 := by
    exact Prod.ext hbackground hexternal
  have hresidualPair := routedMaskPair_injective_of_right_safe safe
    leftResidual1 rightResidual1 leftResidual2 rightResidual2
    hrightSafe1 hrightSafe2 hroute
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

#print axioms exceptionalResidualRoutedCarrierCode_injective

end YMGap.Continuum.XiExceptionalResidualRoutedInjection
