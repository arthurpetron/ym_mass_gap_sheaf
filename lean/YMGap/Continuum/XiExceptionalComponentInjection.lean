/-
# Injectivity of the residual-component carrier

Equality of corrected carrier codes first recovers the common decoded path.
On the right-safe branch, reverse residual-component recovery then recovers
both residual switched masks.  Alternating path sides recover the deleted
path bits, and the already-proved source switch decoder recovers the original
exceptional source entry.
-/

import YMGap.Continuum.XiExceptionalComponentExactWeight

namespace YMGap.Continuum.XiExceptionalComponentInjection

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
open YMGap.Continuum.XiExceptionalPathSideDecoder
open YMGap.Continuum.XiExceptionalPathSafeInjection
open YMGap.Continuum.XiAdmissibleSourceSwitch
open YMGap.Continuum.XiNonexceptionalTargetValidity
open YMGap.Continuum.XiExceptionalComponentRouter
open YMGap.Continuum.XiExceptionalComponentCarrier

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

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

private theorem residual_compatible
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
  exact ⟨familyCompatibleB_of_sublist
      (residual_sub_switched Gamma pathBits switched.1)
      (switched_left_family_compatible Gamma qP b1 b2 pair afacts),
    familyCompatibleB_of_sublist
      (residual_sub_switched Gamma pathBits switched.2)
      (switched_right_family_compatible Gamma qP b1 b2 pair afacts)⟩

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
  exact first_side_of_walk path.indexWalk _ _
    (exceptional_switched_path_start_left Gamma qP b1 b2 entry)

theorem exceptionalComponentCarrierCode_injective_of_rightSafe
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry1 entry2 : ExceptionalSourceEntry Gamma qP b1 b2)
    (hright1 : componentRightSafe Gamma qP b1 b2 entry1)
    (hright2 : componentRightSafe Gamma qP b1 b2 entry2)
    (hcode : exceptionalComponentCarrierCode Gamma qP b1 b2 entry1 =
      exceptionalComponentCarrierCode Gamma qP b1 b2 entry2) :
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
    simpa [exceptionalComponentCarrierCode, exceptionalCustomCarrierCode,
      occurrenceChainVertices_ofWalk] using hverticesRaw
  have hsafe : safe1 = safe2 := by
    unfold safe1 safe2 exceptionalPathSafe
    dsimp only
    funext i
    rw [hvertices]
  have hbackgroundRaw := congrArg
    (fun code => terminalBackground code.carrier.chain) hcode
  have hbackground :
      componentBackground Gamma safe1 leftResidual1 rightResidual1 =
        componentBackground Gamma safe2 leftResidual2 rightResidual2 := by
    simpa [exceptionalComponentCarrierCode, exceptionalCustomCarrierCode,
      terminalBackground_occurrenceChainCodeOfWalk] using hbackgroundRaw
  have hexternal :
      componentExternal Gamma safe1 leftResidual1 rightResidual1 =
        componentExternal Gamma safe2 leftResidual2 rightResidual2 := by
    simpa [exceptionalComponentCarrierCode, exceptionalCustomCarrierCode]
      using congrArg (fun code => code.external) hcode
  rw [← hsafe] at hbackground hexternal
  have hcompat1 := residual_compatible Gamma qP b1 b2 entry1
  have hcompat2 := residual_compatible Gamma qP b1 b2 entry2
  change familyCompatibleB (selectByBits Gamma leftResidual1) = true ∧
      familyCompatibleB (selectByBits Gamma rightResidual1) = true at hcompat1
  change familyCompatibleB (selectByBits Gamma leftResidual2) = true ∧
      familyCompatibleB (selectByBits Gamma rightResidual2) = true at hcompat2
  have hrightSafe1 : ∀ i, i < Gamma.length → rightResidual1.at i = true →
      safe1 i = true := by
    simpa [componentRightSafe, pair1, facts1, path1, pathBits1, switched1,
      rightResidual1, safe1] using hright1
  have hrightSafe2 : ∀ i, i < Gamma.length → rightResidual2.at i = true →
      safe1 i = true := by
    have hout : ∀ i, i < Gamma.length → rightResidual2.at i = true →
        safe2 i = true := by
      simpa [componentRightSafe, pair2, facts2, path2, pathBits2, switched2,
        rightResidual2, safe2] using hright2
    rw [hsafe]
    exact hout
  have hresidualPair := component_pair_injective_of_right_safe Gamma safe1
    leftResidual1 rightResidual1 leftResidual2 rightResidual2
    hcompat1.1 hcompat1.2 hrightSafe1 hcompat2.1 hcompat2.2 hrightSafe2
    (Prod.ext hbackground hexternal)
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
        rw [switchedCode_at_left Gamma b2 pair1 i hi,
          switchedCode_at_left Gamma b2 pair2 i hi,
          switchedCode_at_right Gamma b2 pair1 i hi,
          switchedCode_at_right Gamma b2 pair2 i hi]
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

#print axioms exceptionalComponentCarrierCode_injective_of_rightSafe

end YMGap.Continuum.XiExceptionalComponentInjection
