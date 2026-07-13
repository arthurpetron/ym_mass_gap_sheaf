/-
# Injection of the original right-residual carrier

For a right-only original residual source, the target code stores enough data
to reconstruct the source without requiring the residual mask alone to be
injective.  Its chain stores the ordered canonical path.  Original source
sides alternate on that path, and the terminal bad seed is left-only, so the
ordered path recovers every cleared path bit.  Off the path, the empty left
residual and stored right residual recover the remaining bits.
-/

import YMGap.Continuum.XiExceptionalOneAttachedResidualConsumer
import YMGap.Continuum.XiExceptionalPathSideDecoder

namespace YMGap.Continuum.XiExceptionalOriginalResidualInjection

open YMGap.Continuum.PolymerModel
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalCustomCarrier
open YMGap.Continuum.XiExceptionalPathMaskAlgebra
open YMGap.Continuum.XiExceptionalPathSideDecoder
open YMGap.Continuum.XiExceptionalParallelExternalFamily
open YMGap.Continuum.XiExceptionalParallelResidualBlock
open YMGap.Continuum.XiExceptionalOneAttachedResidualConsumer

variable {L : Lattice} [DecidableEq L.Plaquette]

/-! ## 1. Recovering the chain endpoint and empty bit masks -/

def occurrenceChainEnd (start : Nat) : OccChainCode n → Nat
  | .terminal _ => start
  | .step next rest => occurrenceChainEnd next rest

theorem occurrenceChainEnd_ofWalk
    {edge : Nat → Nat → Bool} {i j : Nat}
    (walk : CWalk edge i j) (background : OccBitVec n) :
    occurrenceChainEnd i (occurrenceChainCodeOfWalk walk background) = j := by
  induction walk with
  | single _ => rfl
  | cons _ rest ih => exact ih

private theorem bitsFromFalse_offset_eq : ∀ (n a b : Nat),
    bitsFromMask n (fun _ => false) a =
      bitsFromMask n (fun _ => false) b
  | 0, _, _ => rfl
  | n + 1, a, b => by
      simp only [bitsFromMask]
      exact congrArg (XiExceptionalOccurrenceCodes.BitVec.cons false)
        (bitsFromFalse_offset_eq n (a + 1) (b + 1))

theorem bitVec_eq_empty_of_select_eq_nil :
    ∀ (Gamma : List (Polymer L)) (bits : OccBitVec Gamma.length),
      selectByBits Gamma bits = [] → bits = emptyOccurrenceBits Gamma
  | [], .nil, _ => rfl
  | X :: Gamma, .cons false tail, h => by
      simp only [selectByBits, Bool.false_eq_true, ↓reduceIte] at h
      have ht := bitVec_eq_empty_of_select_eq_nil Gamma tail h
      rw [ht]
      unfold emptyOccurrenceBits
      simp only [List.length_cons, bitsFromMask]
      exact congrArg (XiExceptionalOccurrenceCodes.BitVec.cons false)
        (bitsFromFalse_offset_eq Gamma.length 0 (0 + 1))
  | X :: Gamma, .cons true tail, h => by
      simp only [selectByBits, ↓reduceIte] at h
      cases h

/-! ## 2. Alternating sides are determined from the endpoint -/

def EndSameSides (left1 right1 left2 right2 : Nat → Bool) :
    List Nat → Prop
  | [] => True
  | [i] => left1 i = left2 i ∧ right1 i = right2 i
  | _ :: j :: rest => EndSameSides left1 right1 left2 right2 (j :: rest)

theorem endSameSides_of_walk
    (left1 right1 left2 right2 : Nat → Bool) :
    ∀ {edge : Nat → Nat → Bool} {i j : Nat} (walk : CWalk edge i j),
      (left1 j = left2 j ∧ right1 j = right2 j) →
      EndSameSides left1 right1 left2 right2 walk.vertices
  | _, _, _, .single _, h => h
  | _, _, _, .cons hedge rest, h => by
      cases rest with
      | single _ => exact h
      | cons hnext tail =>
          exact endSameSides_of_walk left1 right1 left2 right2
            (.cons hnext tail) h

private theorem opposite_source_unique
    (li1 ri1 li2 ri2 lj1 rj1 lj2 rj2 : Bool)
    (htarget : lj1 = lj2 ∧ rj1 = rj2)
    (hop1 : OppositeSides li1 ri1 lj1 rj1)
    (hop2 : OppositeSides li2 ri2 lj2 rj2) :
    li1 = li2 ∧ ri1 = ri2 := by
  rcases hop1 with
      ⟨hli1, hri1, hlj1, hrj1⟩ |
      ⟨hli1, hri1, hlj1, hrj1⟩ <;>
    rcases hop2 with
      ⟨hli2, hri2, hlj2, hrj2⟩ |
      ⟨hli2, hri2, hlj2, hrj2⟩
  · exact ⟨hli1.trans hli2.symm, hri1.trans hri2.symm⟩
  · have hfalseTrue : false = true :=
      hlj1.symm.trans (htarget.1.trans hlj2)
    exact absurd hfalseTrue Bool.false_ne_true
  · have htrueFalse : true = false :=
      hlj1.symm.trans (htarget.1.trans hlj2)
    exact absurd htrueFalse (fun h => Bool.false_ne_true h.symm)
  · exact ⟨hli1.trans hli2.symm, hri1.trans hri2.symm⟩

theorem alternatingSides_unique_from_end
    (left1 right1 left2 right2 : Nat → Bool) :
    ∀ (vertices : List Nat),
      AlternatingSides left1 right1 vertices →
      AlternatingSides left2 right2 vertices →
      EndSameSides left1 right1 left2 right2 vertices →
      ∀ i, i ∈ vertices →
        left1 i = left2 i ∧ right1 i = right2 i
  | [], _, _, _, _, hi => by cases hi
  | [x], _, _, hend, i, hi => by
      rw [List.mem_singleton.mp hi]
      exact hend
  | x :: y :: rest, halt1, halt2, hend, i, hi => by
      have htail := alternatingSides_unique_from_end left1 right1 left2 right2
        (y :: rest) halt1.2 halt2.2 hend
      have hy := htail y List.mem_cons_self
      have hx := opposite_source_unique _ _ _ _ _ _ _ _ hy
        halt1.1 halt2.1
      rcases List.mem_cons.mp hi with hix | hitail
      · rw [hix]
        exact hx
      · exact htail i hitail

/-! ## 3. Original-source reconstruction -/

def originalRightResidualCarrierCode
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OccCarrierXiCodeAt Gamma :=
  parallelExternalCarrierCode Gamma qP b1 b2 entry
    (rightPathResidual Gamma qP b1 b2 entry)

/-- The ordered canonical path together with the original cleared right mask
is injective on sources whose original cleared left mask is empty. -/
theorem originalRightResidualCarrierCode_injective
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry1 entry2 : ExceptionalSourceEntry Gamma qP b1 b2)
    (hleft1 : selectByBits Gamma
      (leftPathResidual Gamma qP b1 b2 entry1) = [])
    (hleft2 : selectByBits Gamma
      (leftPathResidual Gamma qP b1 b2 entry2) = [])
    (hcode : originalRightResidualCarrierCode Gamma qP b1 b2 entry1 =
      originalRightResidualCarrierCode Gamma qP b1 b2 entry2) :
    entry1 = entry2 := by
  let pair1 := entry1.1
  let pair2 := entry2.1
  let facts1 := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair1 entry1.2
  let facts2 := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair2 entry2.2
  let path1 := sourceExceptionalPath Gamma qP b1 b2 pair1 facts1
  let path2 := sourceExceptionalPath Gamma qP b1 b2 pair2 facts2
  let pathBits1 := pathOccurrenceBits Gamma.length path1.indexWalk.vertices
  let pathBits2 := pathOccurrenceBits Gamma.length path2.indexWalk.vertices
  let leftResidual1 := leftPathResidual Gamma qP b1 b2 entry1
  let leftResidual2 := leftPathResidual Gamma qP b1 b2 entry2
  let rightResidual1 := rightPathResidual Gamma qP b1 b2 entry1
  let rightResidual2 := rightPathResidual Gamma qP b1 b2 entry2
  have hverticesRaw := congrArg
    (fun code => occurrenceChainVertices code.carrier.start code.carrier.chain)
    hcode
  have hvertices : path1.indexWalk.vertices = path2.indexWalk.vertices := by
    simpa [originalRightResidualCarrierCode, parallelExternalCarrierCode,
      exceptionalCustomCarrierCode, occurrenceChainVertices_ofWalk]
      using hverticesRaw
  have hseedRaw := congrArg
    (fun code => occurrenceChainEnd code.carrier.start code.carrier.chain)
    hcode
  have hseed : path1.seed = path2.seed := by
    simpa [originalRightResidualCarrierCode, parallelExternalCarrierCode,
      exceptionalCustomCarrierCode, occurrenceChainEnd_ofWalk]
      using hseedRaw
  have hrightResidual : rightResidual1 = rightResidual2 := by
    simpa [originalRightResidualCarrierCode, parallelExternalCarrierCode,
      exceptionalCustomCarrierCode] using
        congrArg (fun code => code.external) hcode
  have hleftResidual1 : leftResidual1 = emptyOccurrenceBits Gamma := by
    exact bitVec_eq_empty_of_select_eq_nil Gamma leftResidual1 hleft1
  have hleftResidual2 : leftResidual2 = emptyOccurrenceBits Gamma := by
    exact bitVec_eq_empty_of_select_eq_nil Gamma leftResidual2 hleft2
  have hleftResidual : leftResidual1 = leftResidual2 :=
    hleftResidual1.trans hleftResidual2.symm
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
    leftF1 rightF1 leftF2 rightF2 path1.indexWalk.vertices
    halt1 halt2 hend
  have hpairsAt : ∀ i, i < Gamma.length →
      pair1.1.at i = pair2.1.at i ∧ pair1.2.at i = pair2.2.at i := by
    intro i hi
    cases hipath : decide (i ∈ path1.indexWalk.vertices) with
    | true =>
        exact hpathSides i (of_decide_eq_true hipath)
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
        change (residualBits pathBits1 pair1.1).at i =
          (residualBits pathBits2 pair2.1).at i at hleftAt
        change (residualBits pathBits1 pair1.2).at i =
          (residualBits pathBits2 pair2.2).at i at hrightAt
        rw [residualBits_at pathBits1 pair1.1 i hi,
          residualBits_at pathBits2 pair2.1 i hi] at hleftAt
        rw [residualBits_at pathBits1 pair1.2 i hi,
          residualBits_at pathBits2 pair2.2 i hi] at hrightAt
        have hp1 : pathBits1.at i = false := by
          unfold pathBits1
          rw [pathOccurrenceBits_at Gamma.length path1.indexWalk.vertices i hi]
          exact decide_eq_false hiNotPath
        have hp2 : pathBits2.at i = false := by
          unfold pathBits2
          rw [pathOccurrenceBits_at Gamma.length path2.indexWalk.vertices i hi]
          exact decide_eq_false hiNotPath2
        simpa [hp1, hp2] using And.intro hleftAt hrightAt
  have hpairs : pair1 = pair2 := by
    apply Prod.ext
    · apply BitVec.ext
      intro i
      cases hlt : decide (i < Gamma.length) with
      | true => exact (hpairsAt i (of_decide_eq_true hlt)).1
      | false =>
          have hnlt : ¬ i < Gamma.length := of_decide_eq_false hlt
          exact (bitVec_at_false_of_ge pair1.1 i (by omega)).trans
            (bitVec_at_false_of_ge pair2.1 i (by omega)).symm
    · apply BitVec.ext
      intro i
      cases hlt : decide (i < Gamma.length) with
      | true => exact (hpairsAt i (of_decide_eq_true hlt)).2
      | false =>
          have hnlt : ¬ i < Gamma.length := of_decide_eq_false hlt
          exact (bitVec_at_false_of_ge pair1.2 i (by omega)).trans
            (bitVec_at_false_of_ge pair2.2 i (by omega)).symm
  exact Subtype.ext hpairs

#print axioms occurrenceChainEnd_ofWalk
#print axioms bitVec_eq_empty_of_select_eq_nil
#print axioms alternatingSides_unique_from_end
#print axioms originalRightResidualCarrierCode_injective

end YMGap.Continuum.XiExceptionalOriginalResidualInjection
