/-
# Injection of the original left-residual carrier

This is the side-symmetric reconstruction theorem.  The carrier stores the
ordered canonical path and the original cleared left residual; when the
original right residual is empty, alternating path sides and the bad
left-only endpoint reconstruct the complete exceptional source.
-/

import YMGap.Continuum.XiExceptionalOriginalResidualInjection
import YMGap.Continuum.XiExceptionalSymmetricResidualBlock

namespace YMGap.Continuum.XiExceptionalSymmetricResidualInjection

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
open YMGap.Continuum.XiExceptionalOriginalResidualInjection
open YMGap.Continuum.XiExceptionalSymmetricResidualBlock

variable {L : Lattice} [DecidableEq L.Plaquette]

def originalLeftResidualCarrierCode
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OccCarrierXiCodeAt Gamma :=
  parallelExternalCarrierCode Gamma qP b1 b2 entry
    (leftPathResidual Gamma qP b1 b2 entry)

theorem originalLeftResidualCarrierCode_injective
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry1 entry2 : ExceptionalSourceEntry Gamma qP b1 b2)
    (hright1 : selectByBits Gamma
      (rightPathResidual Gamma qP b1 b2 entry1) = [])
    (hright2 : selectByBits Gamma
      (rightPathResidual Gamma qP b1 b2 entry2) = [])
    (hcode : originalLeftResidualCarrierCode Gamma qP b1 b2 entry1 =
      originalLeftResidualCarrierCode Gamma qP b1 b2 entry2) :
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
    simpa [originalLeftResidualCarrierCode, parallelExternalCarrierCode,
      exceptionalCustomCarrierCode, occurrenceChainVertices_ofWalk]
      using hverticesRaw
  have hseedRaw := congrArg
    (fun code => occurrenceChainEnd code.carrier.start code.carrier.chain)
    hcode
  have hseed : path1.seed = path2.seed := by
    simpa [originalLeftResidualCarrierCode, parallelExternalCarrierCode,
      exceptionalCustomCarrierCode, occurrenceChainEnd_ofWalk]
      using hseedRaw
  have hleftResidual : leftResidual1 = leftResidual2 := by
    simpa [originalLeftResidualCarrierCode, parallelExternalCarrierCode,
      exceptionalCustomCarrierCode] using
        congrArg (fun code => code.external) hcode
  have hrightResidual1 : rightResidual1 = emptyOccurrenceBits Gamma := by
    exact bitVec_eq_empty_of_select_eq_nil Gamma rightResidual1 hright1
  have hrightResidual2 : rightResidual2 = emptyOccurrenceBits Gamma := by
    exact bitVec_eq_empty_of_select_eq_nil Gamma rightResidual2 hright2
  have hrightResidual : rightResidual1 = rightResidual2 :=
    hrightResidual1.trans hrightResidual2.symm
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
    | true => exact hpathSides i (of_decide_eq_true hipath)
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

#print axioms originalLeftResidualCarrierCode_injective

end YMGap.Continuum.XiExceptionalSymmetricResidualInjection
