/-
# Exact two-sided carrier for a path-safe original left residual

The canonical exceptional path leaves two original-side residual families.
When the left residual is compatible with every path vertex, the ordinary
carrier already has exactly the two required slots: put the left residual in
the terminal background and the right residual in the external family.  Both
families inherit internal compatibility and `qP`-admissibility from their
source sides.  The resulting target has exactly the source weight.

Unlike the one-sided predecessors, the code stores both residual masks.
Together with the ordered alternating path they reconstruct the complete
source without an empty-side premise.
-/

import YMGap.Continuum.XiExceptionalResidualSourceSplit

namespace YMGap.Continuum.XiExceptionalTwoSidedOriginalCarrier

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalCustomCarrier
open YMGap.Continuum.XiExceptionalTargetBlocks
open YMGap.Continuum.XiExceptionalPathMaskAlgebra
open YMGap.Continuum.XiExceptionalPathSideDecoder
open YMGap.Continuum.XiExceptionalParallelExternalFamily
open YMGap.Continuum.XiExceptionalParallelSourceSide
open YMGap.Continuum.XiExceptionalParallelResidualBlock
open YMGap.Continuum.XiExceptionalOneAttachedResidualConsumer
open YMGap.Continuum.XiExceptionalOriginalResidualInjection
open YMGap.Continuum.XiExceptionalResidualSourceSplit

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

def originalTwoSidedCarrierCode
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    OccCarrierXiCodeAt Gamma :=
  exceptionalCustomCarrierCode Gamma qP b1 b2 entry
    (leftPathResidual Gamma qP b1 b2 entry)
    (rightPathResidual Gamma qP b1 b2 entry)

theorem originalTwoSidedCarrierCode_mem
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    originalTwoSidedCarrierCode Gamma qP b1 b2 entry ∈
      occurrenceCarrierXiCodes Gamma :=
  exceptionalCustomCarrierCode_mem Gamma qP b1 b2 entry _ _

theorem leftPathResidual_submask_left
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : ∀ i,
    (leftPathResidual Gamma qP b1 b2 entry).at i = true →
      entry.1.1.at i = true := by
  intro i hres
  cases hlt : decide (i < Gamma.length) with
  | true =>
      have hi := of_decide_eq_true hlt
      rw [leftPathResidual_at Gamma qP b1 b2 entry i hi] at hres
      exact ((Bool.and_eq_true _ _).mp hres).2
  | false =>
      have hnlt : ¬ i < Gamma.length := of_decide_eq_false hlt
      have hout := bitVec_at_false_of_ge
        (leftPathResidual Gamma qP b1 b2 entry) i (by omega)
      rw [hres] at hout
      cases hout

/-- The sole geometric condition for the two-sided original carrier: every
left residual occurrence is compatible with every canonical-path vertex. -/
def OriginalLeftResidualPathSafe
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) : Prop :=
  let pair := entry.1
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 pair entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 pair facts
  ∀ X, X ∈ path.polymerWalk.vertices →
    ∀ T, T ∈ selectByBits Gamma
      (leftPathResidual Gamma qP b1 b2 entry) →
      compatibleB X T = true

/-- Exact source weight in the unchanged ordinary carrier target. -/
theorem originalTwoSidedCarrierCode_weight_eqv_source
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Gamma : List (Polymer L)) (label : L.Plaquette → Rep)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hsafe : OriginalLeftResidualPathSafe Gamma qP b1 b2 entry) :
    occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label
        (originalTwoSidedCarrierCode Gamma qP b1 b2 entry) ≈
      occurrencePairWeight w qP b1 b2 Gamma label entry.1 := by
  let leftResidual := leftPathResidual Gamma qP b1 b2 entry
  let rightResidual := rightPathResidual Gamma qP b1 b2 entry
  have hleftSub : ∀ i, leftResidual.at i = true →
      entry.1.1.at i = true :=
    leftPathResidual_submask_left Gamma qP b1 b2 entry
  have hrightSub : ∀ i, rightResidual.at i = true →
      entry.1.2.at i = true :=
    rightPathResidual_submask_right Gamma qP b1 b2 entry
  have hcode := exceptionalCustomCarrierCode_weight_eqv
    w qP b1 b2 Gamma label entry leftResidual rightResidual
    (exceptional_left_submask_compatible Gamma qP b1 b2 entry
      leftResidual hleftSub)
    (exceptional_left_submask_q Gamma qP b1 b2 entry
      leftResidual hleftSub)
    hsafe
    (exceptional_right_submask_compatible Gamma qP b1 b2 entry
      rightResidual hrightSub)
    (exceptional_right_submask_q Gamma qP b1 b2 entry
      rightResidual hrightSub)
  have hsource := occurrencePairWeight_eqv_original_path_residuals
    w qP b1 b2 Gamma label entry
  dsimp only at hcode hsource
  unfold originalTwoSidedCarrierCode
  exact Q'.eqv_trans _ _ _ hcode
    (Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv _ _ _) (Q'.eqv_symm hsource))

/-! ## Reconstruction from the ordered path and both residual masks -/

theorem originalTwoSidedCarrierCode_injective
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry1 entry2 : ExceptionalSourceEntry Gamma qP b1 b2)
    (hcode : originalTwoSidedCarrierCode Gamma qP b1 b2 entry1 =
      originalTwoSidedCarrierCode Gamma qP b1 b2 entry2) :
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
    simpa [originalTwoSidedCarrierCode, exceptionalCustomCarrierCode,
      occurrenceChainVertices_ofWalk] using hverticesRaw
  have hseedRaw := congrArg
    (fun code => occurrenceChainEnd code.carrier.start code.carrier.chain)
    hcode
  have hseed : path1.seed = path2.seed := by
    simpa [originalTwoSidedCarrierCode, exceptionalCustomCarrierCode,
      occurrenceChainEnd_ofWalk] using hseedRaw
  have hleftResidual : leftResidual1 = leftResidual2 := by
    simpa [originalTwoSidedCarrierCode, exceptionalCustomCarrierCode,
      terminalBackground_occurrenceChainCodeOfWalk] using
        congrArg (fun code => terminalBackground code.carrier.chain) hcode
  have hrightResidual : rightResidual1 = rightResidual2 := by
    simpa [originalTwoSidedCarrierCode, exceptionalCustomCarrierCode] using
      congrArg (fun code => code.external) hcode
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

/-! ## Duplicate-free regional summation -/

private theorem flatMap_singleton_eq_map {alpha beta : Type}
    (f : alpha → beta) : ∀ xs : List alpha,
    xs.flatMap (fun x => [f x]) = xs.map f
  | [] => rfl
  | x :: xs => by
      simp only [List.flatMap_cons, List.map_cons, List.singleton_append]
      rw [flatMap_singleton_eq_map f xs]

theorem originalTwoSidedPathSafe_region_global_bound
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (source : List (ExceptionalSourceEntry Gamma qP b1 b2))
    (hsource : source.Nodup)
    (hsafe : ∀ entry, entry ∈ source →
      OriginalLeftResidualPathSafe Gamma qP b1 b2 entry) :
    qListSum (fun entry => occurrencePairWeight w qP b1 b2 Gamma label
        entry.1) source ≤
      qListSum (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
        (occurrenceCarrierXiCodes Gamma) := by
  apply qListSum_le_of_disjoint_blocks source
    (occurrenceCarrierXiCodes Gamma)
    (fun entry => occurrencePairWeight w qP b1 b2 Gamma label entry.1)
    (occurrenceCarrierXiCodeWeight w qP b1 b2 Gamma label)
    (fun entry => [originalTwoSidedCarrierCode Gamma qP b1 b2 entry])
  · rw [flatMap_singleton_eq_map]
    apply nodup_map_of_injOn _ source hsource
    intro a _ b _ hcode
    exact originalTwoSidedCarrierCode_injective Gamma qP b1 b2 a b hcode
  · intro code hcode
    obtain ⟨entry, _, hsingleton⟩ := List.mem_flatMap.mp hcode
    rw [List.mem_singleton] at hsingleton
    subst code
    exact originalTwoSidedCarrierCode_mem Gamma qP b1 b2 entry
  · intro entry hentry
    simp only [qListSum_cons, qListSum_nil, Q'.add_zero']
    exact Q'.ge_of_eqv (originalTwoSidedCarrierCode_weight_eqv_source
      w qP b1 b2 Gamma label entry (hsafe entry hentry))
  · intro code _
    exact occurrenceCarrierXiCodeWeight_nonnegative hw
      qP b1 b2 Gamma label code

#print axioms originalTwoSidedCarrierCode_mem
#print axioms leftPathResidual_submask_left
#print axioms originalTwoSidedCarrierCode_weight_eqv_source
#print axioms originalTwoSidedCarrierCode_injective
#print axioms originalTwoSidedPathSafe_region_global_bound

end YMGap.Continuum.XiExceptionalTwoSidedOriginalCarrier
