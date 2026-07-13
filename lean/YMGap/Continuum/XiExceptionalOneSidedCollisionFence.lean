/-
# Collision between the two one-sided original-residual carriers

An isolated residual occurrence may be placed on either admissible source
side.  Both sources have the same ordered canonical path and the same
path-cleared occurrence mask.  The forward-path right and left external
carriers are therefore the same target code.  This exact public one-ended
example prevents combining the two individually injective maps without an
orientation-distinguishing mechanism.
-/

import YMGap.Continuum.XiExceptionalResidualSourceSplit

namespace YMGap.Continuum.XiExceptionalOneSidedCollisionFence

open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
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
open YMGap.Continuum.XiExceptionalParallelExternalFamily
open YMGap.Continuum.XiExceptionalParallelResidualBlock
open YMGap.Continuum.XiExceptionalOneAttachedResidualConsumer
open YMGap.Continuum.XiExceptionalOriginalResidualInjection
open YMGap.Continuum.XiExceptionalSymmetricResidualInjection

private abbrev TL := toyLattice
private instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance

private def p0 : TL.Plaquette := (0, 0)
private def p1 : TL.Plaquette := (1, 0)
private def p2 : TL.Plaquette := (2, 0)
private def A : Polymer TL := [p0]
private def B : Polymer TL := [p0, p1]
private def E : Polymer TL := [p2]
private def head : Polymer TL := [p1]
private def Gamma : List (Polymer TL) := [A, B, E]
private def qAll : Polymer TL → Bool := fun _ => true
private def markA : Polymer TL → Bool := fun X => decide (X = A)
private def publicBad : Polymer TL → Bool :=
  fun X => !(compatibleB head X)

private def bits3 (x0 x1 x2 : Bool) : OccBitVec 3 :=
  .cons x0 (.cons x1 (.cons x2 .nil))

private def pairLeft : MaskPair Gamma.length :=
  (bits3 false true true, bits3 true false false)

private def pairRight : MaskPair Gamma.length :=
  (bits3 false true false, bits3 true false true)

theorem pairLeft_mem :
    pairLeft ∈ exceptionalSourceCodes Gamma qAll markA publicBad := by
  apply List.mem_filter.mpr
  refine ⟨maskPairs_complete pairLeft, ?_⟩
  rfl

theorem pairRight_mem :
    pairRight ∈ exceptionalSourceCodes Gamma qAll markA publicBad := by
  apply List.mem_filter.mpr
  refine ⟨maskPairs_complete pairRight, ?_⟩
  rfl

def entryLeft : ExceptionalSourceEntry Gamma qAll markA publicBad :=
  ⟨pairLeft, pairLeft_mem⟩

def entryRight : ExceptionalSourceEntry Gamma qAll markA publicBad :=
  ⟨pairRight, pairRight_mem⟩

theorem entries_ne : entryLeft ≠ entryRight := by
  intro h
  have hp := congrArg (fun entry => entry.1.1.at 2) h
  cases hp

private theorem CWalk.end_mem_vertices
    {alpha : Type} {edge : alpha → alpha → Bool} :
    ∀ {x y : alpha} (walk : CWalk edge x y), y ∈ walk.vertices
  | _, _, .single _ => List.mem_cons_self
  | _, _, .cons _ rest =>
      List.mem_cons_of_mem _ (CWalk.end_mem_vertices rest)

private theorem direct_walk
    {edge : Nat → Nat → Bool} {start finish : Nat}
    (walk : CWalk edge start finish)
    (hstart : start = 0) (hfinish : finish = 1)
    (hnodup : walk.vertices.Nodup)
    (hfirst : ∀ j, edge 0 j = true → j = 1) :
    walk.vertices = [0, 1] := by
  subst start
  subst finish
  cases walk with
  | @cons _ next _ hedge rest =>
      have hnext := hfirst next hedge
      subst next
      cases rest with
      | single _ => rfl
      | @cons _ next2 _ hedge2 tail =>
          have hp := List.nodup_cons.mp hnodup
          have htail := List.nodup_cons.mp hp.2
          exact absurd (CWalk.end_mem_vertices tail) htail.1

private theorem bad_index {i : Nat} (hi : i < Gamma.length)
    (hbad : publicBad (polyAt Gamma i) = true) : i = 1 := by
  have hi3 : i < 3 := by simpa [Gamma] using hi
  have h0 : i ≠ 0 := by intro e; subst i; cases hbad
  have h2 : i ≠ 2 := by intro e; subst i; cases hbad
  omega

private theorem left_path_vertices :
    let facts := exceptionalSourceFactsOfMem Gamma qAll markA publicBad
      pairLeft pairLeft_mem
    let path := sourceExceptionalPath Gamma qAll markA publicBad pairLeft facts
    path.indexWalk.vertices = [0, 1] := by
  dsimp only
  let facts := exceptionalSourceFactsOfMem Gamma qAll markA publicBad
    pairLeft pairLeft_mem
  let path := sourceExceptionalPath Gamma qAll markA publicBad pairLeft facts
  have hstart : exceptionalMarkedIndex Gamma markA publicBad pairLeft = 0 := by
    rfl
  have hp := forwardSeed_parts Gamma.length
    (bitMask pairLeft.1) (bitMask pairLeft.2) (predAt Gamma publicBad)
    path.seed_true
  have hfinish : path.seed = 1 := bad_index hp.1 hp.2.2.2
  apply direct_walk path.indexWalk hstart hfinish path.index_nodup
  intro j hedge
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pairLeft.1) (bitMask pairLeft.2) hedge).2
  have hj3 : j < 3 := by simpa [Gamma] using hj
  have h0 : j ≠ 0 := by intro e; subst j; cases hedge
  have h2 : j ≠ 2 := by intro e; subst j; cases hedge
  omega

private theorem right_path_vertices :
    let facts := exceptionalSourceFactsOfMem Gamma qAll markA publicBad
      pairRight pairRight_mem
    let path := sourceExceptionalPath Gamma qAll markA publicBad pairRight facts
    path.indexWalk.vertices = [0, 1] := by
  dsimp only
  let facts := exceptionalSourceFactsOfMem Gamma qAll markA publicBad
    pairRight pairRight_mem
  let path := sourceExceptionalPath Gamma qAll markA publicBad pairRight facts
  have hstart : exceptionalMarkedIndex Gamma markA publicBad pairRight = 0 := by
    rfl
  have hp := forwardSeed_parts Gamma.length
    (bitMask pairRight.1) (bitMask pairRight.2) (predAt Gamma publicBad)
    path.seed_true
  have hfinish : path.seed = 1 := bad_index hp.1 hp.2.2.2
  apply direct_walk path.indexWalk hstart hfinish path.index_nodup
  intro j hedge
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pairRight.1) (bitMask pairRight.2) hedge).2
  have hj3 : j < 3 := by simpa [Gamma] using hj
  have h0 : j ≠ 0 := by intro e; subst j; cases hedge
  have h2 : j ≠ 2 := by intro e; subst j; cases hedge
  omega

private theorem occurrenceChainCodeOfWalk_direct
    {edge : Nat → Nat → Bool} (walk : CWalk edge 0 1)
    (background : OccBitVec n) (hvertices : walk.vertices = [0, 1]) :
    occurrenceChainCodeOfWalk walk background =
      .step 1 (.terminal background) := by
  cases walk with
  | @cons _ next _ hedge rest =>
      have htailVertices : rest.vertices = [1] := by injection hvertices
      have hnext : next = 1 := by
        exact List.mem_singleton.mp (by
          rw [← htailVertices]
          exact CWalk.start_mem_vertices rest)
      subst next
      cases rest with
      | single _ => rfl
      | @cons _ next2 _ hedge2 tail =>
          have hempty : tail.vertices = [] := by
            simp only [CWalk.vertices] at htailVertices
            injection htailVertices
          exact absurd (CWalk.end_mem_vertices tail) (by
            rw [hempty]
            exact List.not_mem_nil)

private theorem left_path_chain :
    let facts := exceptionalSourceFactsOfMem Gamma qAll markA publicBad
      pairLeft pairLeft_mem
    let path := sourceExceptionalPath Gamma qAll markA publicBad pairLeft facts
    occurrenceChainCodeOfWalk path.indexWalk (emptyOccurrenceBits Gamma) =
      .step 1 (.terminal (emptyOccurrenceBits Gamma)) := by
  dsimp only
  have hstart : exceptionalMarkedIndex Gamma markA publicBad pairLeft = 0 := by
    rfl
  have hseed : (sourceExceptionalPath Gamma qAll markA publicBad pairLeft
    (exceptionalSourceFactsOfMem Gamma qAll markA publicBad pairLeft
      pairLeft_mem)).seed = 1 := by
    have hp := forwardSeed_parts Gamma.length
      (bitMask pairLeft.1) (bitMask pairLeft.2) (predAt Gamma publicBad)
      (sourceExceptionalPath Gamma qAll markA publicBad pairLeft
        (exceptionalSourceFactsOfMem Gamma qAll markA publicBad pairLeft
          pairLeft_mem)).seed_true
    exact bad_index hp.1 hp.2.2.2
  exact occurrenceChainCodeOfWalk_direct
    (show CWalk _ 0 1 from hstart ▸ hseed ▸
      (sourceExceptionalPath Gamma qAll markA publicBad pairLeft
        (exceptionalSourceFactsOfMem Gamma qAll markA publicBad pairLeft
          pairLeft_mem)).indexWalk)
    (emptyOccurrenceBits Gamma) left_path_vertices

private theorem right_path_chain :
    let facts := exceptionalSourceFactsOfMem Gamma qAll markA publicBad
      pairRight pairRight_mem
    let path := sourceExceptionalPath Gamma qAll markA publicBad pairRight facts
    occurrenceChainCodeOfWalk path.indexWalk (emptyOccurrenceBits Gamma) =
      .step 1 (.terminal (emptyOccurrenceBits Gamma)) := by
  dsimp only
  have hstart : exceptionalMarkedIndex Gamma markA publicBad pairRight = 0 := by
    rfl
  have hseed : (sourceExceptionalPath Gamma qAll markA publicBad pairRight
    (exceptionalSourceFactsOfMem Gamma qAll markA publicBad pairRight
      pairRight_mem)).seed = 1 := by
    have hp := forwardSeed_parts Gamma.length
      (bitMask pairRight.1) (bitMask pairRight.2) (predAt Gamma publicBad)
      (sourceExceptionalPath Gamma qAll markA publicBad pairRight
        (exceptionalSourceFactsOfMem Gamma qAll markA publicBad pairRight
          pairRight_mem)).seed_true
    exact bad_index hp.1 hp.2.2.2
  exact occurrenceChainCodeOfWalk_direct
    (show CWalk _ 0 1 from hstart ▸ hseed ▸
      (sourceExceptionalPath Gamma qAll markA publicBad pairRight
        (exceptionalSourceFactsOfMem Gamma qAll markA publicBad pairRight
          pairRight_mem)).indexWalk)
    (emptyOccurrenceBits Gamma) right_path_vertices

theorem left_residual_exact :
    leftPathResidual Gamma qAll markA publicBad entryLeft =
      bits3 false false true := by
  unfold leftPathResidual
  change residualBits
    (pathOccurrenceBits Gamma.length
      (sourceExceptionalPath Gamma qAll markA publicBad pairLeft
        (exceptionalSourceFactsOfMem Gamma qAll markA publicBad pairLeft
          pairLeft_mem)).indexWalk.vertices)
    pairLeft.1 = bits3 false false true
  rw [left_path_vertices]
  rfl

theorem right_residual_exact :
    rightPathResidual Gamma qAll markA publicBad entryRight =
      bits3 false false true := by
  unfold rightPathResidual
  change residualBits
    (pathOccurrenceBits Gamma.length
      (sourceExceptionalPath Gamma qAll markA publicBad pairRight
        (exceptionalSourceFactsOfMem Gamma qAll markA publicBad pairRight
          pairRight_mem)).indexWalk.vertices)
    pairRight.2 = bits3 false false true
  rw [right_path_vertices]
  rfl

/-- The two distinct one-sided sources emit exactly the same forward-path
external carrier code. -/
theorem oneSided_forward_carrier_collision :
    originalLeftResidualCarrierCode Gamma qAll markA publicBad entryLeft =
      originalRightResidualCarrierCode Gamma qAll markA publicBad
        entryRight := by
  unfold entryLeft entryRight
  unfold originalLeftResidualCarrierCode originalRightResidualCarrierCode
    parallelExternalCarrierCode exceptionalCustomCarrierCode
  dsimp only
  rw [left_path_chain, right_path_chain]
  rw [show leftPathResidual Gamma qAll markA publicBad
      ⟨pairLeft, pairLeft_mem⟩ = bits3 false false true by
    simpa [entryLeft] using left_residual_exact]
  rw [show rightPathResidual Gamma qAll markA publicBad
      ⟨pairRight, pairRight_mem⟩ = bits3 false false true by
    simpa [entryRight] using right_residual_exact]
  rw [show exceptionalMarkedIndex Gamma markA publicBad pairLeft = 0 by rfl]
  rw [show exceptionalMarkedIndex Gamma markA publicBad pairRight = 0 by rfl]

#print axioms pairLeft_mem
#print axioms pairRight_mem
#print axioms entries_ne
#print axioms left_residual_exact
#print axioms right_residual_exact
#print axioms oneSided_forward_carrier_collision

end YMGap.Continuum.XiExceptionalOneSidedCollisionFence
