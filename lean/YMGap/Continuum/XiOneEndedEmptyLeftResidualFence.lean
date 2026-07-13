/-
# Public one-ended empty-left-residual fence

The original left residual need not be empty in the public one-ended domain.
Here `A -- B` is the canonical marked-to-bad path, while `D` is a compatible
left occurrence disconnected from that path.  A head polymer meets `B` but
not `A`, so the bad predicate has exactly the public form
`fun X => !(compatibleB head X)`.
-/

import YMGap.Continuum.XiExceptionalOneAttachedResidualConsumer

namespace YMGap.Continuum.XiOneEndedEmptyLeftResidualFence

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
open YMGap.Continuum.XiExceptionalPathMaskAlgebra
open YMGap.Continuum.XiExceptionalOneAttachedResidualConsumer

private abbrev TL := toyLattice
private instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance

private def p0 : TL.Plaquette := (0, 0)
private def p1 : TL.Plaquette := (1, 0)
private def p2 : TL.Plaquette := (2, 0)
private def A : Polymer TL := [p0]
private def B : Polymer TL := [p0, p1]
private def D : Polymer TL := [p2]
private def head : Polymer TL := [p1]
private def Gamma : List (Polymer TL) := [A, B, D]
private def qAll : Polymer TL → Bool := fun _ => true
private def markA : Polymer TL → Bool := fun X => decide (X = A)
private def publicBad : Polymer TL → Bool :=
  fun X => !(compatibleB head X)

private def bits3 (x0 x1 x2 : Bool) : OccBitVec 3 :=
  .cons x0 (.cons x1 (.cons x2 .nil))

private def pair : MaskPair Gamma.length :=
  (bits3 false true true, bits3 true false false)

theorem pair_mem_public_oneEnded :
    pair ∈ exceptionalSourceCodes Gamma qAll markA
      (fun X => !(compatibleB head X)) := by
  apply List.mem_filter.mpr
  refine ⟨maskPairs_complete pair, ?_⟩
  rfl

def entry : ExceptionalSourceEntry Gamma qAll markA publicBad :=
  ⟨pair, pair_mem_public_oneEnded⟩

private abbrev pathEdge := disagreementEdge Gamma.length
  (incAtDistinct Gamma) (bitMask pair.1) (bitMask pair.2)

private theorem edge_zero_only_one {j : Nat}
    (h : pathEdge 0 j = true) : j = 1 := by
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) h).2
  have hj3 : j < 3 := by simpa [Gamma] using hj
  have h0 : j ≠ 0 := by intro e; subst j; cases h
  have h2 : j ≠ 2 := by intro e; subst j; cases h
  omega

private theorem CWalk.end_mem_vertices
    {alpha : Type} {edge : alpha → alpha → Bool} :
    ∀ {x y : alpha} (walk : CWalk edge x y), y ∈ walk.vertices
  | _, _, .single _ => List.mem_cons_self
  | _, _, .cons _ rest =>
      List.mem_cons_of_mem _ (CWalk.end_mem_vertices rest)

private theorem endpoint_walk_single
    (walk : CWalk pathEdge 1 1) (hnodup : walk.vertices.Nodup) :
    walk.vertices = [1] := by
  cases walk with
  | single _ => rfl
  | cons _ rest =>
      have hp := List.nodup_cons.mp hnodup
      exact absurd (CWalk.end_mem_vertices rest) hp.1

private theorem direct_walk
    {start finish : Nat} (walk : CWalk pathEdge start finish)
    (hstart : start = 0) (hfinish : finish = 1)
    (hnodup : walk.vertices.Nodup) : walk.vertices = [0, 1] := by
  subst start
  subst finish
  cases walk with
  | @cons _ next _ hedge rest =>
      have hnext := edge_zero_only_one hedge
      subst next
      simp only [CWalk.vertices]
      rw [endpoint_walk_single rest (List.nodup_cons.mp hnodup).2]

private theorem publicBad_polyAt_index {i : Nat} (hi : i < Gamma.length)
    (hbad : publicBad (polyAt Gamma i) = true) : i = 1 := by
  have hi3 : i < 3 := by simpa [Gamma] using hi
  have h0 : i ≠ 0 := by intro e; subst i; cases hbad
  have h2 : i ≠ 2 := by intro e; subst i; cases hbad
  omega

theorem canonical_path_vertices :
    let facts := exceptionalSourceFactsOfMem Gamma qAll markA publicBad
      pair pair_mem_public_oneEnded
    let path := sourceExceptionalPath Gamma qAll markA publicBad pair facts
    path.indexWalk.vertices = [0, 1] := by
  dsimp only
  let facts := exceptionalSourceFactsOfMem Gamma qAll markA publicBad
    pair pair_mem_public_oneEnded
  let path := sourceExceptionalPath Gamma qAll markA publicBad pair facts
  have hstart : exceptionalMarkedIndex Gamma markA publicBad pair = 0 := by rfl
  have hp := forwardSeed_parts Gamma.length
    (bitMask pair.1) (bitMask pair.2) (predAt Gamma publicBad)
    path.seed_true
  have hfinish : path.seed = 1 := publicBad_polyAt_index hp.1 hp.2.2.2
  exact direct_walk path.indexWalk hstart hfinish path.index_nodup

/-- The original left-cleared residual is exactly the off-path occurrence
`D`, so the sole premise of the right-only public consumer is false here. -/
theorem leftPathResidual_exact :
    leftPathResidual Gamma qAll markA publicBad entry =
      bits3 false false true := by
  unfold leftPathResidual
  change residualBits
    (pathOccurrenceBits Gamma.length
      (sourceExceptionalPath Gamma qAll markA publicBad pair
        (exceptionalSourceFactsOfMem Gamma qAll markA publicBad pair
          pair_mem_public_oneEnded)).indexWalk.vertices)
    pair.1 = bits3 false false true
  rw [canonical_path_vertices]
  rfl

theorem leftPathResidual_family_nonempty :
    selectByBits Gamma
      (leftPathResidual Gamma qAll markA publicBad entry) = [D] := by
  rw [leftPathResidual_exact]
  rfl

theorem empty_left_residual_premise_false :
    selectByBits Gamma
      (leftPathResidual Gamma qAll markA publicBad entry) ≠ [] := by
  rw [leftPathResidual_family_nonempty]
  intro h
  cases h

#print axioms pair_mem_public_oneEnded
#print axioms canonical_path_vertices
#print axioms leftPathResidual_exact
#print axioms leftPathResidual_family_nonempty
#print axioms empty_left_residual_premise_false

end YMGap.Continuum.XiOneEndedEmptyLeftResidualFence
