/-
# Parallel residual/component mismatch fence

The original-source right residual is not, in general, the right residual of
the source-dependent switched component.  In the four-occurrence star, the
bad centre is joined to the marked leaf and to two parallel residual leaves.
The component switch therefore moves the entire star.  Clearing the canonical
marked-to-bad path leaves both parallel leaves on the original right side, but
leaves nothing on the switched right side.

This exact counterexample prevents identifying the `2^k` original-side
parallel block with the switched-component residual block.
-/

import YMGap.Continuum.XiExceptionalParallelSubmaskCount

namespace YMGap.Continuum.XiExceptionalParallelComponentMismatchFence

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
open YMGap.Continuum.XiExceptionalParallelResidualBlock
open YMGap.Continuum.XiExceptionalParallelSubmaskCount

private abbrev TL := toyLattice
private instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance

private def p0 : TL.Plaquette := (0, 0)
private def p1 : TL.Plaquette := (1, 0)
private def p2 : TL.Plaquette := (2, 0)
private def A : Polymer TL := [p0]
private def B : Polymer TL := [p0, p1, p2]
private def C : Polymer TL := [p1]
private def D : Polymer TL := [p2]
private def Gamma : List (Polymer TL) := [A, B, C, D]
private def qAll : Polymer TL → Bool := fun _ => true
private def markA : Polymer TL → Bool := fun X => decide (X = A)
private def badB : Polymer TL → Bool := fun X => decide (X = B)

private def bits4 (x0 x1 x2 x3 : Bool) : OccBitVec 4 :=
  .cons x0 (.cons x1 (.cons x2 (.cons x3 .nil)))

private def pair : MaskPair Gamma.length :=
  (bits4 false true false false, bits4 true false true true)

theorem pair_mem :
    pair ∈ exceptionalSourceCodes Gamma qAll markA badB := by
  apply List.mem_filter.mpr
  refine ⟨maskPairs_complete pair, ?_⟩
  rfl

def entry : ExceptionalSourceEntry Gamma qAll markA badB :=
  ⟨pair, pair_mem⟩

private abbrev starEdge := disagreementEdge Gamma.length
  (incAtDistinct Gamma) (bitMask pair.1) (bitMask pair.2)

private theorem star_neighbor_zero {j : Nat}
    (h : starEdge 0 j = true) : j = 1 := by
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) h).2
  have hj4 : j < 4 := by simpa [Gamma] using hj
  have h0 : j ≠ 0 := by intro e; subst j; cases h
  have h2 : j ≠ 2 := by intro e; subst j; cases h
  have h3 : j ≠ 3 := by intro e; subst j; cases h
  omega

private theorem CWalk.end_mem_vertices
    {alpha : Type} {edge : alpha → alpha → Bool} :
    ∀ {x y : alpha} (walk : CWalk edge x y), y ∈ walk.vertices
  | _, _, .single _ => List.mem_cons_self
  | _, _, .cons _ rest =>
      List.mem_cons_of_mem _ (CWalk.end_mem_vertices rest)

private theorem endpoint_walk_single
    (walk : CWalk starEdge 1 1) (hnodup : walk.vertices.Nodup) :
    walk.vertices = [1] := by
  cases walk with
  | single _ => rfl
  | cons _ rest =>
      have hp := List.nodup_cons.mp hnodup
      exact absurd (CWalk.end_mem_vertices rest) hp.1

private theorem star_walk_direct
    {start finish : Nat} (walk : CWalk starEdge start finish)
    (hstart : start = 0) (hfinish : finish = 1)
    (hnodup : walk.vertices.Nodup) : walk.vertices = [0, 1] := by
  subst start
  subst finish
  cases walk with
  | @cons _ next _ hedge rest =>
      have hnext := star_neighbor_zero hedge
      subst next
      simp only [CWalk.vertices]
      rw [endpoint_walk_single rest (List.nodup_cons.mp hnodup).2]

private theorem badB_polyAt_index {i : Nat} (hi : i < Gamma.length)
    (hbad : badB (polyAt Gamma i) = true) : i = 1 := by
  have hi4 : i < 4 := by simpa [Gamma] using hi
  have h0 : i ≠ 0 := by intro e; subst i; cases hbad
  have h2 : i ≠ 2 := by intro e; subst i; cases hbad
  have h3 : i ≠ 3 := by intro e; subst i; cases hbad
  omega

theorem source_path_vertices :
    let facts := exceptionalSourceFactsOfMem Gamma qAll markA badB pair pair_mem
    let path := sourceExceptionalPath Gamma qAll markA badB pair facts
    path.indexWalk.vertices = [0, 1] := by
  dsimp only
  let facts := exceptionalSourceFactsOfMem Gamma qAll markA badB pair pair_mem
  let path := sourceExceptionalPath Gamma qAll markA badB pair facts
  have hstart : exceptionalMarkedIndex Gamma markA badB pair = 0 := by rfl
  have hp := forwardSeed_parts Gamma.length
    (bitMask pair.1) (bitMask pair.2) (predAt Gamma badB) path.seed_true
  have hfinish : path.seed = 1 := badB_polyAt_index hp.1 hp.2.2.2
  exact star_walk_direct path.indexWalk hstart hfinish path.index_nodup

/-- Both off-path leaves survive in the original right residual. -/
theorem original_right_residual_exact :
    rightPathResidual Gamma qAll markA badB entry =
      bits4 false false true true := by
  unfold rightPathResidual
  change residualBits
    (pathOccurrenceBits Gamma.length
      (sourceExceptionalPath Gamma qAll markA badB pair
        (exceptionalSourceFactsOfMem Gamma qAll markA badB pair pair_mem)).indexWalk.vertices)
    pair.2 = bits4 false false true true
  rw [source_path_vertices]
  rfl

/-- The original cleared residual has two independent occurrence bits. -/
theorem original_right_residual_count :
    occurrenceBitCount (rightPathResidual Gamma qAll markA badB entry) = 2 := by
  rw [original_right_residual_exact]
  rfl

/-- After the full component switch, clearing the path leaves no right bit. -/
theorem switched_right_residual_exact :
    let facts := exceptionalSourceFactsOfMem Gamma qAll markA badB pair pair_mem
    let path := sourceExceptionalPath Gamma qAll markA badB pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    residualBits pathBits (switchedBranchCode Gamma badB pair).2 =
      bits4 false false false false := by
  dsimp only
  rw [source_path_vertices]
  rfl

/-- The two residual masks cannot be identified. -/
theorem original_residual_ne_switched_component_residual :
    let facts := exceptionalSourceFactsOfMem Gamma qAll markA badB pair pair_mem
    let path := sourceExceptionalPath Gamma qAll markA badB pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    rightPathResidual Gamma qAll markA badB entry ≠
      residualBits pathBits (switchedBranchCode Gamma badB pair).2 := by
  dsimp only
  rw [original_right_residual_exact, switched_right_residual_exact]
  intro h
  have hat := congrArg (fun bits => bits.at 2) h
  cases hat

#print axioms pair_mem
#print axioms source_path_vertices
#print axioms original_right_residual_exact
#print axioms original_right_residual_count
#print axioms switched_right_residual_exact
#print axioms original_residual_ne_switched_component_residual

end YMGap.Continuum.XiExceptionalParallelComponentMismatchFence
