/-
# Counterexample to path-local external compatibility

The path-safe router moves every residual right occurrence into the external
family and also moves every path-incompatible residual left occurrence there.
Those two classes need not be mutually compatible.  The four-polymer path
below is the minimal branch-crossing obstruction:

    A -- B -- C -- D

The source sides are `{B,D}` and `{A,C}`.  Switching the reached component
gives `{A,C}` and `{B,D}`; the extracted exceptional path is `A -- B`, so the
residual incompatible pair `C -- D` is routed together into the external
family.  This is a closed, kernel-reduced fence around the path-local router;
it does not weaken `PathSafeRoutedFacts`.
-/

import YMGap.Continuum.XiPathSafeFactsClosure

namespace YMGap.Continuum.XiPathSafeExternalCompatibilityFence

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
open YMGap.Continuum.XiExceptionalBranchRouter
open YMGap.Continuum.XiExceptionalPathMaskAlgebra
open YMGap.Continuum.XiExceptionalPathSafeInjection

private abbrev TL := toyLattice
private instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance

private def p0 : TL.Plaquette := (0, 0)
private def p1 : TL.Plaquette := (1, 0)
private def p2 : TL.Plaquette := (2, 0)
private def A : Polymer TL := [p0]
private def B : Polymer TL := [p0, p1]
private def C : Polymer TL := [p1, p2]
private def D : Polymer TL := [p2]
private def Gamma : List (Polymer TL) := [A, B, C, D]
private def qAll : Polymer TL → Bool := fun _ => true
private def markA : Polymer TL → Bool := fun X => decide (X = A)
private def badB : Polymer TL → Bool := fun X => decide (X = B)

private def bits4 (x0 x1 x2 x3 : Bool) : OccBitVec 4 :=
  .cons x0 (.cons x1 (.cons x2 (.cons x3 .nil)))

private def pair : MaskPair Gamma.length :=
  (bits4 false true false true, bits4 true false true false)

private def pairMem :
    pair ∈ exceptionalSourceCodes Gamma qAll markA badB := by
  apply List.mem_filter.mpr
  refine ⟨maskPairs_complete pair, ?_⟩
  rfl

theorem pair_mem :
    pair ∈ exceptionalSourceCodes Gamma qAll markA badB :=
  pairMem

private def entry : ExceptionalSourceEntry Gamma qAll markA badB :=
  ⟨pair, pairMem⟩

private theorem CWalk.end_mem_vertices
    {alpha : Type} {edge : alpha → alpha → Bool} :
    ∀ {x y : alpha} (walk : CWalk edge x y), y ∈ walk.vertices
  | _, _, .single _ => List.mem_cons_self
  | _, _, .cons _ rest =>
      List.mem_cons_of_mem _ (CWalk.end_mem_vertices rest)

private theorem walk_vertices_eq_direct
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
      have hnext : next = 1 := hfirst next hedge
      subst next
      cases rest with
      | single _ => rfl
      | @cons _ next' _ hedge' tail =>
          have hp := List.nodup_cons.mp hnodup
          have htailNodup := List.nodup_cons.mp hp.2
          exact absurd (CWalk.end_mem_vertices tail) htailNodup.1

private theorem badB_polyAt_index {i : Nat} (hi : i < Gamma.length)
    (hbad : badB (polyAt Gamma i) = true) : i = 1 := by
  have hi4 : i < 4 := by simpa [Gamma] using hi
  have hne0 : i ≠ 0 := by intro h; subst i; cases hbad
  have hne2 : i ≠ 2 := by intro h; subst i; cases hbad
  have hne3 : i ≠ 3 := by intro h; subst i; cases hbad
  omega

private theorem no_edge_00 :
    disagreementEdge Gamma.length (incAtDistinct Gamma)
      (bitMask pair.1) (bitMask pair.2) 0 0 = false := by
  rfl

private theorem no_edge_02 :
    disagreementEdge Gamma.length (incAtDistinct Gamma)
      (bitMask pair.1) (bitMask pair.2) 0 2 = false := by
  rfl

private theorem no_edge_03 :
    disagreementEdge Gamma.length (incAtDistinct Gamma)
      (bitMask pair.1) (bitMask pair.2) 0 3 = false := by
  rfl

private theorem canonical_path_vertices :
    let facts := exceptionalSourceFactsOfMem Gamma qAll markA badB pair pairMem
    let path := sourceExceptionalPath Gamma qAll markA badB pair facts
    path.indexWalk.vertices = [0, 1] := by
  dsimp only
  let facts := exceptionalSourceFactsOfMem Gamma qAll markA badB pair pairMem
  let path := sourceExceptionalPath Gamma qAll markA badB pair facts
  have hmarked : exceptionalMarkedIndex Gamma markA badB pair = 0 := by
    rfl
  have hseed : path.seed = 1 := by
    have hp := forwardSeed_parts Gamma.length
      (bitMask pair.1) (bitMask pair.2) (predAt Gamma badB) path.seed_true
    exact badB_polyAt_index hp.1 hp.2.2.2
  have hfirst : ∀ j,
      disagreementEdge Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) 0 j = true → j = 1 := by
    intro j hedge
    have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
      (bitMask pair.1) (bitMask pair.2) hedge).2
    have hj0 : j ≠ 0 := by
      intro h
      subst j
      rw [no_edge_00] at hedge
      cases hedge
    have hj2 : j ≠ 2 := by
      intro h
      subst j
      rw [no_edge_02] at hedge
      cases hedge
    have hj3 : j ≠ 3 := by
      intro h
      subst j
      rw [no_edge_03] at hedge
      cases hedge
    have hj4 : j < 4 := by simpa [Gamma] using hj
    omega
  exact walk_vertices_eq_direct path.indexWalk hmarked hseed
    path.index_nodup hfirst

/-- The canonical path-local router puts the incompatible residual pair
`C,D` in its external family. -/
theorem routed_external_eq_branch_pair :
    let facts := exceptionalSourceFactsOfMem Gamma qAll markA badB pair pairMem
    let path := sourceExceptionalPath Gamma qAll markA badB pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma badB pair
    let leftResidual := residualBits pathBits switched.1
    let rightResidual := residualBits pathBits switched.2
    selectByBits Gamma
      (routedExternal (exceptionalPathSafe Gamma qAll markA badB entry)
        leftResidual rightResidual) = [C, D] := by
  dsimp only
  unfold exceptionalPathSafe entry
  dsimp only
  rw [canonical_path_vertices]
  rfl

/-- Hence the only unresolved field of `PathSafeRoutedFacts` is false for
this router, even though the source is an admissible exceptional entry. -/
theorem routed_external_not_compatible :
    let facts := exceptionalSourceFactsOfMem Gamma qAll markA badB pair pairMem
    let path := sourceExceptionalPath Gamma qAll markA badB pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma badB pair
    let leftResidual := residualBits pathBits switched.1
    let rightResidual := residualBits pathBits switched.2
    familyCompatibleB (selectByBits Gamma
      (routedExternal (exceptionalPathSafe Gamma qAll markA badB entry)
        leftResidual rightResidual)) = false := by
  dsimp only
  rw [routed_external_eq_branch_pair]
  rfl

#print axioms pair_mem
#print axioms routed_external_eq_branch_pair
#print axioms routed_external_not_compatible

end YMGap.Continuum.XiPathSafeExternalCompatibilityFence
