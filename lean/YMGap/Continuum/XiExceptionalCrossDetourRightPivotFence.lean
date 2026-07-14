/-
# Source-entry fence for a right-pivot cross detour

The failed routed-external branch always supplies an unsafe-left/right cross
edge `i--j`, but it does not force the right endpoint `j` to conflict with the
canonical path.  In the minimal four-occurrence path source below, the routed
external family is the incompatible pair `C,D`; `C` is the unsafe-left
endpoint, while the only right residual occurrence `D` is path-safe.

Consequently a proposed bridge `p--i--j--q` cannot in general obtain its final
edge `j--q`.  This is an entry-level source counterexample, not a raw graph
state.  The one-sided ear through `i` remains available and is the next
allocation mechanism.
-/

import YMGap.Continuum.XiExceptionalRoutedExternalSplit

namespace YMGap.Continuum.XiExceptionalCrossDetourRightPivotFence

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
open YMGap.Continuum.XiExceptionalPathSafeInjection
open YMGap.Continuum.XiExceptionalRoutedExternalSplit

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

private theorem pairMem :
    pair ∈ exceptionalSourceCodes Gamma qAll markA badB := by
  apply List.mem_filter.mpr
  refine ⟨maskPairs_complete pair, ?_⟩
  rfl

def entry : ExceptionalSourceEntry Gamma qAll markA badB :=
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

theorem routed_left_residual_exact :
    routedLeftResidual Gamma qAll markA badB entry =
      bits4 false false true false := by
  unfold routedLeftResidual entry
  dsimp only
  rw [canonical_path_vertices]
  rfl

theorem routed_right_residual_exact :
    routedRightResidual Gamma qAll markA badB entry =
      bits4 false false false true := by
  unfold routedRightResidual entry
  dsimp only
  rw [canonical_path_vertices]
  rfl

theorem routed_external_exact :
    entryRoutedExternal Gamma qAll markA badB entry =
      bits4 false false true true := by
  unfold entryRoutedExternal
  rw [routed_left_residual_exact, routed_right_residual_exact]
  unfold exceptionalPathSafe entry
  dsimp only
  rw [canonical_path_vertices]
  rfl

theorem routed_external_incompatible :
    routedExternalCompatibleB Gamma qAll markA badB entry = false := by
  unfold routedExternalCompatibleB
  rw [routed_external_exact]
  rfl

theorem left_endpoint_unsafe :
    (routedLeftResidual Gamma qAll markA badB entry).at 2 = true ∧
      exceptionalPathSafe Gamma qAll markA badB entry 2 = false := by
  constructor
  · rw [routed_left_residual_exact]
    rfl
  · unfold exceptionalPathSafe entry
    dsimp only
    rw [canonical_path_vertices]
    rfl

theorem cross_edge_exact :
    compatibleB (polyAt Gamma 2) (polyAt Gamma 3) = false := by
  rfl

theorem every_right_residual_occurrence_path_safe :
    ∀ j, j < Gamma.length →
      (routedRightResidual Gamma qAll markA badB entry).at j = true →
      exceptionalPathSafe Gamma qAll markA badB entry j = true := by
  intro j hj hright
  rw [routed_right_residual_exact] at hright
  have hj4 : j < 4 := by simpa [Gamma] using hj
  have hj3 : j = 3 := by
    have hne0 : j ≠ 0 := by intro h; subst j; cases hright
    have hne1 : j ≠ 1 := by intro h; subst j; cases hright
    have hne2 : j ≠ 2 := by intro h; subst j; cases hright
    omega
  subst j
  unfold exceptionalPathSafe entry
  dsimp only
  rw [canonical_path_vertices]
  rfl

/-- The failed routed-external source has no possible right path pivot. -/
theorem no_right_path_conflict_endpoint :
    ¬ ∃ j, j < Gamma.length ∧
      (routedRightResidual Gamma qAll markA badB entry).at j = true ∧
      exceptionalPathSafe Gamma qAll markA badB entry j = false := by
  intro h
  obtain ⟨j, hj, hright, hunsafe⟩ := h
  have hsafe := every_right_residual_occurrence_path_safe j hj hright
  rw [hsafe] at hunsafe
  cases hunsafe

#print axioms routed_left_residual_exact
#print axioms routed_right_residual_exact
#print axioms routed_external_exact
#print axioms routed_external_incompatible
#print axioms left_endpoint_unsafe
#print axioms cross_edge_exact
#print axioms every_right_residual_occurrence_path_safe
#print axioms no_right_path_conflict_endpoint

end YMGap.Continuum.XiExceptionalCrossDetourRightPivotFence
