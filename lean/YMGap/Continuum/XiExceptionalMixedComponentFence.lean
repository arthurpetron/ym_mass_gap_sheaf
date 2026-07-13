/-
# Mixed residual-component fence

The six-cycle has two internally disjoint odd paths between the marked
endpoints.  The canonical exceptional path uses one arc.  The other arc is
a single residual disagreement component whose two endpoint occurrences
are path-incompatible and lie on opposite switched sides.  Consequently
neither a left-rooted nor a right-rooted whole-component orientation can put
every path-incompatible residual occurrence outside the terminal background.
-/

import YMGap.Continuum.XiExceptionalComponentSummation

namespace YMGap.Continuum.XiExceptionalMixedComponentFence

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
open YMGap.Continuum.XiExceptionalPathMaskAlgebra
open YMGap.Continuum.XiExceptionalPathSafeInjection
open YMGap.Continuum.XiExceptionalComponentRouter
open YMGap.Continuum.XiExceptionalComponentCarrier

private abbrev TL := toyLattice
private instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance

private def e0 : TL.Plaquette := (0, 0)
private def e1 : TL.Plaquette := (1, 0)
private def e2 : TL.Plaquette := (2, 0)
private def e3 : TL.Plaquette := (3, 0)
private def e4 : TL.Plaquette := (4, 0)
private def e5 : TL.Plaquette := (5, 0)

private def V0 : Polymer TL := [e5, e0]
private def V1 : Polymer TL := [e0, e1]
private def V2 : Polymer TL := [e1, e2]
private def V3 : Polymer TL := [e2, e3]
private def V4 : Polymer TL := [e3, e4]
private def V5 : Polymer TL := [e4, e5]

private def Gamma : List (Polymer TL) := [V0, V1, V2, V3, V4, V5]
private def qAll : Polymer TL → Bool := fun _ => true
private def markV0 : Polymer TL → Bool := fun X => decide (X = V0)
private def badV3 : Polymer TL → Bool := fun X => decide (X = V3)

private def bits6 (x0 x1 x2 x3 x4 x5 : Bool) : OccBitVec 6 :=
  .cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 (.cons x5 .nil)))))

private def pair : MaskPair Gamma.length :=
  (bits6 false true false true false true,
    bits6 true false true false true false)

private def pairMem :
    pair ∈ exceptionalSourceCodes Gamma qAll markV0 badV3 := by
  apply List.mem_filter.mpr
  refine ⟨maskPairs_complete pair, ?_⟩
  rfl

def entry : ExceptionalSourceEntry Gamma qAll markV0 badV3 :=
  ⟨pair, pairMem⟩

theorem pair_mem :
    pair ∈ exceptionalSourceCodes Gamma qAll markV0 badV3 :=
  pairMem

private theorem CWalk.end_mem_vertices
    {alpha : Type} {edge : alpha → alpha → Bool} :
    ∀ {x y : alpha} (walk : CWalk edge x y), y ∈ walk.vertices
  | _, _, .single _ => List.mem_cons_self
  | _, _, .cons _ rest =>
      List.mem_cons_of_mem _ (CWalk.end_mem_vertices rest)

private abbrev cycleEdge := disagreementEdge Gamma.length
  (incAtDistinct Gamma) (bitMask pair.1) (bitMask pair.2)

private theorem cycle_neighbor_zero {j : Nat}
    (h : cycleEdge 0 j = true) : j = 1 ∨ j = 5 := by
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) h).2
  have hj6 : j < 6 := by simpa [Gamma] using hj
  have h0 : j ≠ 0 := by intro e; subst j; cases h
  have h2 : j ≠ 2 := by intro e; subst j; cases h
  have h3 : j ≠ 3 := by intro e; subst j; cases h
  have h4 : j ≠ 4 := by intro e; subst j; cases h
  omega

private theorem cycle_neighbor_one {j : Nat}
    (h : cycleEdge 1 j = true) : j = 0 ∨ j = 2 := by
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) h).2
  have hj6 : j < 6 := by simpa [Gamma] using hj
  have h1 : j ≠ 1 := by intro e; subst j; cases h
  have h3 : j ≠ 3 := by intro e; subst j; cases h
  have h4 : j ≠ 4 := by intro e; subst j; cases h
  have h5 : j ≠ 5 := by intro e; subst j; cases h
  omega

private theorem cycle_neighbor_two {j : Nat}
    (h : cycleEdge 2 j = true) : j = 1 ∨ j = 3 := by
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) h).2
  have hj6 : j < 6 := by simpa [Gamma] using hj
  have h0 : j ≠ 0 := by intro e; subst j; cases h
  have h2 : j ≠ 2 := by intro e; subst j; cases h
  have h4 : j ≠ 4 := by intro e; subst j; cases h
  have h5 : j ≠ 5 := by intro e; subst j; cases h
  omega

private theorem cycle_neighbor_five {j : Nat}
    (h : cycleEdge 5 j = true) : j = 0 ∨ j = 4 := by
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) h).2
  have hj6 : j < 6 := by simpa [Gamma] using hj
  have h1 : j ≠ 1 := by intro e; subst j; cases h
  have h2 : j ≠ 2 := by intro e; subst j; cases h
  have h3 : j ≠ 3 := by intro e; subst j; cases h
  have h5 : j ≠ 5 := by intro e; subst j; cases h
  omega

private theorem cycle_neighbor_four {j : Nat}
    (h : cycleEdge 4 j = true) : j = 3 ∨ j = 5 := by
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) h).2
  have hj6 : j < 6 := by simpa [Gamma] using hj
  have h0 : j ≠ 0 := by intro e; subst j; cases h
  have h1 : j ≠ 1 := by intro e; subst j; cases h
  have h2 : j ≠ 2 := by intro e; subst j; cases h
  have h4 : j ≠ 4 := by intro e; subst j; cases h
  omega

private theorem endpoint_walk_single
    (walk : CWalk cycleEdge 3 3) (hnodup : walk.vertices.Nodup) :
    walk.vertices = [3] := by
  cases walk with
  | single _ => rfl
  | cons hedge rest =>
      have hp := List.nodup_cons.mp hnodup
      exact absurd (CWalk.end_mem_vertices rest) hp.1

private theorem cycle_walk_arcs
    {start finish : Nat} (walk : CWalk cycleEdge start finish)
    (hstart : start = 0) (hfinish : finish = 3)
    (hnodup : walk.vertices.Nodup) :
    walk.vertices = [0, 1, 2, 3] ∨
      walk.vertices = [0, 5, 4, 3] := by
  subst start
  subst finish
  cases walk with
  | @cons _ next _ hedge rest =>
      have hnd0 := List.nodup_cons.mp hnodup
      rcases cycle_neighbor_zero hedge with hnext | hnext
      · subst next
        cases rest with
        | @cons _ next2 _ hedge2 rest2 =>
            have hnd1 := List.nodup_cons.mp hnd0.2
            rcases cycle_neighbor_one hedge2 with hnext2 | hnext2
            · subst next2
              exact absurd
                (List.mem_cons_of_mem 1 (CWalk.start_mem_vertices rest2)) hnd0.1
            · subst next2
              cases rest2 with
              | @cons _ next3 _ hedge3 rest3 =>
                  have hnd2 := List.nodup_cons.mp hnd1.2
                  rcases cycle_neighbor_two hedge3 with hnext3 | hnext3
                  · subst next3
                    exact absurd
                      (List.mem_cons_of_mem 2 (CWalk.start_mem_vertices rest3)) hnd1.1
                  · subst next3
                    left
                    simp only [CWalk.vertices]
                    rw [endpoint_walk_single rest3 hnd2.2]
      · subst next
        cases rest with
        | @cons _ next2 _ hedge2 rest2 =>
            have hnd5 := List.nodup_cons.mp hnd0.2
            rcases cycle_neighbor_five hedge2 with hnext2 | hnext2
            · subst next2
              exact absurd
                (List.mem_cons_of_mem 5 (CWalk.start_mem_vertices rest2)) hnd0.1
            · subst next2
              cases rest2 with
              | @cons _ next3 _ hedge3 rest3 =>
                  have hnd4 := List.nodup_cons.mp hnd5.2
                  rcases cycle_neighbor_four hedge3 with hnext3 | hnext3
                  · subst next3
                    right
                    simp only [CWalk.vertices]
                    rw [endpoint_walk_single rest3 hnd4.2]
                  · subst next3
                    exact absurd
                      (List.mem_cons_of_mem 4 (CWalk.start_mem_vertices rest3)) hnd5.1

private theorem badV3_polyAt_index {i : Nat} (hi : i < Gamma.length)
    (hbad : badV3 (polyAt Gamma i) = true) : i = 3 := by
  have hi6 : i < 6 := by simpa [Gamma] using hi
  have h0 : i ≠ 0 := by intro e; subst i; cases hbad
  have h1 : i ≠ 1 := by intro e; subst i; cases hbad
  have h2 : i ≠ 2 := by intro e; subst i; cases hbad
  have h4 : i ≠ 4 := by intro e; subst i; cases hbad
  have h5 : i ≠ 5 := by intro e; subst i; cases hbad
  omega

theorem source_path_is_cycle_arc :
    let facts := exceptionalSourceFactsOfMem Gamma qAll markV0 badV3 pair pairMem
    let path := sourceExceptionalPath Gamma qAll markV0 badV3 pair facts
    path.indexWalk.vertices = [0, 1, 2, 3] ∨
      path.indexWalk.vertices = [0, 5, 4, 3] := by
  dsimp only
  let facts := exceptionalSourceFactsOfMem Gamma qAll markV0 badV3 pair pairMem
  let path := sourceExceptionalPath Gamma qAll markV0 badV3 pair facts
  have hstart : exceptionalMarkedIndex Gamma markV0 badV3 pair = 0 := by rfl
  have hp := forwardSeed_parts Gamma.length
    (bitMask pair.1) (bitMask pair.2) (predAt Gamma badV3) path.seed_true
  have hfinish : path.seed = 3 := badV3_polyAt_index hp.1 hp.2.2.2
  exact cycle_walk_arcs path.indexWalk hstart hfinish path.index_nodup

theorem residual_has_unsafe_right :
    let facts := exceptionalSourceFactsOfMem Gamma qAll markV0 badV3 pair pairMem
    let path := sourceExceptionalPath Gamma qAll markV0 badV3 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma badV3 pair
    let rightResidual := residualBits pathBits switched.2
    let safe := exceptionalPathSafe Gamma qAll markV0 badV3 entry
    ∃ i, i < Gamma.length ∧ rightResidual.at i = true ∧ safe i = false := by
  dsimp only
  rcases source_path_is_cycle_arc with hpath | hpath
  · refine ⟨5, by simp [Gamma], ?_, ?_⟩
    · rw [hpath]
      rfl
    · unfold exceptionalPathSafe entry
      dsimp only
      rw [hpath]
      rfl
  · refine ⟨1, by simp [Gamma], ?_, ?_⟩
    · rw [hpath]
      rfl
    · unfold exceptionalPathSafe entry
      dsimp only
      rw [hpath]
      rfl

theorem residual_has_unsafe_left :
    let facts := exceptionalSourceFactsOfMem Gamma qAll markV0 badV3 pair pairMem
    let path := sourceExceptionalPath Gamma qAll markV0 badV3 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma badV3 pair
    let leftResidual := residualBits pathBits switched.1
    let safe := exceptionalPathSafe Gamma qAll markV0 badV3 entry
    ∃ i, i < Gamma.length ∧ leftResidual.at i = true ∧ safe i = false := by
  dsimp only
  rcases source_path_is_cycle_arc with hpath | hpath
  · refine ⟨4, by simp [Gamma], ?_, ?_⟩
    · rw [hpath]
      rfl
    · unfold exceptionalPathSafe entry
      dsimp only
      rw [hpath]
      rfl
  · refine ⟨2, by simp [Gamma], ?_, ?_⟩
    · rw [hpath]
      rfl
    · unfold exceptionalPathSafe entry
      dsimp only
      rw [hpath]
      rfl

theorem component_right_safe_fails :
    ¬ componentRightSafe Gamma qAll markV0 badV3 entry := by
  intro hright
  obtain ⟨i, hi, hres, hunsafe⟩ := residual_has_unsafe_right
  have hsafe := hright i hi hres
  rw [hunsafe] at hsafe
  cases hsafe

def componentLeftSafe : Prop :=
  let facts := exceptionalSourceFactsOfMem Gamma qAll markV0 badV3 pair pairMem
  let path := sourceExceptionalPath Gamma qAll markV0 badV3 pair facts
  let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
  let switched := switchedBranchCode Gamma badV3 pair
  let leftResidual := residualBits pathBits switched.1
  let safe := exceptionalPathSafe Gamma qAll markV0 badV3 entry
  ∀ i, i < Gamma.length → leftResidual.at i = true → safe i = true

theorem component_left_safe_fails : ¬ componentLeftSafe := by
  intro hleft
  obtain ⟨i, hi, hres, hunsafe⟩ := residual_has_unsafe_left
  have hsafe := hleft i hi hres
  rw [hunsafe] at hsafe
  cases hsafe

/-- The left-rooted whole-component orientation moves the unsafe residual
right endpoint into the terminal background. -/
theorem left_rooted_background_has_unsafe :
    let facts := exceptionalSourceFactsOfMem Gamma qAll markV0 badV3 pair pairMem
    let path := sourceExceptionalPath Gamma qAll markV0 badV3 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma badV3 pair
    let leftResidual := residualBits pathBits switched.1
    let rightResidual := residualBits pathBits switched.2
    let safe := exceptionalPathSafe Gamma qAll markV0 badV3 entry
    ∃ i, i < Gamma.length ∧
      (componentBackground Gamma safe leftResidual rightResidual).at i = true ∧
      safe i = false := by
  dsimp only
  rcases source_path_is_cycle_arc with hpath | hpath
  · refine ⟨5, by simp [Gamma], ?_, ?_⟩
    · unfold exceptionalPathSafe entry
      dsimp only
      rw [hpath]
      rfl
    · unfold exceptionalPathSafe entry
      dsimp only
      rw [hpath]
      rfl
  · refine ⟨1, by simp [Gamma], ?_, ?_⟩
    · unfold exceptionalPathSafe entry
      dsimp only
      rw [hpath]
      rfl
    · unfold exceptionalPathSafe entry
      dsimp only
      rw [hpath]
      rfl

/-- Reversing the component orientation only exchanges which unsafe
endpoint is forced into the terminal background. -/
theorem right_rooted_background_has_unsafe :
    let facts := exceptionalSourceFactsOfMem Gamma qAll markV0 badV3 pair pairMem
    let path := sourceExceptionalPath Gamma qAll markV0 badV3 pair facts
    let pathBits := pathOccurrenceBits Gamma.length path.indexWalk.vertices
    let switched := switchedBranchCode Gamma badV3 pair
    let leftResidual := residualBits pathBits switched.1
    let rightResidual := residualBits pathBits switched.2
    let safe := exceptionalPathSafe Gamma qAll markV0 badV3 entry
    ∃ i, i < Gamma.length ∧
      (componentBackground Gamma safe rightResidual leftResidual).at i = true ∧
      safe i = false := by
  dsimp only
  rcases source_path_is_cycle_arc with hpath | hpath
  · refine ⟨4, by simp [Gamma], ?_, ?_⟩
    · unfold exceptionalPathSafe entry
      dsimp only
      rw [hpath]
      rfl
    · unfold exceptionalPathSafe entry
      dsimp only
      rw [hpath]
      rfl
  · refine ⟨2, by simp [Gamma], ?_, ?_⟩
    · unfold exceptionalPathSafe entry
      dsimp only
      rw [hpath]
      rfl
    · unfold exceptionalPathSafe entry
      dsimp only
      rw [hpath]
      rfl

#print axioms pair_mem
#print axioms source_path_is_cycle_arc
#print axioms residual_has_unsafe_right
#print axioms residual_has_unsafe_left
#print axioms component_right_safe_fails
#print axioms component_left_safe_fails
#print axioms left_rooted_background_has_unsafe
#print axioms right_rooted_background_has_unsafe

end YMGap.Continuum.XiExceptionalMixedComponentFence
