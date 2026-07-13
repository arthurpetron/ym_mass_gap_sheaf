/-
# First external-reserve limit fence

The chordless twelve-cycle has complementary marked-to-bad ears with one and
four interior pairs.  It satisfies the same three-branch residual hypotheses
as the earlier eight-cycle.  The long square has eighteen activity factors
and the sharp unchanged occurrence carrier has thirteen vertex slots, so an
external reserve must carry at least five long-interior factors.  But every
compatible family in the eight-vertex long interior has size at most four.
Thus the single-code external-reserve-square extraction cannot be automatic
on the current residual invariant.
-/

import YMGap.Continuum.XiExceptionalUnbalancedCycleRepair

namespace YMGap.Continuum.XiExceptionalExternalReserveLimitFence

open YMGap.Constructive
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
open YMGap.Continuum.XiExceptionalPathSafeInjection
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalFullSourceBound
open YMGap.Continuum.XiExceptionalRoutedExternalSplit
open YMGap.Continuum.XiExceptionalThreeBranchClassificationFence
open YMGap.Continuum.XiExceptionalFourthMixedRepair
open YMGap.Continuum.XiExceptionalBlockCutFuel
open YMGap.Continuum.XiExceptionalEarPairBounce
open YMGap.Continuum.XiExceptionalFirstConflictDetour
open YMGap.Continuum.XiExceptionalUnbalancedCycleFence
open YMGap.Continuum.XiExceptionalUnbalancedCycleRepair

abbrev TL := toyLattice
instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance

def e0 : TL.Plaquette := (0, 0)
def e1 : TL.Plaquette := (1, 0)
def e2 : TL.Plaquette := (2, 0)
def e3 : TL.Plaquette := (3, 0)
def e4 : TL.Plaquette := (4, 0)
def e5 : TL.Plaquette := (5, 0)
def e6 : TL.Plaquette := (6, 0)
def e7 : TL.Plaquette := (7, 0)
def e8 : TL.Plaquette := (8, 0)
def e9 : TL.Plaquette := (9, 0)
def e10 : TL.Plaquette := (10, 0)
def e11 : TL.Plaquette := (11, 0)

def V0 : Polymer TL := [e11, e0]
def V1 : Polymer TL := [e0, e1]
def V2 : Polymer TL := [e1, e2]
def V3 : Polymer TL := [e2, e3]
def V4 : Polymer TL := [e3, e4]
def V5 : Polymer TL := [e4, e5]
def V6 : Polymer TL := [e5, e6]
def V7 : Polymer TL := [e6, e7]
def V8 : Polymer TL := [e7, e8]
def V9 : Polymer TL := [e8, e9]
def V10 : Polymer TL := [e9, e10]
def V11 : Polymer TL := [e10, e11]

def Gamma : List (Polymer TL) :=
  [V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11]
def qAll : Polymer TL → Bool := fun _ => true
def markV0 : Polymer TL → Bool := fun X => decide (X = V0)
def badV3 : Polymer TL → Bool := fun X => decide (X = V3)

def bits12
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Bool) : OccBitVec 12 :=
  .cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 (.cons x5
    (.cons x6 (.cons x7 (.cons x8 (.cons x9 (.cons x10
      (.cons x11 .nil)))))))))))

def pair : MaskPair Gamma.length :=
  (bits12 false true false true false true false true false true false true,
    bits12 true false true false true false true false true false true false)

theorem pair_mem :
    pair ∈ exceptionalSourceCodes Gamma qAll markV0 badV3 := by
  apply List.mem_filter.mpr
  refine ⟨maskPairs_complete pair, ?_⟩
  rfl

def entry : ExceptionalSourceEntry Gamma qAll markV0 badV3 :=
  ⟨pair, pair_mem⟩

theorem entry_mem_full :
    entry ∈ fullExceptionalSource Gamma qAll markV0 badV3 :=
  List.mem_attach _ entry

abbrev cycleEdge := disagreementEdge Gamma.length
  (incAtDistinct Gamma) (bitMask pair.1) (bitMask pair.2)

private theorem CWalk.end_mem_vertices
    {alpha : Type} {edge : alpha → alpha → Bool} :
    ∀ {x y : alpha} (walk : CWalk edge x y), y ∈ walk.vertices
  | _, _, .single _ => List.mem_cons_self
  | _, _, .cons _ rest =>
      List.mem_cons_of_mem _ (CWalk.end_mem_vertices rest)

private theorem neighbor_zero {j : Nat}
    (h : cycleEdge 0 j = true) : j = 1 ∨ j = 11 := by
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) h).2
  have hj12 : j < 12 := by simpa [Gamma] using hj
  have h0 : j ≠ 0 := by intro e; subst j; cases h
  have h2 : j ≠ 2 := by intro e; subst j; cases h
  have h3 : j ≠ 3 := by intro e; subst j; cases h
  have h4 : j ≠ 4 := by intro e; subst j; cases h
  have h5 : j ≠ 5 := by intro e; subst j; cases h
  have h6 : j ≠ 6 := by intro e; subst j; cases h
  have h7 : j ≠ 7 := by intro e; subst j; cases h
  have h8 : j ≠ 8 := by intro e; subst j; cases h
  have h9 : j ≠ 9 := by intro e; subst j; cases h
  have h10 : j ≠ 10 := by intro e; subst j; cases h
  omega

private theorem neighbor_one {j : Nat}
    (h : cycleEdge 1 j = true) : j = 0 ∨ j = 2 := by
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) h).2
  have hj12 : j < 12 := by simpa [Gamma] using hj
  have h1 : j ≠ 1 := by intro e; subst j; cases h
  have h3 : j ≠ 3 := by intro e; subst j; cases h
  have h4 : j ≠ 4 := by intro e; subst j; cases h
  have h5 : j ≠ 5 := by intro e; subst j; cases h
  have h6 : j ≠ 6 := by intro e; subst j; cases h
  have h7 : j ≠ 7 := by intro e; subst j; cases h
  have h8 : j ≠ 8 := by intro e; subst j; cases h
  have h9 : j ≠ 9 := by intro e; subst j; cases h
  have h10 : j ≠ 10 := by intro e; subst j; cases h
  have h11 : j ≠ 11 := by intro e; subst j; cases h
  omega

private theorem neighbor_two {j : Nat}
    (h : cycleEdge 2 j = true) : j = 1 ∨ j = 3 := by
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) h).2
  have hj12 : j < 12 := by simpa [Gamma] using hj
  have h0 : j ≠ 0 := by intro e; subst j; cases h
  have h2 : j ≠ 2 := by intro e; subst j; cases h
  have h4 : j ≠ 4 := by intro e; subst j; cases h
  have h5 : j ≠ 5 := by intro e; subst j; cases h
  have h6 : j ≠ 6 := by intro e; subst j; cases h
  have h7 : j ≠ 7 := by intro e; subst j; cases h
  have h8 : j ≠ 8 := by intro e; subst j; cases h
  have h9 : j ≠ 9 := by intro e; subst j; cases h
  have h10 : j ≠ 10 := by intro e; subst j; cases h
  have h11 : j ≠ 11 := by intro e; subst j; cases h
  omega

private theorem neighbor_eleven {j : Nat}
    (h : cycleEdge 11 j = true) : j = 0 ∨ j = 10 := by
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) h).2
  have hj12 : j < 12 := by simpa [Gamma] using hj
  have h1 : j ≠ 1 := by intro e; subst j; cases h
  have h2 : j ≠ 2 := by intro e; subst j; cases h
  have h3 : j ≠ 3 := by intro e; subst j; cases h
  have h4 : j ≠ 4 := by intro e; subst j; cases h
  have h5 : j ≠ 5 := by intro e; subst j; cases h
  have h6 : j ≠ 6 := by intro e; subst j; cases h
  have h7 : j ≠ 7 := by intro e; subst j; cases h
  have h8 : j ≠ 8 := by intro e; subst j; cases h
  have h9 : j ≠ 9 := by intro e; subst j; cases h
  have h11 : j ≠ 11 := by intro e; subst j; cases h
  omega

private theorem neighbor_ten {j : Nat}
    (h : cycleEdge 10 j = true) : j = 9 ∨ j = 11 := by
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) h).2
  have hj12 : j < 12 := by simpa [Gamma] using hj
  have h0 : j ≠ 0 := by intro e; subst j; cases h
  have h1 : j ≠ 1 := by intro e; subst j; cases h
  have h2 : j ≠ 2 := by intro e; subst j; cases h
  have h3 : j ≠ 3 := by intro e; subst j; cases h
  have h4 : j ≠ 4 := by intro e; subst j; cases h
  have h5 : j ≠ 5 := by intro e; subst j; cases h
  have h6 : j ≠ 6 := by intro e; subst j; cases h
  have h7 : j ≠ 7 := by intro e; subst j; cases h
  have h8 : j ≠ 8 := by intro e; subst j; cases h
  have h10 : j ≠ 10 := by intro e; subst j; cases h
  omega

private theorem neighbor_nine {j : Nat}
    (h : cycleEdge 9 j = true) : j = 8 ∨ j = 10 := by
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) h).2
  have hj12 : j < 12 := by simpa [Gamma] using hj
  have h0 : j ≠ 0 := by intro e; subst j; cases h
  have h1 : j ≠ 1 := by intro e; subst j; cases h
  have h2 : j ≠ 2 := by intro e; subst j; cases h
  have h3 : j ≠ 3 := by intro e; subst j; cases h
  have h4 : j ≠ 4 := by intro e; subst j; cases h
  have h5 : j ≠ 5 := by intro e; subst j; cases h
  have h6 : j ≠ 6 := by intro e; subst j; cases h
  have h7 : j ≠ 7 := by intro e; subst j; cases h
  have h9 : j ≠ 9 := by intro e; subst j; cases h
  have h11 : j ≠ 11 := by intro e; subst j; cases h
  omega

private theorem neighbor_eight {j : Nat}
    (h : cycleEdge 8 j = true) : j = 7 ∨ j = 9 := by
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) h).2
  have hj12 : j < 12 := by simpa [Gamma] using hj
  have h0 : j ≠ 0 := by intro e; subst j; cases h
  have h1 : j ≠ 1 := by intro e; subst j; cases h
  have h2 : j ≠ 2 := by intro e; subst j; cases h
  have h3 : j ≠ 3 := by intro e; subst j; cases h
  have h4 : j ≠ 4 := by intro e; subst j; cases h
  have h5 : j ≠ 5 := by intro e; subst j; cases h
  have h6 : j ≠ 6 := by intro e; subst j; cases h
  have h8 : j ≠ 8 := by intro e; subst j; cases h
  have h10 : j ≠ 10 := by intro e; subst j; cases h
  have h11 : j ≠ 11 := by intro e; subst j; cases h
  omega

private theorem neighbor_seven {j : Nat}
    (h : cycleEdge 7 j = true) : j = 6 ∨ j = 8 := by
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) h).2
  have hj12 : j < 12 := by simpa [Gamma] using hj
  have h0 : j ≠ 0 := by intro e; subst j; cases h
  have h1 : j ≠ 1 := by intro e; subst j; cases h
  have h2 : j ≠ 2 := by intro e; subst j; cases h
  have h3 : j ≠ 3 := by intro e; subst j; cases h
  have h4 : j ≠ 4 := by intro e; subst j; cases h
  have h5 : j ≠ 5 := by intro e; subst j; cases h
  have h7 : j ≠ 7 := by intro e; subst j; cases h
  have h9 : j ≠ 9 := by intro e; subst j; cases h
  have h10 : j ≠ 10 := by intro e; subst j; cases h
  have h11 : j ≠ 11 := by intro e; subst j; cases h
  omega

private theorem neighbor_six {j : Nat}
    (h : cycleEdge 6 j = true) : j = 5 ∨ j = 7 := by
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) h).2
  have hj12 : j < 12 := by simpa [Gamma] using hj
  have h0 : j ≠ 0 := by intro e; subst j; cases h
  have h1 : j ≠ 1 := by intro e; subst j; cases h
  have h2 : j ≠ 2 := by intro e; subst j; cases h
  have h3 : j ≠ 3 := by intro e; subst j; cases h
  have h4 : j ≠ 4 := by intro e; subst j; cases h
  have h6 : j ≠ 6 := by intro e; subst j; cases h
  have h8 : j ≠ 8 := by intro e; subst j; cases h
  have h9 : j ≠ 9 := by intro e; subst j; cases h
  have h10 : j ≠ 10 := by intro e; subst j; cases h
  have h11 : j ≠ 11 := by intro e; subst j; cases h
  omega

private theorem neighbor_five {j : Nat}
    (h : cycleEdge 5 j = true) : j = 4 ∨ j = 6 := by
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) h).2
  have hj12 : j < 12 := by simpa [Gamma] using hj
  have h0 : j ≠ 0 := by intro e; subst j; cases h
  have h1 : j ≠ 1 := by intro e; subst j; cases h
  have h2 : j ≠ 2 := by intro e; subst j; cases h
  have h3 : j ≠ 3 := by intro e; subst j; cases h
  have h5 : j ≠ 5 := by intro e; subst j; cases h
  have h7 : j ≠ 7 := by intro e; subst j; cases h
  have h8 : j ≠ 8 := by intro e; subst j; cases h
  have h9 : j ≠ 9 := by intro e; subst j; cases h
  have h10 : j ≠ 10 := by intro e; subst j; cases h
  have h11 : j ≠ 11 := by intro e; subst j; cases h
  omega

private theorem neighbor_four {j : Nat}
    (h : cycleEdge 4 j = true) : j = 3 ∨ j = 5 := by
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) h).2
  have hj12 : j < 12 := by simpa [Gamma] using hj
  have h0 : j ≠ 0 := by intro e; subst j; cases h
  have h1 : j ≠ 1 := by intro e; subst j; cases h
  have h2 : j ≠ 2 := by intro e; subst j; cases h
  have h4 : j ≠ 4 := by intro e; subst j; cases h
  have h6 : j ≠ 6 := by intro e; subst j; cases h
  have h7 : j ≠ 7 := by intro e; subst j; cases h
  have h8 : j ≠ 8 := by intro e; subst j; cases h
  have h9 : j ≠ 9 := by intro e; subst j; cases h
  have h10 : j ≠ 10 := by intro e; subst j; cases h
  have h11 : j ≠ 11 := by intro e; subst j; cases h
  omega

private theorem endpoint_walk_single
    (walk : CWalk cycleEdge 3 3) (hnodup : walk.vertices.Nodup) :
    walk.vertices = [3] := by
  cases walk with
  | single _ => rfl
  | cons _ rest =>
      have hp := List.nodup_cons.mp hnodup
      exact absurd (CWalk.end_mem_vertices rest) hp.1

private theorem cycle_walk_arcs
    {start finish : Nat} (walk : CWalk cycleEdge start finish)
    (hstart : start = 0) (hfinish : finish = 3)
    (hnodup : walk.vertices.Nodup) :
    walk.vertices = [0, 1, 2, 3] ∨
      walk.vertices = [0, 11, 10, 9, 8, 7, 6, 5, 4, 3] := by
  subst start
  subst finish
  cases walk with
  | @cons _ next _ hedge rest =>
      have hnd0 := List.nodup_cons.mp hnodup
      rcases neighbor_zero hedge with hnext | hnext
      · subst next
        cases rest with
        | @cons _ next2 _ hedge2 rest2 =>
            have hnd1 := List.nodup_cons.mp hnd0.2
            rcases neighbor_one hedge2 with hnext2 | hnext2
            · subst next2
              exact absurd
                (List.mem_cons_of_mem 1 (CWalk.start_mem_vertices rest2))
                hnd0.1
            · subst next2
              cases rest2 with
              | @cons _ next3 _ hedge3 rest3 =>
                  have hnd2 := List.nodup_cons.mp hnd1.2
                  rcases neighbor_two hedge3 with hnext3 | hnext3
                  · subst next3
                    exact absurd
                      (List.mem_cons_of_mem 2
                        (CWalk.start_mem_vertices rest3)) hnd1.1
                  · subst next3
                    left
                    simp only [CWalk.vertices]
                    rw [endpoint_walk_single rest3 hnd2.2]
      · subst next
        cases rest with
        | @cons _ next2 _ hedge2 rest2 =>
            have hnd11 := List.nodup_cons.mp hnd0.2
            rcases neighbor_eleven hedge2 with hnext2 | hnext2
            · subst next2
              exact absurd
                (List.mem_cons_of_mem 11 (CWalk.start_mem_vertices rest2))
                hnd0.1
            · subst next2
              cases rest2 with
              | @cons _ next3 _ hedge3 rest3 =>
                  have hnd10 := List.nodup_cons.mp hnd11.2
                  rcases neighbor_ten hedge3 with hnext3 | hnext3
                  · subst next3
                    cases rest3 with
                    | @cons _ next4 _ hedge4 rest4 =>
                        have hnd9 := List.nodup_cons.mp hnd10.2
                        rcases neighbor_nine hedge4 with hnext4 | hnext4
                        · subst next4
                          cases rest4 with
                          | @cons _ next5 _ hedge5 rest5 =>
                              have hnd8 := List.nodup_cons.mp hnd9.2
                              rcases neighbor_eight hedge5 with
                                hnext5 | hnext5
                              · subst next5
                                cases rest5 with
                                | @cons _ next6 _ hedge6 rest6 =>
                                    have hnd7 :=
                                      List.nodup_cons.mp hnd8.2
                                    rcases neighbor_seven hedge6 with
                                      hnext6 | hnext6
                                    · subst next6
                                      cases rest6 with
                                      | @cons _ next7 _ hedge7 rest7 =>
                                          have hnd6 :=
                                            List.nodup_cons.mp hnd7.2
                                          rcases neighbor_six hedge7 with
                                            hnext7 | hnext7
                                          · subst next7
                                            cases rest7 with
                                            | @cons _ next8 _ hedge8 rest8 =>
                                                have hnd5 :=
                                                  List.nodup_cons.mp hnd6.2
                                                rcases neighbor_five hedge8
                                                  with hnext8 | hnext8
                                                · subst next8
                                                  cases rest8 with
                                                  | @cons _ next9 _ hedge9 rest9 =>
                                                      have hnd4 :=
                                                        List.nodup_cons.mp
                                                          hnd5.2
                                                      rcases neighbor_four
                                                        hedge9 with
                                                        hnext9 | hnext9
                                                      · subst next9
                                                        right
                                                        simp only
                                                          [CWalk.vertices]
                                                        rw [endpoint_walk_single
                                                          rest9 hnd4.2]
                                                      · subst next9
                                                        exact absurd
                                                          (List.mem_cons_of_mem
                                                            4
                                                            (CWalk.start_mem_vertices
                                                              rest9)) hnd5.1
                                                · subst next8
                                                  exact absurd
                                                    (List.mem_cons_of_mem 5
                                                      (CWalk.start_mem_vertices
                                                        rest8)) hnd6.1
                                          · subst next7
                                            exact absurd
                                              (List.mem_cons_of_mem 6
                                                (CWalk.start_mem_vertices
                                                  rest7)) hnd7.1
                                    · subst next6
                                      exact absurd
                                        (List.mem_cons_of_mem 7
                                          (CWalk.start_mem_vertices rest6))
                                        hnd8.1
                              · subst next5
                                exact absurd
                                  (List.mem_cons_of_mem 8
                                    (CWalk.start_mem_vertices rest5)) hnd9.1
                        · subst next4
                          exact absurd
                            (List.mem_cons_of_mem 9
                              (CWalk.start_mem_vertices rest4)) hnd10.1
                  · subst next3
                    exact absurd
                      (List.mem_cons_of_mem 10
                        (CWalk.start_mem_vertices rest3)) hnd11.1

private theorem badV3_polyAt_index {i : Nat} (hi : i < Gamma.length)
    (hbad : badV3 (polyAt Gamma i) = true) : i = 3 := by
  have hi12 : i < 12 := by simpa [Gamma] using hi
  have h0 : i ≠ 0 := by intro e; subst i; cases hbad
  have h1 : i ≠ 1 := by intro e; subst i; cases hbad
  have h2 : i ≠ 2 := by intro e; subst i; cases hbad
  have h4 : i ≠ 4 := by intro e; subst i; cases hbad
  have h5 : i ≠ 5 := by intro e; subst i; cases hbad
  have h6 : i ≠ 6 := by intro e; subst i; cases hbad
  have h7 : i ≠ 7 := by intro e; subst i; cases hbad
  have h8 : i ≠ 8 := by intro e; subst i; cases hbad
  have h9 : i ≠ 9 := by intro e; subst i; cases hbad
  have h10 : i ≠ 10 := by intro e; subst i; cases hbad
  have h11 : i ≠ 11 := by intro e; subst i; cases hbad
  omega

theorem source_path_is_unbalanced_arc :
    let facts := exceptionalSourceFactsOfMem Gamma qAll markV0 badV3
      pair pair_mem
    let path := sourceExceptionalPath Gamma qAll markV0 badV3 pair facts
    path.indexWalk.vertices = [0, 1, 2, 3] ∨
      path.indexWalk.vertices = [0, 11, 10, 9, 8, 7, 6, 5, 4, 3] := by
  dsimp only
  let facts := exceptionalSourceFactsOfMem Gamma qAll markV0 badV3
    pair pair_mem
  let path := sourceExceptionalPath Gamma qAll markV0 badV3 pair facts
  have hstart : exceptionalMarkedIndex Gamma markV0 badV3 pair = 0 := by
    rfl
  have hp := forwardSeed_parts Gamma.length
    (bitMask pair.1) (bitMask pair.2) (predAt Gamma badV3) path.seed_true
  have hfinish : path.seed = 3 := badV3_polyAt_index hp.1 hp.2.2.2
  exact cycle_walk_arcs path.indexWalk hstart hfinish path.index_nodup

theorem routed_path_safe_fails :
    routedExternalCompatibleB Gamma qAll markV0 badV3 entry = false := by
  unfold routedExternalCompatibleB entryRoutedExternal
    routedLeftResidual routedRightResidual exceptionalPathSafe entry
  dsimp only
  rcases source_path_is_unbalanced_arc with h | h
  · rw [h]
    decide
  · rw [h]
    decide

theorem component_right_safeB_fails :
    componentRightSafeB Gamma qAll markV0 badV3 entry = false := by
  unfold componentRightSafeB routedResidualPathSafeB routedRightResidual
    exceptionalPathSafe entry
  dsimp only
  rcases source_path_is_unbalanced_arc with h | h
  · rw [h]
    decide
  · rw [h]
    decide

theorem component_left_safeB_fails :
    componentLeftSafeB Gamma qAll markV0 badV3 entry = false := by
  unfold componentLeftSafeB routedResidualPathSafeB routedLeftResidual
    exceptionalPathSafe entry
  dsimp only
  rcases source_path_is_unbalanced_arc with h | h
  · rw [h]
    decide
  · rw [h]
    decide

theorem entry_mem_threeBranchResidual :
    entry ∈ threeBranchResidualSource Gamma qAll markV0 badV3 := by
  apply List.mem_filter.mpr
  refine ⟨?_, by simp [component_left_safeB_fails]⟩
  apply List.mem_filter.mpr
  refine ⟨?_, by simp [component_right_safeB_fails]⟩
  apply List.mem_filter.mpr
  exact ⟨entry_mem_full, by simp [routed_path_safe_fails]⟩

theorem residual_invariant :
    ThreeBranchResidualInvariant Gamma qAll markV0 badV3 entry :=
  threeBranchResidualSource_invariant Gamma qAll markV0 badV3 entry
    entry_mem_threeBranchResidual

/-! ## Exact unequal ears and the sharp reserve deficit -/

def shortArc : PairedPath (incAtDistinct Gamma) 0 3 :=
  .pair (x := 0) (y := 1) (z := 2) (t := 3)
    (by rfl) (by rfl) (.last (by rfl))

def longArc : PairedPath (incAtDistinct Gamma) 0 3 :=
  .pair (x := 0) (y := 11) (z := 10) (t := 3)
    (by rfl) (by rfl)
    (.pair (x := 10) (y := 9) (z := 8) (t := 3)
      (by rfl) (by rfl)
      (.pair (x := 8) (y := 7) (z := 6) (t := 3)
        (by rfl) (by rfl)
        (.pair (x := 6) (y := 5) (z := 4) (t := 3)
          (by rfl) (by rfl) (.last (by rfl)))))

private theorem cycleEdge_symm (i j : Nat)
    (h : incAtDistinct Gamma i j = true) :
    incAtDistinct Gamma j i = true := by
  rw [incAtDistinct_symm Gamma]
  exact h

theorem unequal_pair_counts :
    shortArc.pairCount = 1 ∧ longArc.pairCount = 4 := by
  decide

def extractedFuel : BlockCutFuel := .leaf 1 4

theorem extractedFuel_unbalanced :
    complementaryFuelBalancedB extractedFuel = false := by
  rfl

theorem longArc_bounce_length :
    (longArc.bounceWalk cycleEdge_symm).vertices.length = 18 := by
  rw [PairedPath.bounceWalk_length cycleEdge_symm longArc]
  decide

theorem sharp_target_vertex_capacity : Gamma.length + 1 = 13 := by
  rfl

theorem long_square_sharp_overflow :
    (longArc.bounceWalk cycleEdge_symm).vertices.length =
      (Gamma.length + 1) + 5 := by
  rw [longArc_bounce_length]
  rfl

/-! ## Exhaustive compatible-reserve classification -/

def longInterior : List (Polymer TL) :=
  [V4, V5, V6, V7, V8, V9, V10, V11]

def supportedOnLongInteriorB (bits : OccBitVec Gamma.length) : Bool :=
  (selectByBits Gamma bits).all
    (fun X => decide (X ∈ longInterior))

def longReserveCandidateB (bits : OccBitVec Gamma.length) : Bool :=
  supportedOnLongInteriorB bits &&
    familyCompatibleB (selectByBits Gamma bits)

def longReserveCandidates : List (OccBitVec Gamma.length) :=
  (bitVectors Gamma.length).filter longReserveCandidateB

set_option maxRecDepth 1000000 in
theorem longReserveCandidates_at_most_four :
    longReserveCandidates.all
      (fun bits => decide ((selectByBits Gamma bits).length ≤ 4)) = true := by
  decide

theorem compatible_long_reserve_le_four
    (bits : OccBitVec Gamma.length)
    (hsupport : supportedOnLongInteriorB bits = true)
    (hcompatible : familyCompatibleB (selectByBits Gamma bits) = true) :
    (selectByBits Gamma bits).length ≤ 4 := by
  have hcandidate : bits ∈ longReserveCandidates := by
    apply List.mem_filter.mpr
    exact ⟨bitVectors_complete bits,
      (Bool.and_eq_true _ _).mpr ⟨hsupport, hcompatible⟩⟩
  have hcheck := List.all_eq_true.mp longReserveCandidates_at_most_four
    bits hcandidate
  exact of_decide_eq_true hcheck

/-- Data required by any single-code repair that covers the sharp five-slot
overflow solely with a compatible external mask on the long interior. -/
structure SingleExternalLongSquareReserve where
  reserve : OccBitVec Gamma.length
  supported : supportedOnLongInteriorB reserve = true
  compatible : familyCompatibleB (selectByBits Gamma reserve) = true
  coversOverflow : 5 ≤ (selectByBits Gamma reserve).length

theorem no_single_external_long_square_reserve :
    ¬ Nonempty SingleExternalLongSquareReserve := by
  intro h
  obtain ⟨cert⟩ := h
  have hle := compatible_long_reserve_le_four cert.reserve
    cert.supported cert.compatible
  have hge := cert.coversOverflow
  omega

theorem maximum_reserve_fails_sharp_fuel :
    externalReserveFitsB 18 4 13 = false := by
  rfl

/-- For a one-pair short ear, long ears of one, two, and three pairs pass
the sharp maximum-compatible-reserve count.  Four pairs is the first failure. -/
theorem one_pair_short_first_reserve_failure :
    externalReserveFitsB 6 1 7 = true ∧
      externalReserveFitsB 10 2 9 = true ∧
      externalReserveFitsB 14 3 11 = true ∧
      externalReserveFitsB 18 4 13 = false := by
  decide

#print axioms pair_mem
#print axioms source_path_is_unbalanced_arc
#print axioms routed_path_safe_fails
#print axioms component_right_safeB_fails
#print axioms component_left_safeB_fails
#print axioms entry_mem_threeBranchResidual
#print axioms residual_invariant
#print axioms unequal_pair_counts
#print axioms extractedFuel_unbalanced
#print axioms longArc_bounce_length
#print axioms long_square_sharp_overflow
#print axioms longReserveCandidates_at_most_four
#print axioms compatible_long_reserve_le_four
#print axioms no_single_external_long_square_reserve
#print axioms maximum_reserve_fails_sharp_fuel
#print axioms one_pair_short_first_reserve_failure

end YMGap.Continuum.XiExceptionalExternalReserveLimitFence
