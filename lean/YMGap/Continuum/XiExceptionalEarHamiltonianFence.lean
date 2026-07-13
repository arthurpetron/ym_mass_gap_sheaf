/-
# Hamiltonian-ear fence

The smallest branching bipartite component is a three-leaf star.  Between
two leaves its unique simple path omits the third leaf.  Thus a general mixed
component cannot be absorbed by assuming that one loop-erased carrier path
visits every residual occurrence.  Branches need a separate allocation layer
after the path-ear mechanism.
-/

import YMGap.Continuum.XiExceptionalMixedEarAbsorption

namespace YMGap.Continuum.XiExceptionalEarHamiltonianFence

open YMGap.Continuum.XiExceptionalPathExtraction

def starEdge (i j : Nat) : Bool :=
  (decide (i = 0) &&
      (decide (j = 1) || decide (j = 2) || decide (j = 3))) ||
    (decide (j = 0) &&
      (decide (i = 1) || decide (i = 2) || decide (i = 3)))

private theorem neighbor_one {j : Nat} (h : starEdge 1 j = true) :
    j = 0 := by
  simp [starEdge] at h
  exact h

private theorem neighbor_three {j : Nat} (h : starEdge 3 j = true) :
    j = 0 := by
  simp [starEdge] at h
  exact h

private theorem neighbor_zero {j : Nat} (h : starEdge 0 j = true) :
    j = 1 ∨ j = 2 ∨ j = 3 := by
  simp [starEdge] at h
  rcases h with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

private theorem end_mem_vertices
    {alpha : Type} {edge : alpha → alpha → Bool} :
    ∀ {x y : alpha} (walk : CWalk edge x y), y ∈ walk.vertices
  | _, _, .single _ => List.mem_cons_self
  | _, _, .cons _ rest =>
      List.mem_cons_of_mem _ (end_mem_vertices rest)

private theorem endpoint_walk_single
    (walk : CWalk starEdge 2 2) (hnodup : walk.vertices.Nodup) :
    walk.vertices = [2] := by
  cases walk with
  | single _ => rfl
  | cons hedge rest =>
      have hp := List.nodup_cons.mp hnodup
      exact absurd (end_mem_vertices rest) hp.1

/-- Every simple star walk from leaf `1` to leaf `2` is the unique
three-vertex path through the center. -/
theorem simple_leaf_walk_vertices (walk : CWalk starEdge 1 2)
    (hnodup : walk.vertices.Nodup) : walk.vertices = [1, 0, 2] := by
  cases walk with
  | @cons _ next _ hedge rest =>
      have hnext : next = 0 := neighbor_one hedge
      subst next
      have hnd1 := List.nodup_cons.mp hnodup
      cases rest with
      | @cons _ next2 _ hedge2 rest2 =>
          have hnd0 := List.nodup_cons.mp hnd1.2
          rcases neighbor_zero hedge2 with hnext2 | hnext2 | hnext2
          · subst next2
            exact absurd
              (List.mem_cons_of_mem 0 (CWalk.start_mem_vertices rest2)) hnd1.1
          · subst next2
            simp only [CWalk.vertices]
            rw [endpoint_walk_single rest2 hnd0.2]
          · subst next2
            cases rest2 with
            | @cons _ next3 _ hedge3 rest3 =>
                have hnd3 := List.nodup_cons.mp hnd0.2
                have hnext3 : next3 = 0 := neighbor_three hedge3
                subst next3
                exact absurd
                  (List.mem_cons_of_mem 3 (CWalk.start_mem_vertices rest3))
                  hnd0.1

/-- The remaining leaf cannot lie on a simple carrier path between the
other two leaves. -/
theorem simple_leaf_walk_omits_third (walk : CWalk starEdge 1 2)
    (hnodup : walk.vertices.Nodup) : 3 ∉ walk.vertices := by
  rw [simple_leaf_walk_vertices walk hnodup]
  decide

#print axioms simple_leaf_walk_vertices
#print axioms simple_leaf_walk_omits_third

end YMGap.Continuum.XiExceptionalEarHamiltonianFence
