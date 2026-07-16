/-
# Fresh Cartesian identifiers for one production link resolver

The production `fuseLabels` block mixes numerical plaquette identifiers with
one eight-coordinate auxiliary block reserved for the physical lattice link.
Before a recursive finite-Fubini argument can identify that graph block with
the left-associated fusion kernel, those coordinates must be known to be
genuinely distinct.

This file proves that the incident plaquette identifiers are duplicate-free,
that every one of them lies strictly below the plaquette-edge boundary, and
that every reserved link-block identifier lies on or above that boundary.
Consequently the physical and auxiliary lists are disjoint and their
concatenation is duplicate-free.  These are statements about the actual box
identifiers, not a canonical surrogate.

Honest scope: identifier freshness removes the reindexing obstruction.  The
successor Fubini calculation and the equality with the packet kernel remain
separate obligations.
-/

import YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound

namespace YMGap.Continuum.Z4LinkIdentifierFreshness

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Continuum
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

private theorem nodup_map_of_injective {a b : Type} (f : a → b)
    (hf : ∀ {x y}, f x = f y → x = y) : ∀ {xs : List a},
    xs.Nodup → (xs.map f).Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
      have hp := List.nodup_cons.mp h
      apply List.nodup_cons.mpr
      refine ⟨?_, nodup_map_of_injective f hf hp.2⟩
      intro hmem
      obtain ⟨y, hy, heq⟩ := List.mem_map.mp hmem
      exact hp.1 ((hf heq) ▸ hy)

/-! ## 1. Duplicate-free numerical enumeration -/

theorem enumerateFrom_index_ge {a : Type} {start i : Nat} {x : a} :
    ∀ {xs : List a}, (i, x) ∈ enumerateFrom start xs → start ≤ i
  | [], h => by cases h
  | _ :: _, h => by
      simp only [enumerateFrom, List.mem_cons] at h
      rcases h with h | h
      · injection h with hi
        omega
      · have ht := enumerateFrom_index_ge h
        omega

theorem enumerateFrom_fst_nodup {a : Type} :
    ∀ (start : Nat) (xs : List a),
      ((enumerateFrom start xs).map Prod.fst).Nodup
  | _, [] => List.nodup_nil
  | start, x :: xs => by
      simp only [enumerateFrom, List.map_cons]
      apply List.nodup_cons.mpr
      refine ⟨?_, enumerateFrom_fst_nodup (start + 1) xs⟩
      intro hmem
      obtain ⟨indexed, hindexed, hfst⟩ := List.mem_map.mp hmem
      have hge := enumerateFrom_index_ge hindexed
      have heq : indexed.1 = start := hfst
      rw [heq] at hge
      omega

theorem enumerate_fst_nodup {a : Type} (xs : List a) :
    ((enumerate xs).map Prod.fst).Nodup :=
  enumerateFrom_fst_nodup 0 xs

theorem enumerateFrom_index_lt {a : Type} {start i : Nat} {x : a} :
    ∀ {xs : List a}, (i, x) ∈ enumerateFrom start xs →
      i < start + xs.length
  | [], h => by cases h
  | y :: ys, h => by
      simp only [enumerateFrom, List.mem_cons] at h
      rcases h with h | h
      · have hi : i = start := congrArg Prod.fst h
        rw [hi]
        simp
      · have ht := enumerateFrom_index_lt h
        simp only [List.length_cons]
        omega

theorem enumerate_index_lt {a : Type} {xs : List a} {i : Nat} {x : a}
    (h : (i, x) ∈ enumerate xs) : i < xs.length := by
  have ht := enumerateFrom_index_lt h
  simpa only [Nat.zero_add] using ht

/-! ## 2. The physical plaquette coordinates -/

/-- Incident plaquette identifiers are sampled from a duplicate-free global
enumeration, so no physical coordinate is summed twice locally. -/
theorem incidentPlaqIds_nodup (n : Nat) (ell : Z4Link) :
    (incidentPlaqIds n ell).Nodup := by
  unfold incidentPlaqIds
  exact (List.filter_sublist.map Prod.fst).nodup
    (enumerate_fst_nodup (boxPlaquettes n))

/-- Every physical identifier is strictly below the first reserved auxiliary
identifier. -/
theorem incidentPlaqId_lt_count {n : Nat} {ell : Z4Link} {edge : Nat}
    (he : edge ∈ incidentPlaqIds n ell) :
    edge < plaquetteEdgeCount n := by
  obtain ⟨p, hp, _⟩ := mem_incidentPlaqIds.mp he
  unfold plaquetteEdgeCount
  exact enumerate_index_lt hp

/-! ## 3. The reserved auxiliary coordinates -/

theorem linkBlockBase_ge_count (n i : Nat) :
    plaquetteEdgeCount n ≤ linkBlockBase n i := by
  unfold linkBlockBase
  omega

theorem mem_linkBlockEdges_iff {n i edge : Nat} :
    edge ∈ linkBlockEdges n i ↔
      ∃ j, j < 8 ∧ edge = linkBlockBase n i + j := by
  unfold linkBlockEdges
  constructor
  · intro h
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
    exact ⟨j, List.mem_range.mp hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

theorem linkBlockEdge_ge_count {n i edge : Nat}
    (he : edge ∈ linkBlockEdges n i) :
    plaquetteEdgeCount n ≤ edge := by
  obtain ⟨j, _, rfl⟩ := mem_linkBlockEdges_iff.mp he
  have hbase := linkBlockBase_ge_count n i
  omega

theorem linkBlockEdges_nodup (n i : Nat) :
    (linkBlockEdges n i).Nodup := by
  unfold linkBlockEdges
  apply nodup_map_of_injective
  · intro x y h
    omega
  · decide

/-! ## 4. Actual local Cartesian freshness -/

theorem incidentPlaqIds_disjoint_linkBlockEdges (n i : Nat) (ell : Z4Link) :
    ∀ edge, edge ∈ incidentPlaqIds n ell →
      edge ∈ linkBlockEdges n i → False := by
  intro edge hphysical haux
  have hlt := incidentPlaqId_lt_count hphysical
  have hge := linkBlockEdge_ge_count haux
  omega

/-- One actual link's physical plaquette coordinates followed by its reserved
auxiliary block form a duplicate-free Cartesian coordinate list. -/
theorem incidentPlaqIds_append_linkBlockEdges_nodup
    (n i : Nat) (ell : Z4Link) :
    (incidentPlaqIds n ell ++ linkBlockEdges n i).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨incidentPlaqIds_nodup n ell, linkBlockEdges_nodup n i, ?_⟩
  intro x hx y hy hxy
  subst y
  exact incidentPlaqIds_disjoint_linkBlockEdges n i ell x hx hy

/-! ## 5. Every production vertex coordinate lies in the fresh list -/

/-- Structural classification of every identifier used by a `fuseChain`.
Besides the physical inputs and the vacuum terminator, an identifier is one
of the successive auxiliary coordinates whose index is justified by the
remaining tail length. -/
theorem fuseChain_vertex_edge_classify (vacuum : Nat) :
    ∀ (tail : List Nat) (aux left right : Nat) (v : TrivalentVertex)
      (edge : Nat),
      v ∈ fuseChain vacuum aux left right tail →
      VertexContains edge v →
      edge = vacuum ∨ edge ∈ left :: right :: tail ∨
        ∃ j, edge = aux + j ∧
          j + 3 ≤ (right :: tail).length
  | [], aux, left, right, v, edge, hv, he => by
      simp only [fuseChain, List.mem_singleton] at hv
      subst v
      unfold VertexContains at he
      rcases he with he | he | he
      · exact Or.inr (Or.inl (by simp [he]))
      · exact Or.inr (Or.inl (by simp [he]))
      · exact Or.inl he
  | [last], aux, left, right, v, edge, hv, he => by
      simp only [fuseChain, List.mem_singleton] at hv
      subst v
      unfold VertexContains at he
      rcases he with he | he | he
      · exact Or.inr (Or.inl (by simp [he]))
      · exact Or.inr (Or.inl (by simp [he]))
      · exact Or.inr (Or.inl (by simp [he]))
  | next :: after :: rest, aux, left, right, v, edge, hv, he => by
      simp only [fuseChain, List.mem_cons] at hv
      rcases hv with hv | hv
      · subst v
        unfold VertexContains at he
        rcases he with he | he | he
        · exact Or.inr (Or.inl (by simp [he]))
        · exact Or.inr (Or.inl (by simp [he]))
        · refine Or.inr (Or.inr ⟨0, ?_, ?_⟩)
          · simpa using he
          · simp
      · obtain hvac | hinput | ⟨j, hedge, hj⟩ :=
          fuseChain_vertex_edge_classify vacuum (after :: rest)
            (aux + 1) aux next v edge hv he
        · exact Or.inl hvac
        · simp only [List.mem_cons] at hinput
          rcases hinput with haux | hphysical
          · refine Or.inr (Or.inr ⟨0, ?_, ?_⟩)
            · simpa using haux
            · simp
          · exact Or.inr (Or.inl (by simp [hphysical]))
        · refine Or.inr (Or.inr ⟨j + 1, ?_, ?_⟩)
          · omega
          · simp only [List.length_cons] at hj ⊢
            omega

/-- The corresponding classification for the public `fuseLabels` resolver.
The auxiliary offset is stated against the length of the complete physical
input list. -/
theorem fuseLabels_vertex_edge_classify (vacuum aux : Nat) :
    ∀ (labels : List Nat) (v : TrivalentVertex) (edge : Nat),
      v ∈ fuseLabels vacuum aux labels →
      VertexContains edge v →
      edge = vacuum ∨ edge ∈ labels ∨
        ∃ j, edge = aux + j ∧ j + 4 ≤ labels.length
  | [], v, edge, hv, _ => by cases hv
  | [only], v, edge, hv, he => by
      simp only [fuseLabels, List.mem_singleton] at hv
      subst v
      unfold VertexContains at he
      rcases he with he | he | he
      · exact Or.inr (Or.inl (by simp [he]))
      · exact Or.inl he
      · exact Or.inl he
  | left :: right :: tail, v, edge, hv, he => by
      obtain hvac | hphysical | ⟨j, hedge, hj⟩ :=
        fuseChain_vertex_edge_classify vacuum tail aux left right v edge hv he
      · exact Or.inl hvac
      · exact Or.inr (Or.inl hphysical)
      · refine Or.inr (Or.inr ⟨j, hedge, ?_⟩)
        simp only [List.length_cons] at hj ⊢
        omega

/-- Every coordinate appearing at an actual link-resolution vertex belongs
to the duplicate-free physical-plus-reserved coordinate list proved above. -/
theorem linkResolutionVertex_edge_mem_localCoordinates
    {n i : Nat} {ell : Z4Link} {v : TrivalentVertex} {edge : Nat}
    (hv : v ∈ linkResolutionVertices n i ell)
    (he : VertexContains edge v) :
    edge ∈ incidentPlaqIds n ell ++ linkBlockEdges n i := by
  unfold linkResolutionVertices at hv
  obtain hedge | hphysical | ⟨j, hedge, hj⟩ :=
    fuseLabels_vertex_edge_classify
      (linkBlockBase n i) (linkBlockBase n i + 1)
      (incidentPlaqIds n ell) v edge hv he
  · apply List.mem_append_right
    apply mem_linkBlockEdges_iff.mpr
    exact ⟨0, by omega, by simpa using hedge⟩
  · exact List.mem_append_left _ hphysical
  · apply List.mem_append_right
    apply mem_linkBlockEdges_iff.mpr
    refine ⟨j + 1, ?_, ?_⟩
    · have hdegree := incidentPlaqIds_length_le_six n ell
      omega
    · omega

end YMGap.Continuum.Z4LinkIdentifierFreshness

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4LinkIdentifierFreshness.enumerateFrom_fst_nodup
#print axioms YMGap.Continuum.Z4LinkIdentifierFreshness.enumerate_index_lt
#print axioms YMGap.Continuum.Z4LinkIdentifierFreshness.incidentPlaqIds_nodup
#print axioms YMGap.Continuum.Z4LinkIdentifierFreshness.incidentPlaqId_lt_count
#print axioms YMGap.Continuum.Z4LinkIdentifierFreshness.linkBlockEdges_nodup
#print axioms YMGap.Continuum.Z4LinkIdentifierFreshness.incidentPlaqIds_disjoint_linkBlockEdges
#print axioms YMGap.Continuum.Z4LinkIdentifierFreshness.incidentPlaqIds_append_linkBlockEdges_nodup
#print axioms YMGap.Continuum.Z4LinkIdentifierFreshness.fuseChain_vertex_edge_classify
#print axioms YMGap.Continuum.Z4LinkIdentifierFreshness.fuseLabels_vertex_edge_classify
#print axioms YMGap.Continuum.Z4LinkIdentifierFreshness.linkResolutionVertex_edge_mem_localCoordinates
