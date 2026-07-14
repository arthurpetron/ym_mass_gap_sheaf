/-
# An explicit unbounded tower of compensated graph refinements

The pathwise gap theorem applies to any certified finite refinement path.
Here a path is generated constructively: exact maxima of the currently used
edge and vertex identifiers provide two fresh identifiers, and a pointed old
edge is subdivided repeatedly.  The resulting tower has two more graph edges
at every level, preserves the complete support-pruned correlator, and carries
the same `(1/8)^2` spectral separator at every finite level.

This is an explicit unbounded finite-volume family.  It is not yet a
thermodynamic colimit, a four-dimensional cofinal lattice family, or a
continuum limit.
-/

import YMGap.Continuum.SU2FiniteTrivalentPacketGraphWeightedGapTransport

namespace YMGap.Continuum.SU2FiniteTrivalentPacketGraphCanonicalRefinementTower

set_option maxHeartbeats 1000000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinement
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCompensatedRefinementPath
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphSupportedRefinementPath
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphWeightedGapTransport
open YMGap.Continuum.SU2PeterWeylWilsonBlock

local infix:50 " ≈ " => Q'.eqv

/-! ## Constructive fresh identifiers -/

def edgeIdMax : List Nat → Nat
  | [] => 0
  | edge :: rest => Nat.max edge (edgeIdMax rest)

theorem edge_le_edgeIdMax {edge : Nat} : ∀ {edges : List Nat},
    edge ∈ edges → edge ≤ edgeIdMax edges
  | [], h => by cases h
  | head :: rest, h => by
      simp only [List.mem_cons] at h
      rcases h with rfl | hrest
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (edge_le_edgeIdMax hrest)
          (Nat.le_max_right _ _)

def vertexIdMax : List TrivalentVertex → Nat
  | [] => 0
  | v :: rest =>
      Nat.max v.1 (Nat.max v.2.1 (Nat.max v.2.2 (vertexIdMax rest)))

theorem vertex_coords_le_vertexIdMax {v : TrivalentVertex} :
    ∀ {vertices : List TrivalentVertex}, v ∈ vertices →
      v.1 ≤ vertexIdMax vertices ∧
      v.2.1 ≤ vertexIdMax vertices ∧
      v.2.2 ≤ vertexIdMax vertices
  | [], h => by cases h
  | head :: rest, h => by
      simp only [List.mem_cons] at h
      rcases h with rfl | hrest
      · constructor
        · exact Nat.le_max_left _ _
        constructor
        · exact Nat.le_trans (Nat.le_max_left _ _)
            (Nat.le_max_right _ _)
        · exact Nat.le_trans
            (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
            (Nat.le_max_right _ _)
      · have ih := vertex_coords_le_vertexIdMax hrest
        have htail : vertexIdMax rest ≤ vertexIdMax (head :: rest) :=
          Nat.le_trans (Nat.le_max_right _ _)
            (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
        exact ⟨Nat.le_trans ih.1 htail,
          Nat.le_trans ih.2.1 htail, Nat.le_trans ih.2.2 htail⟩

def stateIdMax {K : Nat} (S : CompensatedGraphState K) : Nat :=
  Nat.max (edgeIdMax S.edges) (vertexIdMax S.vertices)

def canonicalNewEdge {K : Nat} (S : CompensatedGraphState K) : Nat :=
  stateIdMax S + 1

def canonicalVacuumEdge {K : Nat} (S : CompensatedGraphState K) : Nat :=
  stateIdMax S + 2

theorem canonicalNewEdge_fresh {K : Nat} (S : CompensatedGraphState K) :
    canonicalNewEdge S ∉ S.edges := by
  intro hmem
  have hle := Nat.le_trans (edge_le_edgeIdMax hmem)
    (Nat.le_max_left (edgeIdMax S.edges) (vertexIdMax S.vertices))
  have hlt : stateIdMax S < canonicalNewEdge S := by
    unfold canonicalNewEdge
    omega
  exact (Nat.not_lt_of_ge hle) hlt

theorem canonicalVacuumEdge_fresh {K : Nat} (S : CompensatedGraphState K) :
    canonicalVacuumEdge S ∉ S.edges := by
  intro hmem
  have hle := Nat.le_trans (edge_le_edgeIdMax hmem)
    (Nat.le_max_left (edgeIdMax S.edges) (vertexIdMax S.vertices))
  have hlt : stateIdMax S < canonicalVacuumEdge S := by
    unfold canonicalVacuumEdge
    omega
  exact (Nat.not_lt_of_ge hle) hlt

theorem canonicalNewEdge_vertices_avoid {K : Nat}
    (S : CompensatedGraphState K) :
    VerticesAvoid (canonicalNewEdge S) S.vertices := by
  intro v hv
  have hc := vertex_coords_le_vertexIdMax hv
  have hmax : vertexIdMax S.vertices ≤ stateIdMax S :=
    Nat.le_max_right _ _
  unfold canonicalNewEdge
  exact ⟨by omega, by omega, by omega⟩

theorem canonicalVacuumEdge_vertices_avoid {K : Nat}
    (S : CompensatedGraphState K) :
    VerticesAvoid (canonicalVacuumEdge S) S.vertices := by
  intro v hv
  have hc := vertex_coords_le_vertexIdMax hv
  have hmax : vertexIdMax S.vertices ≤ stateIdMax S :=
    Nat.le_max_right _ _
  unfold canonicalVacuumEdge
  exact ⟨by omega, by omega, by omega⟩

/-! ## Pointed states and the canonical tower -/

/-- A compensated graph with one retained edge chosen for repeated
subdivision. -/
structure PointedCompensatedGraphState (K : Nat) where
  state : CompensatedGraphState K
  oldEdge : Nat
  old_mem : oldEdge ∈ state.edges

def canonicalMove {K : Nat} (P : PointedCompensatedGraphState K) :
    IdentityRefinementMove P.state where
  oldEdge := P.oldEdge
  newEdge := canonicalNewEdge P.state
  vacuumEdge := canonicalVacuumEdge P.state
  old_mem := P.old_mem
  new_fresh := canonicalNewEdge_fresh P.state
  vacuum_fresh := canonicalVacuumEdge_fresh P.state
  new_ne_old := by
    have hle := Nat.le_trans (edge_le_edgeIdMax P.old_mem)
      (Nat.le_max_left (edgeIdMax P.state.edges)
        (vertexIdMax P.state.vertices))
    have hlt : stateIdMax P.state < canonicalNewEdge P.state := by
      unfold canonicalNewEdge
      omega
    exact Nat.ne_of_gt (Nat.lt_of_le_of_lt hle hlt)
  vacuum_ne_old := by
    have hle := Nat.le_trans (edge_le_edgeIdMax P.old_mem)
      (Nat.le_max_left (edgeIdMax P.state.edges)
        (vertexIdMax P.state.vertices))
    have hlt : stateIdMax P.state < canonicalVacuumEdge P.state := by
      unfold canonicalVacuumEdge
      omega
    exact Nat.ne_of_gt (Nat.lt_of_le_of_lt hle hlt)
  new_ne_vacuum := by
    unfold canonicalNewEdge canonicalVacuumEdge
    omega
  vertices_avoid_new := canonicalNewEdge_vertices_avoid P.state
  vertices_avoid_vacuum := canonicalVacuumEdge_vertices_avoid P.state

def canonicalNext {K : Nat} (P : PointedCompensatedGraphState K) :
    PointedCompensatedGraphState K where
  state := (canonicalMove P).next
  oldEdge := P.oldEdge
  old_mem := by
    exact List.mem_cons_of_mem (canonicalVacuumEdge P.state)
      (List.mem_cons_of_mem (canonicalNewEdge P.state) P.old_mem)

def canonicalTower {K : Nat} (P : PointedCompensatedGraphState K) :
    Nat → PointedCompensatedGraphState K
  | 0 => P
  | n + 1 => canonicalNext (canonicalTower P n)

/-- The first `n` canonical subdivisions form a certified refinement path. -/
theorem canonicalTower_path {K : Nat} (P : PointedCompensatedGraphState K) :
    ∀ n : Nat, CompensatedRefinementPath P.state (canonicalTower P n).state
  | 0 => .refl _
  | n + 1 => by
      let Q := canonicalTower P n
      have hprefix := canonicalTower_path P n
      have hstep : CompensatedRefinementPath Q.state (canonicalNext Q).state :=
        .step (canonicalMove Q) (.refl _)
      exact hprefix.trans hstep

/-- Each canonical subdivision adds exactly two graph edges. -/
theorem canonicalTower_edge_length {K : Nat}
    (P : PointedCompensatedGraphState K) : ∀ n : Nat,
    (canonicalTower P n).state.edges.length =
      P.state.edges.length + 2 * n
  | 0 => by simp [canonicalTower]
  | n + 1 => by
      change ((canonicalMove (canonicalTower P n)).next).edges.length =
        P.state.edges.length + 2 * (n + 1)
      change (canonicalVacuumEdge (canonicalTower P n).state ::
        canonicalNewEdge (canonicalTower P n).state ::
        (canonicalTower P n).state.edges).length =
        P.state.edges.length + 2 * (n + 1)
      simp only [List.length_cons]
      rw [canonicalTower_edge_length P n]
      omega

/-- Every finite tower level has exactly the same support-pruned correlator
as the initial state. -/
theorem canonicalTower_supportedCorr {K : Nat}
    (P : PointedCompensatedGraphState K) (n t : Nat) :
    supportedGraphCorr (canonicalTower P n).state t ≈
      supportedGraphCorr P.state t :=
  path_supportedGraphCorr_invariant (canonicalTower_path P n) t

/-- If the initial pointed graph is uncompensated, every finite level has the
same ordinary support-pruned spectral separator `(1/8)^2`. -/
theorem canonicalTower_uniform_gap {K : Nat}
    (P : PointedCompensatedGraphState K)
    (hcopy : P.state.copiedEdges = []) (n : Nat) :
    SpectralGapBound
      (supportedGraphSpectralModel (canonicalTower P n).state)
      (eighth * eighth) :=
  path_supported_gap_from_uncompensated (canonicalTower_path P n) hcopy

end YMGap.Continuum.SU2FiniteTrivalentPacketGraphCanonicalRefinementTower

#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCanonicalRefinementTower.canonicalNewEdge_fresh
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCanonicalRefinementTower.canonicalMove
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCanonicalRefinementTower.canonicalTower_path
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCanonicalRefinementTower.canonicalTower_edge_length
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCanonicalRefinementTower.canonicalTower_supportedCorr
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphCanonicalRefinementTower.canonicalTower_uniform_gap
