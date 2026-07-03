/-
Closing the named `(D2)` structural residual `Ursell4DProgress.SepLatticeZ4`:
a genuine `SepLattice` metric refining the CLOSED degree-24 Z⁴ plaquette count
lattice `z4Chain` (`Continuum/ClusterCount4DProgress.lean`), hence an inhabitant
of the subtype

    SepLatticeZ4 := { S : SepLattice // S.toLattice = z4Chain.toLattice }.

# What is delivered (all PROVED, axiom-clean)

  * `sVertex` / `sPlaq` — the L¹ coordinate-sum potential on `Z4Vertex` / `Z4Plaq`
    (the base-vertex coordinate sum `a + b + c + d`).
  * `sVertex_addE` — a single `addE` step raises the potential by EXACTLY `1`
    (no Nat truncation: `addE` only increments).
  * `edge_base_sum` — THE load-bearing structural fact: every one of the 4
    boundary edges of a plaquette `p` is based at `p.1` (potential `= sPlaq p`) or
    at `addE p.1 _` (potential `= sPlaq p + 1`) — NEVER at `subE p.1 _`.  So the
    base of a boundary edge sits in the width-1 window `[sPlaq p, sPlaq p + 1]`.
  * `z4dist` — the Mathlib-free `Nat.dist` of the two potentials,
    `(sPlaq p - sPlaq q) + (sPlaq q - sPlaq p)`.
  * `z4Sep : SepLattice` over `z4Lattice` with `dist := z4dist`, discharging the
    three `SepLattice` axioms (`dist_self`, `dist_adj_le`, `dist_triangle`) — the
    adjacency-step bound `dist_adj_le ≤ 1` follows because a shared edge places its
    base in BOTH width-1 windows, so the two potentials differ by `≤ 1`.
  * `SepLatticeZ4_witness : SepLatticeZ4` — the subtype proof is `rfl`
    (`z4Sep.toLattice` and `z4Chain.toLattice` are both `z4Lattice`).

This is EXACTLY (and only) what the sole downstream consumer
`PinnedCluster.connected_spanning_size_ge` consumes: it routes only through
`dist_le_pathLen`, which invokes only `dist_self`, `dist_adj_le`, `dist_triangle`.
A full degree-24 BFS fixpoint is NOT required for that lower bound.

# Honest scope (what this is NOT)

This is the L¹ coordinate-SUM projection, hence a genuine but **non-tight**
separation: two plaquettes displaced along a constant-sum direction (e.g. `+e_x`,
`−e_y`) get `z4dist = 0`.  It fully and honestly inhabits `SepLattice`
(genuinely unbounded, unlike `PinnedCluster.toySep`'s `dist ≡ 0`) and delivers a
SOUND lower bound on the true degree-24 BFS plaquette distance — precisely what
`connected_spanning_size_ge` needs — but it is *not equal to* that BFS distance.
The strictly-stronger drop-in (only if the downstream Ursell decay later needs
directional, non-collapsing separation) is the per-coordinate L∞ metric
`maxᵢ |vᵢ(p) − vᵢ(q)|`, whose triangle inequality is a 4-way `max`/`omega` case
split rather than this single scalar `omega`.

# Constructive contract (`lean/AGENTS.md`)

Mathlib-free; only `Nat` / `List` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `sorry` / `admit` / new `axiom`.  All witnesses are
`Type`-level data.  Permitted axioms only `propext` / `Quot.sound`.
-/

import YMGap.Continuum.Ursell4DProgress

namespace YMGap.Continuum.SepLatticeZ4Close

open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Ursell4DProgress
open Dir4

/-! ## 1. The L¹ coordinate-sum potential -/

/-- The L¹ coordinate sum of a `Z4Vertex`. -/
def sVertex (v : Z4Vertex) : Nat := v.1 + v.2.1 + v.2.2.1 + v.2.2.2

/-- The potential of a plaquette = the potential of its base vertex. -/
def sPlaq (p : Z4Plaq) : Nat := sVertex p.1

/-- A single `addE` step raises the potential by exactly `1` (no truncation,
because `addE` only increments a coordinate). -/
theorem sVertex_addE (v : Z4Vertex) (m : Dir4) :
    sVertex (addE v m) = sVertex v + 1 := by
  obtain ⟨a, b, c, d⟩ := v
  cases m <;> simp [sVertex, addE] <;> omega

/-! ## 2. The load-bearing structural fact: boundary edges sit in a width-1 window -/

/-- **`edge_base_sum` (PROVED — the load-bearing fact).**  Every boundary edge of
`p` is based at `p.1` (potential `= sPlaq p`) or at `addE p.1 _`
(potential `= sPlaq p + 1`); never at a decremented vertex.  Hence the base of a
boundary edge sits in the width-1 window `[sPlaq p, sPlaq p + 1]`. -/
theorem edge_base_sum {p : Z4Plaq} {ℓ : Z4Link} (h : ℓ ∈ edgesOf p) :
    sVertex ℓ.1 = sPlaq p ∨ sVertex ℓ.1 = sPlaq p + 1 := by
  simp only [edgesOf, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr (sVertex_addE _ _)
  · exact Or.inr (sVertex_addE _ _)

/-! ## 3. The `Nat.dist` of the potentials (Mathlib-free) -/

/-- The `Nat`-distance between two plaquette potentials, written out so `omega`
sees it transparently. -/
def z4dist (p q : Z4Plaq) : Nat := (sPlaq p - sPlaq q) + (sPlaq q - sPlaq p)

/-! ## 4. The genuine `SepLattice` over `z4Lattice` -/

/-- **`z4Sep` (PROVED).**  A genuine `SepLattice` over the CLOSED degree-24 Z⁴
plaquette lattice, with `dist := z4dist`.  All three metric axioms discharged;
`dist_adj_le ≤ 1` is the interesting one, and follows from `edge_base_sum`: a
shared boundary edge places its base in BOTH width-1 windows, so the two
potentials differ by at most `1`. -/
def z4Sep : SepLattice where
  toLattice := z4Lattice
  dist := z4dist
  dist_self := by intro p; simp only [z4dist]; omega
  dist_adj_le := by
    intro p q adj
    -- The shared edge lies on the boundary of both `p` and `q`.
    have hp : adj.link ∈ edgesOf p := of_decide_eq_true adj.on_p
    have hq : adj.link ∈ edgesOf q := of_decide_eq_true adj.on_q
    -- Its base potential is within `1` of `sPlaq p` AND of `sPlaq q`.
    have Hp := edge_base_sum hp
    have Hq := edge_base_sum hq
    simp only [z4dist]
    omega
  dist_triangle := by intro p q r; simp only [z4dist]; omega

/-! ## 5. Inhabiting the named residual subtype -/

/-- **`SepLatticeZ4_witness` (PROVED — closes the named `(D2)` residual).**  The
subtype proof is `rfl` because `z4Sep.toLattice` and `z4Chain.toLattice` are both
definitionally `z4Lattice`. -/
def SepLatticeZ4_witness : SepLatticeZ4 := ⟨z4Sep, rfl⟩

/-- The potential is genuinely unbounded on this lattice (unlike the collapsed
`toySep`): stepping a base coordinate strictly increases `sPlaq`, so `z4Sep` is
NOT a faked zero-distance metric. -/
theorem sPlaq_addE (v : Z4Vertex) (P : Z4Plane) (m : Dir4) :
    sPlaq (addE v m, P) = sPlaq (v, P) + 1 := by
  simp only [sPlaq]
  exact sVertex_addE v m

end YMGap.Continuum.SepLatticeZ4Close
