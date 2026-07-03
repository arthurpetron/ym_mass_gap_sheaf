/-
A GENUINE four-dimensional plaquette-incidence `BddLattice` instance — the
d = 4 analog of the integer plaquette chain `zChain`
(`Continuum/BddLatticeAnimal.lean`), inhabiting the lattice-animal
`ClusterCountBound` for the physical Z⁴ hypercubic lattice.

# Why this module exists (the residual it closes)

`Continuum/BddLatticeAnimal.lean` proves the KP criterion UNCONDITIONALLY for
ANY `BddLattice` at strong coupling (`kpCriterion_unconditional`): the animal
count `animalCount n ≤ ((D+1)²)^n` is generic, `K = (D+1)²` is a crude
Euler-tour overcount, and the spanning-tree anchoring
(`AdjSpanningBuild.clusterCountBound_animal`) is discharged
UNCONDITIONALLY for every `BddLattice`.  The ONLY concrete inhabitant there is
`zChain`, a 1D plaquette chain (`D = 3`).  The connective-constant literature
(μ₄, Klarner, Madras–Slade) is a **red herring** for this interface: `count_le`
does not see any growth constant.

The entire d = 4 residual is therefore a single genuine `BddLattice` inhabitant
for the Z⁴ plaquette graph, beside `zChain` — with real incidence and two
distinct lattice neighbours per shared edge (NOT a degenerate self-loop like
`toyLattice`).  This module builds it.

# What is delivered (all PROVED, axiom-clean)

  * `Dir4` / `Z4Plane` — the 4 axis directions and the 6 coordinate planes of
    ℝ⁴, with `dirsOf`/`planeOf` inverses (`planeOf_dirsOf`).
  * `Z4Vertex := Nat⁴` (corner-anchored Z≥0⁴), `addE`/`subE` coordinate
    increment/decrement with `subE_addE : subE (addE v m) m = v` (EXACT — no
    truncation, because we decrement exactly what we incremented).
  * `z4Boundary` — the 4 GENUINE boundary edges of a plaquette
    `(v, plane)`: `(v,a), (v,b), (v+e_b, a), (v+e_a, b)`.
  * `z4Nbrs` — the 24 = 4 edges × 6 plaquettes/edge candidate neighbours
    (forward + backward per shared edge, per other direction).
  * `edge_complete` — the crux: every plaquette carrying a given edge is
    enumerated by `edgePlaqs` of that edge (per-edge enumeration completeness).
    The backward-plaquette positions use `subE (addE …)` which cancels EXACTLY,
    so the Nat truncated-subtraction boundary (`x = 0`) is NEVER hit — the
    completeness holds with no edge-of-lattice special-casing.
  * `z4_sound` — the ONE genuine proof obligation (adjacency soundness),
    PROVED: link-adjacent plaquettes are enumerated neighbours.
  * `z4Chain : BddLattice` — the genuine degree-24 Z⁴ plaquette graph, and
  * `z4ClusterCountBound` / `z4ClusterCountBound_animal` — the lattice-animal
    `ClusterCountBound` for d = 4 with free constant `K = (24+1)² = 625`, plus
    the UNCONDITIONAL over-count guarantee inherited from `AdjSpanningBuild`.

# Honest scope (what this is NOT)

Inhabiting `ClusterCountBound` for d = 4 supplies the lattice-animal counting
brick feeding `kp_criterion_of_count` under the explicit strong-coupling
threshold `kpRatio ≤ 1/2`.  It is NOT the full cluster-sum convergence, NOT
volume-uniformity, and NOT the continuum mass gap — those remain the
continuum frontier.

# Constructive contract (`lean/AGENTS.md`)

Mathlib-free; only `Nat` / `List` core and the existing `BddLatticeAnimal`
machinery.  No `Classical.*`, no `Real`, no `native_decide`, no `sorry` /
`admit` / new `axiom`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.BddLatticeAnimal
import YMGap.Continuum.AdjSpanningBuild

namespace YMGap.Continuum.ClusterCount4DProgress

open YMGap.Continuum.PolymerModel
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.KPCriterion

/-! ## 1. Directions, planes, vertices -/

/-- The four axis directions of ℤ⁴. -/
inductive Dir4 | x0 | x1 | x2 | x3
  deriving DecidableEq

/-- The six coordinate 2-planes of ℤ⁴ (canonically `i < j`). -/
inductive Z4Plane | p01 | p02 | p03 | p12 | p13 | p23
  deriving DecidableEq

open Dir4 Z4Plane

/-- The ordered direction pair `(a, b)`, `a < b`, spanning a plane. -/
def dirsOf : Z4Plane → Dir4 × Dir4
  | p01 => (x0, x1) | p02 => (x0, x2) | p03 => (x0, x3)
  | p12 => (x1, x2) | p13 => (x1, x3) | p23 => (x2, x3)

/-- The plane spanned by two distinct directions (symmetric; the diagonal
`d = d` value is unused). -/
def planeOf : Dir4 → Dir4 → Z4Plane
  | x0, x1 => p01 | x1, x0 => p01
  | x0, x2 => p02 | x2, x0 => p02
  | x0, x3 => p03 | x3, x0 => p03
  | x1, x2 => p12 | x2, x1 => p12
  | x1, x3 => p13 | x3, x1 => p13
  | x2, x3 => p23 | x3, x2 => p23
  | _,  _  => p01

/-- `planeOf` inverts `dirsOf` (forward order). -/
theorem planeOf_dirsOf (P : Z4Plane) :
    planeOf (dirsOf P).1 (dirsOf P).2 = P := by cases P <;> rfl

/-- `planeOf` inverts `dirsOf` (swapped order). -/
theorem planeOf_dirsOf_symm (P : Z4Plane) :
    planeOf (dirsOf P).2 (dirsOf P).1 = P := by cases P <;> rfl

/-- A plane's two directions are distinct. -/
theorem dirsOf_ne (P : Z4Plane) : (dirsOf P).1 ≠ (dirsOf P).2 := by
  cases P <;> decide

/-- A corner-anchored vertex of `ℤ≥0⁴`. -/
abbrev Z4Vertex : Type := Nat × Nat × Nat × Nat

/-- Increment the `m`-th coordinate. -/
def addE : Z4Vertex → Dir4 → Z4Vertex
  | (a, b, c, d), x0 => (a + 1, b, c, d)
  | (a, b, c, d), x1 => (a, b + 1, c, d)
  | (a, b, c, d), x2 => (a, b, c + 1, d)
  | (a, b, c, d), x3 => (a, b, c, d + 1)

/-- Decrement (truncated) the `m`-th coordinate. -/
def subE : Z4Vertex → Dir4 → Z4Vertex
  | (a, b, c, d), x0 => (a - 1, b, c, d)
  | (a, b, c, d), x1 => (a, b - 1, c, d)
  | (a, b, c, d), x2 => (a, b, c - 1, d)
  | (a, b, c, d), x3 => (a, b, c, d - 1)

/-- **Exact cancellation:** decrementing the coordinate we just incremented
returns the original vertex.  Because the `+1` precedes the `-1`, the Nat
truncated subtraction never bites, so this holds with no `x = 0` case. -/
theorem subE_addE (v : Z4Vertex) (m : Dir4) : subE (addE v m) m = v := by
  obtain ⟨a, b, c, d⟩ := v
  cases m <;> simp [addE, subE]

/-! ## 2. Links, plaquettes, and the boundary incidence -/

/-- A link: a base vertex plus an edge direction. -/
abbrev Z4Link : Type := Z4Vertex × Dir4

/-- A plaquette: a base vertex plus a plane (with `i < j` convention baked into
`Z4Plane`). -/
abbrev Z4Plaq : Type := Z4Vertex × Z4Plane

/-- **The 4 genuine boundary edges** of a plaquette `(v, P)` with `P` spanning
directions `(a, b)`: the two edges at `v` (`(v,a)`, `(v,b)`) and the two far
edges (`(v+e_b, a)`, `(v+e_a, b)`). -/
def edgesOf (p : Z4Plaq) : List Z4Link :=
  [ (p.1, (dirsOf p.2).1),
    (p.1, (dirsOf p.2).2),
    (addE p.1 (dirsOf p.2).2, (dirsOf p.2).1),
    (addE p.1 (dirsOf p.2).1, (dirsOf p.2).2) ]

/-- **The boundary incidence** as a `Bool`: link `ℓ` is on the boundary of
plaquette `p` iff it is one of the 4 genuine boundary edges. -/
def z4Boundary (p : Z4Plaq) (ℓ : Z4Link) : Bool := decide (ℓ ∈ edgesOf p)

/-! ## 3. The neighbour enumeration and its per-edge completeness

For a shared edge `(u, d)`, the plaquettes carrying it are: for each of the 3
other directions `m ≠ d`, the plane `planeOf d m`, with two plaquettes —
`(u, ·)` (forward) and `(subE u m, ·)` (backward, i.e. based one step back in
direction `m`).  `edgePlaqs u d` lists these 6.  The full neighbour list of a
plaquette is `edgePlaqs` over its 4 edges (24 candidates). -/

/-- The (≤ 6) plaquettes carrying edge `(u, d)`: forward and backward in each of
the 3 planes containing `d`.  A literal 6-element list per direction. -/
def edgePlaqs (u : Z4Vertex) (d : Dir4) : List Z4Plaq :=
  match d with
  | x0 => [(u, planeOf x0 x1), (subE u x1, planeOf x0 x1),
           (u, planeOf x0 x2), (subE u x2, planeOf x0 x2),
           (u, planeOf x0 x3), (subE u x3, planeOf x0 x3)]
  | x1 => [(u, planeOf x1 x0), (subE u x0, planeOf x1 x0),
           (u, planeOf x1 x2), (subE u x2, planeOf x1 x2),
           (u, planeOf x1 x3), (subE u x3, planeOf x1 x3)]
  | x2 => [(u, planeOf x2 x0), (subE u x0, planeOf x2 x0),
           (u, planeOf x2 x1), (subE u x1, planeOf x2 x1),
           (u, planeOf x2 x3), (subE u x3, planeOf x2 x3)]
  | x3 => [(u, planeOf x3 x0), (subE u x0, planeOf x3 x0),
           (u, planeOf x3 x1), (subE u x1, planeOf x3 x1),
           (u, planeOf x3 x2), (subE u x2, planeOf x3 x2)]

/-- Each edge is carried by exactly 6 enumerated plaquettes. -/
theorem edgePlaqs_length (u : Z4Vertex) (d : Dir4) :
    (edgePlaqs u d).length = 6 := by cases d <;> rfl

/-- The forward plaquette `(u, planeOf d m)` (for `m ≠ d`) is enumerated. -/
theorem mem_forward (u : Z4Vertex) (d m : Dir4) (h : m ≠ d) :
    (u, planeOf d m) ∈ edgePlaqs u d := by
  cases d <;> cases m <;>
    first
    | exact absurd rfl h
    | simp [edgePlaqs, planeOf]

/-- The backward plaquette `(subE u m, planeOf d m)` (for `m ≠ d`) is
enumerated. -/
theorem mem_backward (u : Z4Vertex) (d m : Dir4) (h : m ≠ d) :
    (subE u m, planeOf d m) ∈ edgePlaqs u d := by
  cases d <;> cases m <;>
    first
    | exact absurd rfl h
    | simp [edgePlaqs, planeOf]

/-- **Per-edge completeness (the crux).**  Every plaquette `q` carrying edge
`(u, d)` is one of the 6 enumerated `edgePlaqs u d`.  Proven by cases on which
of `q`'s 4 boundary edges equals `(u, d)`; the two "far edge" cases use
`subE_addE` to cancel the offset EXACTLY (no `x = 0` boundary case). -/
theorem edge_complete (q : Z4Plaq) (u : Z4Vertex) (d : Dir4)
    (h : (u, d) ∈ edgesOf q) : q ∈ edgePlaqs u d := by
  obtain ⟨w, P⟩ := q
  simp only [edgesOf, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at h
  have hne : (dirsOf P).2 ≠ (dirsOf P).1 := (dirsOf_ne P).symm
  rcases h with ⟨hu, hd⟩ | ⟨hu, hd⟩ | ⟨hu, hd⟩ | ⟨hu, hd⟩
  · -- (u,d) = (w, (dirsOf P).1): forward, plane P, other dir (dirsOf P).2
    rw [hu, hd]
    have hm := mem_forward w (dirsOf P).1 (dirsOf P).2 hne
    rw [planeOf_dirsOf] at hm
    exact hm
  · -- (u,d) = (w, (dirsOf P).2): forward, plane P, other dir (dirsOf P).1
    rw [hu, hd]
    have hm := mem_forward w (dirsOf P).2 (dirsOf P).1 (dirsOf_ne P)
    rw [planeOf_dirsOf_symm] at hm
    exact hm
  · -- (u,d) = (addE w (dirsOf P).2, (dirsOf P).1): backward, offset e_b
    rw [hu, hd]
    have hm := mem_backward (addE w (dirsOf P).2) (dirsOf P).1 (dirsOf P).2 hne
    rw [subE_addE, planeOf_dirsOf] at hm
    exact hm
  · -- (u,d) = (addE w (dirsOf P).1, (dirsOf P).2): backward, offset e_a
    rw [hu, hd]
    have hm := mem_backward (addE w (dirsOf P).1) (dirsOf P).2 (dirsOf P).1
      (dirsOf_ne P)
    rw [subE_addE, planeOf_dirsOf_symm] at hm
    exact hm

/-- **The neighbour list** of a plaquette `(v, P)`: `edgePlaqs` over each of the
4 boundary edges, concatenated — 24 candidate neighbours. -/
def z4Nbrs (p : Z4Plaq) : List Z4Plaq :=
  edgePlaqs p.1 (dirsOf p.2).1
    ++ edgePlaqs p.1 (dirsOf p.2).2
    ++ edgePlaqs (addE p.1 (dirsOf p.2).2) (dirsOf p.2).1
    ++ edgePlaqs (addE p.1 (dirsOf p.2).1) (dirsOf p.2).2

/-- The neighbour list has exactly 24 = 4 × 6 entries. -/
theorem z4Nbrs_length (p : Z4Plaq) : (z4Nbrs p).length = 24 := by
  unfold z4Nbrs
  simp only [List.length_append, edgePlaqs_length]

/-! ## 4. Adjacency soundness — the ONE genuine obligation (PROVED) -/

/-- **`z4_sound` (PROVED).**  If link `ℓ` is on the boundary of both `p` and
`q`, then `q` is an enumerated neighbour of `p`.  This is the d = 4 analog of
`zChain_sound`, discharged via per-edge completeness (`edge_complete`): the
shared edge `ℓ` is one of `p`'s 4 edges, whose `edgePlaqs` block sits inside
`z4Nbrs p` and (by `edge_complete`) already contains `q`. -/
theorem z4_sound (p q : Z4Plaq) (ℓ : Z4Link)
    (hp : z4Boundary p ℓ = true) (hq : z4Boundary q ℓ = true) :
    q ∈ z4Nbrs p := by
  obtain ⟨v, P⟩ := p
  obtain ⟨u, d⟩ := ℓ
  have hpe : (u, d) ∈ edgesOf (v, P) := of_decide_eq_true hp
  have hqe : (u, d) ∈ edgesOf q := of_decide_eq_true hq
  have hq' : q ∈ edgePlaqs u d := edge_complete q u d hqe
  -- Determine which of p's 4 edges the shared edge is; place q's block.
  simp only [edgesOf, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at hpe
  unfold z4Nbrs
  rcases hpe with ⟨hu, hd⟩ | ⟨hu, hd⟩ | ⟨hu, hd⟩ | ⟨hu, hd⟩
  · rw [hu, hd] at hq'
    exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ hq'))
  · rw [hu, hd] at hq'
    exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ hq'))
  · rw [hu, hd] at hq'
    exact List.mem_append_left _ (List.mem_append_right _ hq')
  · rw [hu, hd] at hq'
    exact List.mem_append_right _ hq'

/-! ## 5. The genuine Z⁴ `BddLattice` and its cluster-count bound -/

/-- The Z⁴ plaquette-incidence lattice (`Link = Z4Link`, `Plaquette = Z4Plaq`,
`boundary = z4Boundary`). -/
def z4Lattice : Lattice where
  Link := Z4Link
  Plaquette := Z4Plaq
  boundary := z4Boundary

/-- **The genuine degree-24 Z⁴ plaquette `BddLattice`.**  Real incidence, two
distinct lattice neighbours per shared edge — the honest 4D analog of
`zChain`, NOT a degenerate self-loop. -/
def z4Chain : BddLattice where
  toLattice := z4Lattice
  decEq := inferInstanceAs (DecidableEq Z4Plaq)
  nbrs := z4Nbrs
  D := 24
  deg_le := fun p => Nat.le_of_eq (z4Nbrs_length p)
  adjacent_mem_nbrs := fun p q adj => z4_sound p q adj.link adj.on_p adj.on_q

/-- **The lattice-animal `ClusterCountBound` for d = 4** (`K = (24+1)² = 625`),
`count_le` PROVED via the generic `clusterCountBound_of_bdd`. -/
def z4ClusterCountBound (p : z4Chain.toLattice.Plaquette) :
    ClusterCountBound z4Chain.toLattice p :=
  clusterCountBound_of_bdd z4Chain p

/-- **The d = 4 cluster-count bound WITH the unconditional over-count
guarantee**, inherited from `AdjSpanningBuild.clusterCountBound_animal` — every
connected size-`n` lattice animal through `p` is represented (up to support) in
the decoded enumeration, with NO named-open obligation. -/
def z4ClusterCountBound_animal (p : z4Chain.toLattice.Plaquette) :
    (cc : ClusterCountBound z4Chain.toLattice p) ×'
      (∀ n X, YMGap.Continuum.BddLatticeAnimal.IsClusterThroughIn z4Chain p n X →
        ∃ Y, Y ∈ YMGap.Continuum.BddLatticeAnimal.enumPolys z4Chain p n ∧
          YMGap.Continuum.BddLatticeAnimal.sameSupport X Y) :=
  YMGap.Continuum.AdjSpanningBuild.clusterCountBound_animal z4Chain p

/-! ## 6. Non-degeneracy witnesses (this is a GENUINE 4D graph) -/

/-- A sample base vertex. -/
def v0 : Z4Vertex := (0, 0, 0, 0)

/-- Two DISTINCT plaquettes `(v0, p01)` and `(v0, p02)` share the genuine edge
`(v0, x0)`: real incidence, distinct planes, distinct plaquettes.  Confirms
`z4Chain` is not a self-loop degeneracy. -/
theorem z4_shares_edge :
    z4Boundary (v0, p01) (v0, x0) = true
      ∧ z4Boundary (v0, p02) (v0, x0) = true
      ∧ (v0, p02) ≠ (v0, p01) := by decide

/-- The shared-edge neighbour `(v0, p02)` is genuinely enumerated in
`z4Nbrs (v0, p01)` — a real lattice neighbour, not the plaquette itself. -/
theorem z4_neighbour_witness : (v0, p02) ∈ z4Nbrs (v0, p01) := by decide

/-! ## 7. Documentation: PROVED, and honest scope (AGENTS.md Rule 6)

PROVED in this module, axiom-clean (`[propext]` / `[propext, Quot.sound]`):

  * `Dir4` / `Z4Plane` + `dirsOf` / `planeOf` inverses (`planeOf_dirsOf`,
    `planeOf_dirsOf_symm`, `dirsOf_ne`);
  * `addE` / `subE` with `subE_addE` (EXACT cancellation, no `x = 0` case);
  * `z4Boundary` — the 4 genuine boundary edges of a plaquette;
  * `edgePlaqs` (+ `edgePlaqs_length`, `mem_forward`, `mem_backward`) and the
    crux `edge_complete` — per-edge enumeration completeness;
  * `z4Nbrs` (+ `z4Nbrs_length = 24`);
  * `z4_sound` — the ONE genuine adjacency-soundness obligation, PROVED;
  * `z4Chain : BddLattice` — the genuine degree-24 Z⁴ plaquette graph;
  * `z4ClusterCountBound` — the d = 4 lattice-animal `ClusterCountBound`,
    `K = 625`, `count_le` proved;
  * `z4ClusterCountBound_animal` — the same, packaged with the UNCONDITIONAL
    over-count guarantee inherited from `AdjSpanningBuild`;
  * `z4_shares_edge` / `z4_neighbour_witness` — non-degeneracy (two distinct
    real neighbours sharing a genuine edge).

The connective-constant literature (μ₄, Klarner, Madras–Slade) is a red herring
here: `count_le` is generic over `BddLattice` at `K = (D+1)²`, a crude
Euler-tour overcount; a sharp μ₄ would only relax the strong-coupling threshold
and is strictly harder to prove.  This module is NOT the full cluster-sum
convergence, NOT volume-uniformity, and NOT the continuum mass gap. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms subE_addE
#print axioms planeOf_dirsOf
#print axioms edgePlaqs_length
#print axioms mem_forward
#print axioms mem_backward
#print axioms edge_complete
#print axioms z4Nbrs_length
#print axioms z4_sound
#print axioms z4Chain
#print axioms z4ClusterCountBound
#print axioms z4ClusterCountBound_animal
#print axioms z4_shares_edge
#print axioms z4_neighbour_witness

end YMGap.Continuum.ClusterCount4DProgress
