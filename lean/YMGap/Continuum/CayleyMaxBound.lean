/-
# Leg (C) — Cayley's spanning-tree count bound, honestly reduced.

`Continuum/TreeGraphBoundProgress.lean` carries the tree-graph atom as a chain
`(P)·(C)·(A)`, where leg (C) is the `cayleyMax` field of `TreeGraphReduction`:

    cayleyMax : ∀ Y, treeCount Y ≤ (Polymer.size Y) ^ (Polymer.size Y - 2)

with `treeCount` abstract in that structure but PINNED (via `UrsellPin.countPin`)
to the concrete spanning-tree count `PenroseDomInduction.treeCount` — the number
of connected spanning edge-subsets with exactly `n-1` edges, over the Mathlib-free
`sublists` power-set enumeration.

## THE KEY HONEST FINDING: the unconditional bound is FALSE

The literal statement `treeCount n edges ≤ n ^ (n - 2)` for an *arbitrary* edge
list is **false**.  The concrete `treeCount` counts edge-SUBSETS of the given
list, so a MULTIGRAPH over-counts.  Concretely (verified by `#eval` on the real
definitions):

    treeCount 2 [(0,1),(0,1)] = 2   >   1 = 2 ^ (2 - 2).

Two parallel edges on `{0,1}` each give a distinct "spanning tree" edge-subset,
but `n^{n-2} = 1`.  Hence Cayley's bound requires the graph to be **simple**
(no repeated edge, no self-loop, endpoints in range).  For a triangle
`treeCount 3 [(0,1),(1,2),(0,2)] = 3 = 3^{3-2}` — the simple case is tight, so
the bound with a simplicity hypothesis is non-vacuous and sharp.

## THE SECOND HONEST FINDING: the recommended deletion–contraction route CANNOT close

The deletion–contraction recurrence `τ(G) = τ(G−e) + τ(G/e)` (the `DCHyp`
`treeCount`-half already residual in `PenroseDomInduction`) does **not** bound
`treeCount` by `n^{n-2}`.  The multigraph above satisfies the recurrence exactly
(`treeCount 2 [(0,1),(0,1)] = treeCount 2 [(0,1)] + treeCount 1 [(0,0)] = 1 + 1`)
while violating the bound.  A fuel-induction on `edges.length` keeps the SAME
target `n^{n-2}` on the delete branch and adds a positive contract term at every
step, so it accumulates past `n^{n-2}`.  The genuine Cayley proof is NOT a raw
deletion–contraction recursion: it needs the Prüfer injection into
`Fin (n-2) → Fin n` (which is where the simplicity/`Nodup` hypothesis becomes
load-bearing), or Kirchhoff's matrix-tree theorem.  The `DCHyp`/R2 route sketched
for this milestone is therefore mathematically insufficient; only the Prüfer
(or Kirchhoff) route works, and it is heavy Mathlib-free.

## What this module delivers (all GREEN, axiom-clean, unless marked NAMED-open)

  * `SimpleEdges n edges` — the faithful simple-graph predicate (canonical
    orientation `e.1 < e.2 < n` per edge + `Nodup`), the honest hypothesis under
    which Cayley's bound is TRUE.
  * `CayleyCountBound` (NAMED-open, leg (C) proper) — the genuine Cayley bound
    `SimpleEdges n edges → treeCount n edges ≤ n^{n-2}`.  This is a TRUE theorem,
    provable in principle by the Prüfer injection (heavy Mathlib-free), but not
    yet in the repo.  Left UNINHABITED — the single honest residual for leg (C).
  * `CayleyPin` — a reduction datum pinning the abstract `treeCount` to the
    concrete count on the (simple, `n`-vertex) connectivity graph `adjGraph Y`
    of each polymer, carrying `adjN_eq : adjN Y = size Y`, `adjSimple`, and the
    `countPin` (the same pin `UrsellPin.countPin` supplies for leg (P)).
  * `CayleyPin.cayleyMax_field` — **PROVED**: from `CayleyCountBound` and a
    `CayleyPin`, the exact `cayleyMax` field statement
    `∀ Y, treeCountF Y ≤ (Polymer.size Y) ^ (Polymer.size Y - 2)`.  This is the
    reduction deliverable: leg (C) is now a THEOREM of one honest named residual
    plus the pin that the connectivity graph is simple with `n = |Y|` vertices.

## Honest geography

This does NOT close leg (C).  It is a genuine REDUCTION: `cayleyMax` is reduced
to `CayleyCountBound` (the real Cayley theorem, Prüfer-provable) under a simple,
`n`-vertex connectivity-graph pin.  The postulated deletion–contraction/R2 route
is shown insufficient; the simplicity hypothesis (absent from the naive target
statement) is identified as load-bearing.  `CayleyCountBound` and `CayleyPin` are
LEFT UNINHABITED for a physical lattice; nothing is faked.

Fixed spacing; not the spacing-uniform continuum modulus; Clay YM mass gap
remains OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1/6/8)

Mathlib-free; only `Nat` / `List` core (+ the pinned concrete `treeCount`).  No
`Classical.*`, no `Real`, no `native_decide`, no `sorry` / new `axiom`.  All
witnesses are `Type`-level data.  Every load-bearing declaration is gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.PenroseDomInduction

namespace YMGap.Continuum.CayleyMaxBound

open YMGap.Continuum.PolymerModel
open YMGap.Continuum.PenroseDomInduction

/-! ## 1. The faithful simple-graph predicate

Cayley's bound counts spanning trees of a *simple* graph on `{0,…,n-1}`.  The
concrete `treeCount` counts edge-SUBSETS, so it agrees with the classical
spanning-tree count only when the edge list is a simple graph: each edge is
canonically oriented `e.1 < e.2` (ruling out self-loops and giving a unique
representative per unordered pair), its larger endpoint is `< n` (so both are in
range), and the list has no repeats. -/

/-- The simple-graph predicate on an edge list over `{0,…,n-1}`:
canonical orientation `e.1 < e.2 < n` per edge, and no repeated edge. -/
def SimpleEdges (n : Nat) (edges : List Edge) : Prop :=
  edges.Nodup ∧ ∀ e ∈ edges, e.1 < e.2 ∧ e.2 < n

/-! ## 2. Leg (C) proper — the genuine Cayley count bound (NAMED residual)

The one honest residual: the Cayley bound for the concrete `treeCount`, under the
simplicity hypothesis that makes it TRUE.  Provable in principle by the Prüfer
encoding `treeSubset ↪ (Fin (n-2) → Fin n)` (repeatedly strip the minimum-label
leaf, record its neighbour; the decoder inverts it, giving injectivity; the
codomain has `n^{n-2}` elements).  That injection is heavy Mathlib-free (finite
function-space cardinality, `Nodup`-preservation under injective map), so it is
LEFT UNINHABITED here.  The multigraph counterexample in the module header shows
the `SimpleEdges` hypothesis is genuinely load-bearing — without it the statement
is false — so this residual is non-vacuous and sharp. -/
def CayleyCountBound : Prop :=
  ∀ (n : Nat) (edges : List Edge),
    SimpleEdges n edges → treeCount n edges ≤ n ^ (n - 2)

/-! ## 3. The pin and the reduction of `cayleyMax`

`CayleyPin` pins the abstract `TreeGraphReduction.treeCount` field to the concrete
`PenroseDomInduction.treeCount` of the connectivity graph `adjGraph Y = (adjN Y,
adjE Y)`, exactly as `UrsellPin.countPin` does for leg (P), and additionally
records the two facts leg (C) needs: the connectivity graph is SIMPLE, and it has
`n = |Y| = size Y` vertices. -/

variable {L : Lattice}

/-- **`CayleyPin` — the reduction datum for leg (C) (NAMED, uninhabited).**
Pins the abstract tree count to the concrete spanning-tree count of the
connectivity graph of each polymer, with the two structural facts Cayley needs:

* `adjN_eq`   — the connectivity graph has `n = |Y| = size Y` vertices;
* `adjSimple` — the connectivity graph is a SIMPLE graph (the hypothesis under
  which the Cayley bound is true — see the multigraph counterexample);
* `countPin`  — `treeCountF Y = treeCount (adjGraph Y)` (the same pin
  `UrsellPin.countPin` supplies).

LEFT UNINHABITED for a physical lattice; NOT faked. -/
structure CayleyPin (L : Lattice) where
  /-- Vertex count of the connectivity graph of `Y`. -/
  adjN : Polymer L → Nat
  /-- Edge list of the connectivity graph of `Y`. -/
  adjE : Polymer L → List Edge
  /-- The pinned spanning-tree count (matches the abstract `treeCount` field). -/
  treeCountF : Polymer L → Nat
  /-- The connectivity graph has `n = |Y| = size Y` vertices. -/
  adjN_eq : ∀ Y, adjN Y = Polymer.size Y
  /-- The connectivity graph of a polymer support is a SIMPLE graph. -/
  adjSimple : ∀ Y, SimpleEdges (adjN Y) (adjE Y)
  /-- `treeCount Y = τ(adjGraph Y)` — the tree-count pin. -/
  countPin : ∀ Y, treeCountF Y = treeCount (adjN Y) (adjE Y)

/-- **`cayleyMax_field` — leg (C), reduced (PROVED from the named residual + the
pin).**  From the genuine Cayley bound `CayleyCountBound` and a `CayleyPin`, the
pinned tree count of every polymer satisfies

    treeCountF Y  ≤  (Polymer.size Y) ^ (Polymer.size Y - 2),

which is exactly the `cayleyMax` field of `TreeGraphReduction`.  Proof: rewrite
by `countPin`, apply `CayleyCountBound` to the (simple, `n`-vertex) connectivity
graph, and transport the vertex count with `adjN_eq`. -/
theorem CayleyPin.cayleyMax_field (P : CayleyPin L) (hCay : CayleyCountBound)
    (Y : Polymer L) :
    P.treeCountF Y ≤ (Polymer.size Y) ^ (Polymer.size Y - 2) := by
  rw [P.countPin Y]
  have hc : treeCount (P.adjN Y) (P.adjE Y) ≤ (P.adjN Y) ^ (P.adjN Y - 2) :=
    hCay (P.adjN Y) (P.adjE Y) (P.adjSimple Y)
  rw [P.adjN_eq Y] at hc ⊢
  exact hc

end YMGap.Continuum.CayleyMaxBound

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CayleyMaxBound.CayleyPin.cayleyMax_field
