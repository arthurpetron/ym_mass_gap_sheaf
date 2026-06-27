import YMGap.Continuum.DecodeTourSound

/-!
# Building a `Faithful` spanning tree: the adjacency bridge + length derivation

This file attacks the last combinatorial brick `SpanningTreeExists`
(`DecodeTourSound.SpanningTreeExists`) from below.  It does NOT fake the deep
connectivity content; it strictly REDUCES `SpanningTreeExists` by DISCHARGING
its `Faithful` conjunct (the `nbrs`-index resolution) via a re-indexing
construction, leaving the remaining four conjuncts as a pure *graph*
spanning-tree residual:

  * `RTree.root t = p`              — carried directly by the residual.
  * `(RTree.nodes t).length = n`    — carried directly by the residual.
  * `sameSupport X (RTree.nodes t)` — carried directly by the residual.
  * `(RTree.nodes t).Nodup`         — carried directly by the residual.
  * `Faithful t`                    — DISCHARGED here: the residual instead
                                       carries a purely *lattice-level* adjacency
                                       annotation `AdjacentEdges t` (every tree
                                       edge is a `BL.toLattice.Adjacent` pair),
                                       from which `reindex` rebuilds the tree
                                       with genuine faithful `nbrs`-indices,
                                       preserving root/nodes and producing a
                                       `Faithful` tree by construction.

The residual is therefore `AdjSpanningTree`: pure *graph* spanning-tree
existence (root `p`, node count `n`, distinct nodes, node support `= X`, and
every tree edge a genuine lattice adjacency) — with **no** mention of
`BL.nbrs`, `Fin`-indices, `Faithful`, `decode`, or `tour`.  `AdjSpanningTree`
is strictly smaller than `SpanningTreeExists`: it replaces the runtime
`nbrs`-index resolution `Faithful` (a condition on stored `Fin BL.D` indices
and their `BL.nbrs` lookups) with the single natural lattice condition "every
edge is an `Adjacent` pair", which is exactly what a DFS over
`BL.toLattice.Adjacent` produces — no index bookkeeping.  The
`nbrs`-index/faithfulness bridge (`firstIndexOfMem`, `faithIndex`, `reindex`
and its three preservation lemmas) is fully PROVED here.

## Constructive contract (`lean/AGENTS.md`)

Mathlib-free; only core `List`/`Nat`/`Fin`.  No `Classical.*`, no `sorry` /
`admit` / new `axiom`.  Witnesses are Type-level data.  The new residual
`AdjSpanningTree` is a precisely-named `Prop`, never inhabited vacuously.
-/

namespace YMGap.Continuum.SpanningTreeBuild

open YMGap.Continuum.PolymerModel
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.DecodeTourSound

/-! ## 1. The adjacency-to-faithful-index bridge

`Faithful` demands, at each edge from parent `r` to child `c`, a `Fin BL.D`
index `i` with `(BL.nbrs r)[i.val]? = some c`.  The lattice only hands us
`BL.toLattice.Adjacent r c` (a shared boundary link).  `adjacent_mem_nbrs`
turns that into `c ∈ BL.nbrs r`, and `getElem_of_mem` + the degree bound
`deg_le` turn membership into such a `Fin BL.D` index.  This is the entire
`nbrs`-index content of `Faithful`, isolated and proved. -/

/-- **The faithful index** of a lattice-adjacent child.  Given
`BL.toLattice.Adjacent r c`, there is a `Fin BL.D` index `i` whose `BL.nbrs r`
lookup is exactly `some c`.  Proved from `adjacent_mem_nbrs` (adjacency ⇒
membership), `getElem_of_mem` (membership ⇒ indexed lookup), and `deg_le`
(index `< D`). -/
theorem exists_faithIndex (BL : BddLattice) {r c : BL.toLattice.Plaquette}
    (adj : BL.toLattice.Adjacent r c) :
    ∃ i : Fin BL.D, (BL.nbrs r)[i.val]? = some c := by
  have hmem : c ∈ BL.nbrs r := BL.adjacent_mem_nbrs r c adj
  obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hmem
  -- j < (nbrs r).length ≤ D
  have hjD : j < BL.D := Nat.lt_of_lt_of_le hj (BL.deg_le r)
  refine ⟨⟨j, hjD⟩, ?_⟩
  -- (nbrs r)[j]? = some c  from  (nbrs r)[j] = c
  rw [List.getElem?_eq_some_iff]
  exact ⟨hj, hget⟩

/-- Find the first index `i < (BL.nbrs r).length` with `(BL.nbrs r)[i] = c`,
returned as data with its proof, given `c ∈ BL.nbrs r`.  Pure list recursion,
no choice. -/
def firstIndexOfMem {BL : BddLattice} (r c : BL.toLattice.Plaquette) :
    (l : List BL.toLattice.Plaquette) → c ∈ l →
      { i : Nat // i < l.length ∧ l[i]? = some c }
  | a :: rest, h =>
      if hac : c = a then
        ⟨0, by
          refine ⟨Nat.zero_lt_succ _, ?_⟩
          show (a :: rest)[0]? = some c
          simp [hac]⟩
      else
        let ⟨i, hi, hget⟩ := firstIndexOfMem r c rest (by
          rcases List.mem_cons.mp h with h0 | h1
          · exact absurd h0 hac
          · exact h1)
        ⟨i + 1, by
          refine ⟨Nat.succ_lt_succ hi, ?_⟩
          show (a :: rest)[i + 1]? = some c
          rw [List.getElem?_cons_succ]
          exact hget⟩

/-- The faithful index of an adjacent child, as DATA (no `Classical.choice`):
a `Fin BL.D` index `i` with `(BL.nbrs r)[i.val]? = some c`. -/
def faithIndex {BL : BddLattice} {r c : BL.toLattice.Plaquette}
    (adj : BL.toLattice.Adjacent r c) :
    { i : Fin BL.D // (BL.nbrs r)[i.val]? = some c } :=
  let hmem : c ∈ BL.nbrs r := BL.adjacent_mem_nbrs r c adj
  let ⟨j, hj, hget⟩ := firstIndexOfMem r c (BL.nbrs r) hmem
  ⟨⟨j, Nat.lt_of_lt_of_le hj (BL.deg_le r)⟩, hget⟩

/-! ## 2. The lattice-edge annotation of an `RTree` (Type-level data)

`Lattice.Adjacent` is a *structure* (`Type`), carrying the shared link as data,
so the edge annotation is Type-valued, not `Prop`.  `AdjacentEdges t` is the
nested record of `Adjacent` witnesses, one per tree edge.  This is the natural,
`nbrs`-index-free well-formedness a graph spanning tree of a connected animal
carries.  From it we will REBUILD faithful indices. -/

mutual
  /-- Every edge of `t` is a lattice adjacency from parent to child root;
  recursively for subtrees.  Type-valued (carries the `Adjacent` data). -/
  def AdjacentEdges {BL : BddLattice} : RTree BL → Type
    | .node r ch => AdjacentEdgesList r ch
  /-- `AdjacentEdgesList r ch`: from parent root `r`, each child `(_, t')`
  carries `BL.toLattice.Adjacent r (RTree.root t')`, recursively. -/
  def AdjacentEdgesList {BL : BddLattice} (r : BL.toLattice.Plaquette) :
      List (Fin BL.D × RTree BL) → Type
    | [] => PUnit
    | (_, t') :: rest =>
        BL.toLattice.Adjacent r (RTree.root t') ×
          AdjacentEdges t' × AdjacentEdgesList r rest
end

/-! ## 3. Re-indexing to a `Faithful` tree (same root, same nodes)

`reindex t h` rebuilds `t` with the SAME root and SAME child-subtree shapes,
but replacing each stored `Fin BL.D` edge index with a genuine faithful index
from `faithIndex` (driven by the carried `Adjacent` witness).  Because
`RTree.root` and `RTree.nodes` ignore the `Fin` indices entirely, `reindex`
preserves both — proved as `reindex_root` / `reindex_nodes`.  And the rebuilt
tree is `Faithful` by construction — proved as `reindex_faithful`. -/

mutual
  /-- Rebuild `t` with faithful indices, preserving root and node list. -/
  def reindex {BL : BddLattice} :
      (t : RTree BL) → AdjacentEdges t → RTree BL
    | .node r ch, h => RTree.node r (reindexList r ch h)
  /-- Rebuild a child list with faithful indices. -/
  def reindexList {BL : BddLattice} (r : BL.toLattice.Plaquette) :
      (ch : List (Fin BL.D × RTree BL)) → AdjacentEdgesList r ch →
        List (Fin BL.D × RTree BL)
    | [], _ => []
    | (_, t') :: rest, h =>
        ((faithIndex h.1).1, reindex t' h.2.1) :: reindexList r rest h.2.2
end

/-! ## 4. `reindex` preserves root and nodes, and yields a `Faithful` tree -/

theorem reindex_root {BL : BddLattice} (t : RTree BL) (h : AdjacentEdges t) :
    RTree.root (reindex t h) = RTree.root t := by
  cases t with
  | node r ch => rfl

mutual
  theorem reindex_nodes {BL : BddLattice} :
      ∀ (t : RTree BL) (h : AdjacentEdges t),
        RTree.nodes (reindex t h) = RTree.nodes t
    | .node r ch, h => by
        show r :: RTree.nodesList (reindexList r ch h)
          = r :: RTree.nodesList ch
        rw [reindexList_nodes r ch h]
  theorem reindexList_nodes {BL : BddLattice} (r : BL.toLattice.Plaquette) :
      ∀ (ch : List (Fin BL.D × RTree BL)) (h : AdjacentEdgesList r ch),
        RTree.nodesList (reindexList r ch h) = RTree.nodesList ch
    | [], _ => rfl
    | (_, t') :: rest, h => by
        show RTree.nodes (reindex t' h.2.1) ++ RTree.nodesList (reindexList r rest h.2.2)
          = RTree.nodes t' ++ RTree.nodesList rest
        rw [reindex_nodes t' h.2.1, reindexList_nodes r rest h.2.2]
end

mutual
  theorem reindex_faithful {BL : BddLattice} :
      ∀ (t : RTree BL) (h : AdjacentEdges t), Faithful (reindex t h)
    | .node r ch, h => by
        show FaithfulList r (reindexList r ch h)
        exact reindexList_faithful r ch h
  theorem reindexList_faithful {BL : BddLattice} (r : BL.toLattice.Plaquette) :
      ∀ (ch : List (Fin BL.D × RTree BL)) (h : AdjacentEdgesList r ch),
        FaithfulList r (reindexList r ch h)
    | [], _ => True.intro
    | (_, t') :: rest, h => by
        -- reindexList r ((_,t')::rest) h
        --   = ((faithIndex h.1).1, reindex t' h.2.1) :: reindexList r rest h.2.2
        -- FaithfulList r (that) unfolds to the triple
        show (BL.nbrs r)[((faithIndex h.1).1).val]? = some (RTree.root (reindex t' h.2.1)) ∧
            Faithful (reindex t' h.2.1) ∧ FaithfulList r (reindexList r rest h.2.2)
        refine ⟨?_, reindex_faithful t' h.2.1, reindexList_faithful r rest h.2.2⟩
        -- the stored index is faithIndex h.1, whose lookup is some (root t');
        -- and root (reindex t') = root t' by reindex_root
        rw [reindex_root t' h.2.1]
        exact (faithIndex h.1).2
end

#print axioms faithIndex
#print axioms reindex_root
#print axioms reindex_nodes
#print axioms reindex_faithful

/-! ## 5. The strictly smaller residual `AdjSpanningTree` and the reduction

The residual replaces the `Faithful` conjunct of `SpanningTreeExists` (the
`nbrs`-index resolution) by the natural lattice condition `AdjacentEdges`: every
tree edge is a `BL.toLattice.Adjacent` pair.  `reindex` + the four preservation
lemmas of §4 turn an `AdjacentEdges`-annotated tree into a `Faithful` one with
the same root/nodes, discharging `Faithful`.  The other four conjuncts (root,
length, support, Nodup) are carried directly.

`AdjacentEdges` is `Type`-valued (it carries `Adjacent` link data), so to keep
the residual a `Prop` we wrap it in `Nonempty`; the reduction eliminates that
`Nonempty` into the `Prop` goal `∃ t, …`, which is legal. -/

/-- **The strictly smaller residual: adjacency-edge spanning-tree existence.**
For each connected size-`n` polymer `X` through `p`, there is a rooted tree with
root `p`, node count `n`, node support `X` (`sameSupport`), distinct nodes, and
every edge a genuine lattice adjacency (`AdjacentEdges`, wrapped in `Nonempty`
to stay in `Prop`).  This is pure *graph* spanning-tree existence: it mentions
no `BL.nbrs`, no `Fin`-index, no `Faithful`, no `decode`/`tour`.  It is strictly
smaller than `SpanningTreeExists`, which additionally demanded the runtime
`nbrs`-index resolution `Faithful` — discharged here via `reindex`. -/
def AdjSpanningTree (BL : BddLattice) (p : BL.toLattice.Plaquette)
    (n : Nat) : Prop :=
  ∀ X : Polymer BL.toLattice, IsClusterThrough BL p n X →
    ∃ t : RTree BL,
      RTree.root t = p ∧
      (RTree.nodes t).length = n ∧
      sameSupport X (RTree.nodes t) ∧
      (RTree.nodes t).Nodup ∧
      Nonempty (AdjacentEdges t)

/-- **`SpanningTreeExists` from `AdjSpanningTree` (PROVED reduction).**  Given
the adjacency-edge spanning tree, `reindex` produces a `Faithful` tree with the
same root, node list, support and `Nodup` (preservation lemmas of §4); the
`Faithful` conjunct of `SpanningTreeExists` is thereby discharged, the rest
transported. -/
theorem spanningTreeExists_of_adj (BL : BddLattice)
    (p : BL.toLattice.Plaquette) (n : Nat)
    (h : AdjSpanningTree BL p n) :
    SpanningTreeExists BL p n := by
  intro X hX
  obtain ⟨t, hroot, hlen, hsupp, hnd, hadjne⟩ := h X hX
  -- eliminate the Type-level AdjacentEdges into the Prop goal
  refine hadjne.elim (fun hadj => ?_)
  refine ⟨reindex t hadj, ?_, ?_, ?_, ?_, ?_⟩
  · rw [reindex_root t hadj]; exact hroot
  · rw [reindex_nodes t hadj]; exact hlen
  · rw [reindex_nodes t hadj]; exact hsupp
  · exact reindex_faithful t hadj
  · rw [reindex_nodes t hadj]; exact hnd

#print axioms spanningTreeExists_of_adj

/-! ## 6. Threading the reduction to the cluster-count bound

Composing with `DecodeTourSound.decodeComplete_of_exists` /
`clusterCountBound_of_exists`, the genuine cluster-count over-count guarantee is
now conditional ONLY on `AdjSpanningTree` (pure graph spanning-tree existence
with lattice-adjacent edges). -/

/-- **`DecodeComplete` from `AdjSpanningTree` (PROVED).** -/
theorem decodeComplete_of_adj (BL : BddLattice)
    (p : BL.toLattice.Plaquette) (n : Nat)
    (h : AdjSpanningTree BL p n) :
    DecodeComplete BL p n :=
  DecodeTourSound.decodeComplete_of_exists BL p n
    (spanningTreeExists_of_adj BL p n h)

/-- **Cluster-count bound anchored on `AdjSpanningTree` ONLY (PROVED).** -/
def clusterCountBound_of_adj (BL : BddLattice)
    (p : BL.toLattice.Plaquette)
    (h : ∀ n, AdjSpanningTree BL p n) :
    (cc : KPCriterion.ClusterCountBound BL.toLattice p) ×'
      (∀ n X, IsClusterThrough BL p n X →
        ∃ Y, Y ∈ enumPolys BL p n ∧ sameSupport X Y) :=
  DecodeTourSound.clusterCountBound_of_exists BL p
    (fun n => spanningTreeExists_of_adj BL p n (h n))

#print axioms decodeComplete_of_adj
#print axioms clusterCountBound_of_adj

/-! ## 7. Non-vacuity of `AdjSpanningTree` (a concrete satisfied instance)

To rule out the "unsatisfiable named obligation" failure mode we exhibit, on
the integer chain `zChain`, a concrete cluster `X = [0, 1]` (connected, size 2,
through `0`) and a tree witnessing `AdjSpanningTree zChain 0 2` for it: the tree
`node 0 [(_, node 1 [])]` has root `0`, nodes `[0,1]` (length 2, Nodup, same
support as `[0,1]`), and its single edge `0 → 1` is a genuine `zChain` adjacency
(they share boundary link `1`).  Hence the residual is genuinely inhabitable on
a real, non-degenerate tree. -/

/-- The shared boundary link `1` makes `0` and `1` adjacent in `zChain`. -/
def zChainAdj01 : zChain.toLattice.Adjacent (0 : Nat) (1 : Nat) where
  link := (1 : Nat)
  on_p := by decide
  on_q := by decide

/-- A concrete `AdjacentEdges` witness for the size-2 chain tree. -/
def witnessAdjEdges :
    AdjacentEdges (RTree.node (0 : Nat) [(⟨0, by decide⟩, RTree.node (1 : Nat) [])] :
      RTree zChain) :=
  ⟨zChainAdj01, PUnit.unit, PUnit.unit⟩

/-- **Non-vacuity witness (PROVED).**  For `X = [0,1]` on `zChain`, the tree
`node 0 [(_, node 1 [])]` satisfies every conjunct of `AdjSpanningTree`'s body:
root `0`, length `2`, same support as `[0,1]`, `Nodup`, and lattice-adjacent
edges.  So `AdjSpanningTree` is not an empty obligation. -/
theorem witnessAdjSpanning_spec :
    let t : RTree zChain := RTree.node (0 : Nat) [(⟨0, by decide⟩, RTree.node (1 : Nat) [])]
    RTree.root t = (0 : Nat) ∧
    (RTree.nodes t).length = 2 ∧
    sameSupport ([(0 : Nat), (1 : Nat)] : Polymer zChain.toLattice) (RTree.nodes t) ∧
    (RTree.nodes t).Nodup ∧
    Nonempty (AdjacentEdges t) := by
  refine ⟨rfl, rfl, ?_, ?_, ⟨witnessAdjEdges⟩⟩
  · -- sameSupport [0,1] [0,1]
    have hnodes : RTree.nodes (RTree.node (0 : Nat)
        [(⟨0, by decide⟩, RTree.node (1 : Nat) [])] : RTree zChain) = [(0 : Nat), (1 : Nat)] := rfl
    rw [hnodes]; exact sameSupport_refl _
  · -- Nodup [0,1]
    have hnodes : RTree.nodes (RTree.node (0 : Nat)
        [(⟨0, by decide⟩, RTree.node (1 : Nat) [])] : RTree zChain) = [(0 : Nat), (1 : Nat)] := rfl
    rw [hnodes]
    refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · intro hmem
      rcases List.mem_cons.mp hmem with h | h
      · exact absurd h (by decide : (0 : Nat) ≠ 1)
      · exact absurd h (List.not_mem_nil)
    · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩

#print axioms witnessAdjSpanning_spec

end YMGap.Continuum.SpanningTreeBuild
