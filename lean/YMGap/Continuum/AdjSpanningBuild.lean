import YMGap.Continuum.SpanningTreeBuild

/-!
# Discharging the spanning-tree count: the boundary-crossing lemma and the
constructive BFS tree build

This file attacks `SpanningTreeBuild.AdjSpanningTree` — the entire remaining
combinatorial content of the cluster-count over-count guarantee — from below.

## The honest connectivity notion (load-bearing) — now CANONICAL

The naive `PolymerModel.connected X` says: for every two plaquettes `p q ∈ X`,
there is a `ChainConn` chain joining them.  Crucially `ChainConn` is a chain
over the **whole lattice** — its intermediate plaquettes need NOT lie in `X`.
Under that (weak) notion a spanning tree is genuinely FALSE: take `X = [p, v]`
with `p`, `v` not link-adjacent but joined only through an external plaquette
`r ∉ X`; then `connected X` holds, yet any tree on the 2-element support
`{p, v}` needs a single edge `p — v` carrying `Adjacent p v`, which does not
exist.

The correct combinatorial notion for a *lattice animal* (and what the cluster
expansion actually sums over) is **internal** connectivity: chains every node
of which lies in `X`.  This is `ChainIn` / `connectedIn` (now living upstream in
`PolymerModel`), and the canonical cluster predicate `IsClusterThrough` =
`IsClusterThroughIn` (in `BddLatticeAnimal`) is built from it (internal
connectivity + `Nodup` support).  We prove the genuine spanning-tree existence
for it, FULLY:

  * `boundaryCrossing` — THE mathematical heart: an internal chain from an
    in-`visited` source to an out-of-`visited` target must cross the boundary,
    i.e. yields an `Adjacent u w` with `u ∈ visited`, `w ∈ X`, `w ∉ visited`.
    Proved by structural induction on `ChainIn`.

  * a constructive **BFS/worklist tree build** (`grow` + fuel recursion) that
    assembles a `Faithful`-free `AdjacentEdges`-annotated `RTree` on exactly
    `X`'s support, with `Nodup` nodes and root `p`, BY CONSTRUCTION.

  * `adjSpanningTreeInternal` — the full `AdjSpanningTree` statement, but with
    the *internal* cluster predicate `IsClusterThroughIn`.  PROVED.

Because the canonical cluster predicate `IsClusterThrough` IS the internal
animal predicate (`IsClusterThroughIn`), the former "ambient-vs-internal"
refinement obligation collapses to the identity (`internalConnRefines`), and
`AdjSpanningTree` is closed UNCONDITIONALLY by `adjSpanningTreeInternal`
(`adjSpanningTree_unconditional`).  This yields the unconditional terminal
`clusterCountBound_animal`: the genuine cluster-count bound plus the over-count
guarantee over real lattice animals, with NO named-open obligation.

## Constructive contract (`lean/AGENTS.md`)

Mathlib-free; only core `List`/`Nat`/`Fin`.  No `Classical.*`, no `sorry` /
`admit` / new `axiom`.  Membership tests use the `BddLattice.decEq` instance
(constructive `Decidable`), never `Classical.dec`.  Witnesses are Type-level
data.
-/

namespace YMGap.Continuum.AdjSpanningBuild

open YMGap.Continuum.PolymerModel
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.DecodeTourSound
open YMGap.Continuum.SpanningTreeBuild

/-! ## 0. `Adjacent` is symmetric (swap the two incidence proofs) -/

/-- Link-adjacency is symmetric: the same shared link witnesses `Adjacent q p`. -/
def adjacentSymm {L : Lattice} {p q : L.Plaquette} (a : L.Adjacent p q) :
    L.Adjacent q p where
  link := a.link
  on_p := a.on_q
  on_q := a.on_p

/-! ## 1. Internal connectivity (`ChainIn` / `connectedIn`) and the animal
predicate `IsClusterThroughIn`

The internal connectivity notions `ChainIn` / `connectedIn` and the canonical
lattice-animal predicate `IsClusterThroughIn` (= `IsClusterThrough`, which is
now itself the internal animal predicate) live UPSTREAM (`PolymerModel` and
`BddLatticeAnimal` respectively); they are opened above.  Recall:

  * `ChainIn L X p q` — a chain `p ⤳ q` every node of which lies in `X`;
  * `connectedIn X := ∀ p q ∈ X, ChainIn L X p q` — internal connectivity;
  * `IsClusterThroughIn BL p n X := size X = n ∧ p ∈ X ∧ X.Nodup ∧
    Nonempty (connectedIn X)` — the genuine lattice-animal predicate.

Because `IsClusterThrough` is now DEFINED to be this animal predicate, the
entire upstream count/completeness chain is stated over real lattice animals,
and the spanning-tree construction below closes it unconditionally. -/

/-! ## 2. THE boundary-crossing lemma (the mathematical heart)

Given an internal chain `c : ChainIn X p v` from a source `p ∈ visited` to a
target `v ∉ visited`, the chain must cross the boundary of `visited`: there is
an edge `Adjacent u w` with `u ∈ visited`, `w ∈ X`, and `w ∉ visited`.

The proof is structural induction on `c`, peeling steps until the first one
whose source is `visited` but whose target is not.  Decidable membership on the
`List` of plaquettes comes from the `BddLattice.decEq` instance — NOT from
`Classical`. -/

/-- **The boundary-crossing lemma (PROVED).**  An internal chain from an
in-`visited` source `p` to an out-of-`visited` target `v` yields a crossing edge
`Adjacent u w` with `u ∈ visited`, `w ∈ X`, `w ∉ visited`.

`ChainIn` induction:
* `refl p`: then `v = p`, so `p ∈ visited` and `v ∉ visited` are contradictory
  (`absurd`).
* `step (adj : Adjacent p r) (hr : r ∈ X) (rest : ChainIn X r v)`: decide
  `r ∈ visited`.  If `r ∉ visited`, the crossing edge is `u := p`, `w := r`
  (`p ∈ visited`, `r ∈ X` from `hr`, `r ∉ visited`, `Adjacent p r` from `adj`).
  If `r ∈ visited`, recurse on `rest` with the new source-membership `r ∈
  visited`, still ending outside `visited` at `v`. -/
def boundaryCrossing {BL : BddLattice} {X : Polymer BL.toLattice} :
    {p v : BL.toLattice.Plaquette} → ChainIn BL.toLattice X p v →
      (visited : List BL.toLattice.Plaquette) →
      p ∈ visited → v ∉ visited →
      Σ' u w : BL.toLattice.Plaquette,
        (u ∈ visited) ×' (w ∈ X) ×' (w ∉ visited) ×'
          BL.toLattice.Adjacent u w
  | p, _, ChainIn.refl _, visited, hp, hv => absurd hp hv
  | p, v, ChainIn.step (r := r) adj hr rest, visited, hp, hv =>
      if hrv : r ∈ visited then
        boundaryCrossing rest visited hrv hv
      else
        ⟨p, r, hp, hr, hrv, adj⟩

/-! ## 3. RTree insertion (zipper-free, first-match) carrying the edge witness

`insertUnder u childTree t` inserts `childTree` as a NEW child under the first
node of `t` whose root equals `u` (decidable equality from `BddLattice.decEq`).
The stored `Fin BL.D` index is irrelevant to `AdjacentEdges` / `RTree.nodes`
(both ignore it), so we thread it as a parameter `i`.  If no node matches `u`,
`t` is returned unchanged. -/

mutual
  /-- Insert `(i, c)` as a new (appended) child under the first node of `t` whose
  root equals `u`. -/
  def insertUnder {BL : BddLattice} (u : BL.toLattice.Plaquette)
      (i : Fin BL.D) (c : RTree BL) : RTree BL → RTree BL
    | .node r ch =>
        if r = u then
          RTree.node r (ch ++ [(i, c)])
        else
          RTree.node r (insertUnderList u i c ch)
  /-- Map `insertUnder` over a child list (inserting into the first matching
  subtree). -/
  def insertUnderList {BL : BddLattice} (u : BL.toLattice.Plaquette)
      (i : Fin BL.D) (c : RTree BL) :
      List (Fin BL.D × RTree BL) → List (Fin BL.D × RTree BL)
    | [] => []
    | (j, t) :: rest => (j, insertUnder u i c t) :: insertUnderList u i c rest
end

/-! ### 3a. `insertUnder` preserves the root -/

theorem insertUnder_root {BL : BddLattice} (u : BL.toLattice.Plaquette)
    (i : Fin BL.D) (c : RTree BL) (t : RTree BL) :
    RTree.root (insertUnder u i c t) = RTree.root t := by
  cases t with
  | node r ch =>
      show RTree.root (if r = u then RTree.node r (ch ++ [(i, c)])
        else RTree.node r (insertUnderList u i c ch)) = r
      by_cases h : r = u
      · rw [if_pos h]; rfl
      · rw [if_neg h]; rfl

/-- `nodesList` distributes over list append. -/
theorem nodesList_append {BL : BddLattice}
    (ch₁ ch₂ : List (Fin BL.D × RTree BL)) :
    RTree.nodesList (ch₁ ++ ch₂)
      = RTree.nodesList ch₁ ++ RTree.nodesList ch₂ := by
  induction ch₁ with
  | nil => rfl
  | cons hd rest ih =>
      obtain ⟨j, t⟩ := hd
      show RTree.nodes t ++ RTree.nodesList (rest ++ ch₂)
        = (RTree.nodes t ++ RTree.nodesList rest) ++ RTree.nodesList ch₂
      rw [ih, List.append_assoc]

/-! ### 3b. `insertUnder` node-membership characterization

`a ∈ nodes (insertUnder u i c t) ↔ a ∈ nodes t ∨ (a ∈ nodes c ∧ u ∈ nodes t)`:
the inserted child's nodes are added exactly when `u` actually occurs in `t`;
otherwise the tree is unchanged.  This holds *unconditionally* (no `u ∈ nodes t`
hypothesis), so the two branches compose cleanly. -/

mutual
  theorem insertUnder_mem {BL : BddLattice} (u : BL.toLattice.Plaquette)
      (i : Fin BL.D) (c : RTree BL) :
      ∀ (t : RTree BL) (a : BL.toLattice.Plaquette),
        (a ∈ RTree.nodes (insertUnder u i c t) ↔
          a ∈ RTree.nodes t ∨ (a ∈ RTree.nodes c ∧ u ∈ RTree.nodes t))
    | .node r ch, a => by
        by_cases h : r = u
        · -- inserted here: nodes = r :: (nodesList ch ++ nodes c)
          have hins : insertUnder u i c (RTree.node r ch)
              = RTree.node r (ch ++ [(i, c)]) := by
            show (if r = u then RTree.node r (ch ++ [(i, c)])
              else RTree.node r (insertUnderList u i c ch)) = _
            rw [if_pos h]
          rw [hins]
          -- nodes (node r (ch ++ [(i,c)])) = r :: nodesList (ch ++ [(i,c)])
          have hnl : RTree.nodes (RTree.node r (ch ++ [(i, c)]))
              = r :: (RTree.nodesList ch ++ RTree.nodes c) := by
            show r :: RTree.nodesList (ch ++ [(i, c)])
              = r :: (RTree.nodesList ch ++ RTree.nodes c)
            rw [nodesList_append]
            show r :: (RTree.nodesList ch ++ RTree.nodesList [(i, c)])
              = r :: (RTree.nodesList ch ++ RTree.nodes c)
            have : RTree.nodesList [(i, c)] = RTree.nodes c := by
              show RTree.nodes c ++ RTree.nodesList ([] : List (Fin BL.D × RTree BL))
                = RTree.nodes c
              show RTree.nodes c ++ [] = RTree.nodes c
              rw [List.append_nil]
            rw [this]
          rw [hnl]
          -- u ∈ nodes (node r ch) = r :: nodesList ch, and r = u so always true
          have huin : u ∈ RTree.nodes (RTree.node r ch) := by
            show u ∈ r :: RTree.nodesList ch
            rw [h]; exact List.mem_cons_self
          constructor
          · intro hmem
            rcases List.mem_cons.mp hmem with h0 | h1
            · exact Or.inl (by show a ∈ r :: RTree.nodesList ch; rw [h0]; exact List.mem_cons_self)
            · rcases List.mem_append.mp h1 with hh | hh
              · exact Or.inl (by show a ∈ r :: RTree.nodesList ch; exact List.mem_cons_of_mem _ hh)
              · exact Or.inr ⟨hh, huin⟩
          · intro hmem
            rcases hmem with h0 | ⟨hc, _⟩
            · rcases List.mem_cons.mp h0 with hh | hh
              · exact List.mem_cons.mpr (Or.inl hh)
              · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hh)))
            · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr hc)))
        · -- not here: recurse into children
          have hins : insertUnder u i c (RTree.node r ch)
              = RTree.node r (insertUnderList u i c ch) := by
            show (if r = u then RTree.node r (ch ++ [(i, c)])
              else RTree.node r (insertUnderList u i c ch)) = _
            rw [if_neg h]
          rw [hins]
          have hnl : RTree.nodes (RTree.node r (insertUnderList u i c ch))
              = r :: RTree.nodesList (insertUnderList u i c ch) := rfl
          rw [hnl]
          constructor
          · intro hmem
            rcases List.mem_cons.mp hmem with h0 | h1
            · exact Or.inl (by show a ∈ r :: RTree.nodesList ch; rw [h0]; exact List.mem_cons_self)
            · rcases (insertUnderList_mem u i c ch a).mp h1 with hh | ⟨hc, hu⟩
              · exact Or.inl (List.mem_cons_of_mem _ hh)
              · exact Or.inr ⟨hc, List.mem_cons_of_mem _ hu⟩
          · intro hmem
            rcases hmem with h0 | ⟨hc, hu⟩
            · rcases List.mem_cons.mp h0 with hh | hh
              · exact List.mem_cons.mpr (Or.inl hh)
              · exact List.mem_cons.mpr (Or.inr ((insertUnderList_mem u i c ch a).mpr (Or.inl hh)))
            · -- u ∈ r :: nodesList ch, but r ≠ u so u ∈ nodesList ch
              rcases List.mem_cons.mp hu with hh | hh
              · exact absurd hh.symm h
              · exact List.mem_cons.mpr (Or.inr ((insertUnderList_mem u i c ch a).mpr (Or.inr ⟨hc, hh⟩)))

  theorem insertUnderList_mem {BL : BddLattice} (u : BL.toLattice.Plaquette)
      (i : Fin BL.D) (c : RTree BL) :
      ∀ (ch : List (Fin BL.D × RTree BL)) (a : BL.toLattice.Plaquette),
        (a ∈ RTree.nodesList (insertUnderList u i c ch) ↔
          a ∈ RTree.nodesList ch ∨ (a ∈ RTree.nodes c ∧ u ∈ RTree.nodesList ch))
    | [], a => by
        constructor
        · intro h; exact Or.inl h
        · intro h
          rcases h with h | ⟨_, hu⟩
          · exact h
          · exact absurd hu (List.not_mem_nil)
    | (j, t) :: rest, a => by
        -- insertUnderList u i c ((j,t)::rest) = (j, insertUnder u i c t) :: insertUnderList u i c rest
        have hnl : RTree.nodesList (insertUnderList u i c ((j, t) :: rest))
            = RTree.nodes (insertUnder u i c t)
              ++ RTree.nodesList (insertUnderList u i c rest) := rfl
        rw [hnl]
        have hnlold : RTree.nodesList ((j, t) :: rest)
            = RTree.nodes t ++ RTree.nodesList rest := rfl
        rw [hnlold]
        constructor
        · intro hmem
          rcases List.mem_append.mp hmem with hh | hh
          · rcases (insertUnder_mem u i c t a).mp hh with h0 | ⟨hc, hu⟩
            · exact Or.inl (List.mem_append.mpr (Or.inl h0))
            · exact Or.inr ⟨hc, List.mem_append.mpr (Or.inl hu)⟩
          · rcases (insertUnderList_mem u i c rest a).mp hh with h0 | ⟨hc, hu⟩
            · exact Or.inl (List.mem_append.mpr (Or.inr h0))
            · exact Or.inr ⟨hc, List.mem_append.mpr (Or.inr hu)⟩
        · intro hmem
          rcases hmem with h0 | ⟨hc, hu⟩
          · rcases List.mem_append.mp h0 with hh | hh
            · exact List.mem_append.mpr (Or.inl ((insertUnder_mem u i c t a).mpr (Or.inl hh)))
            · exact List.mem_append.mpr (Or.inr ((insertUnderList_mem u i c rest a).mpr (Or.inl hh)))
          · rcases List.mem_append.mp hu with hh | hh
            · exact List.mem_append.mpr (Or.inl ((insertUnder_mem u i c t a).mpr (Or.inr ⟨hc, hh⟩)))
            · exact List.mem_append.mpr (Or.inr ((insertUnderList_mem u i c rest a).mpr (Or.inr ⟨hc, hh⟩)))
end

/-! ### 3c. `insertUnder` preserves the `AdjacentEdges` annotation

Given the old annotation `AdjacentEdges t`, a witness `Adjacent u (root c)` and
the child's own annotation `AdjacentEdges c`, we build the annotation of the
inserted tree by construction.  (Type-level data — `AdjacentEdges` carries real
`Adjacent` witnesses; the new edge carries the supplied `Adjacent u (root c)`.) -/

/-- Append on the `AdjacentEdgesList` carrier: combine annotations of two child
lists into the annotation of their concatenation. -/
def adjEdgesListAppend {BL : BddLattice} (r : BL.toLattice.Plaquette) :
    ∀ (ch₁ ch₂ : List (Fin BL.D × RTree BL)),
      AdjacentEdgesList r ch₁ → AdjacentEdgesList r ch₂ →
        AdjacentEdgesList r (ch₁ ++ ch₂)
  | [], ch₂, _, h₂ => h₂
  | (j, t) :: rest, ch₂, h₁, h₂ =>
      ⟨h₁.1, h₁.2.1, adjEdgesListAppend r rest ch₂ h₁.2.2 h₂⟩

mutual
  /-- Build `AdjacentEdges (insertUnder u i c t)` from the old annotation, the
  edge witness `Adjacent u (root c)`, and the child annotation. -/
  def insertUnder_adj {BL : BddLattice} (u : BL.toLattice.Plaquette)
      (i : Fin BL.D) (c : RTree BL)
      (edge : BL.toLattice.Adjacent u (RTree.root c)) (hc : AdjacentEdges c) :
      ∀ (t : RTree BL), AdjacentEdges t → AdjacentEdges (insertUnder u i c t)
    | .node r ch, h =>
        if hru : r = u then by
          have hins : insertUnder u i c (RTree.node r ch)
              = RTree.node r (ch ++ [(i, c)]) := by
            show (if r = u then RTree.node r (ch ++ [(i, c)])
              else RTree.node r (insertUnderList u i c ch)) = _
            rw [if_pos hru]
          rw [hins]
          show AdjacentEdgesList r (ch ++ [(i, c)])
          -- the new singleton child annotation: Adjacent r (root c) × AdjacentEdges c × PUnit
          have edge' : BL.toLattice.Adjacent r (RTree.root c) := by rw [hru]; exact edge
          have htail : AdjacentEdgesList r [(i, c)] :=
            ⟨edge', hc, PUnit.unit⟩
          exact adjEdgesListAppend r ch [(i, c)] (h : AdjacentEdgesList r ch) htail
        else by
          have hins : insertUnder u i c (RTree.node r ch)
              = RTree.node r (insertUnderList u i c ch) := by
            show (if r = u then RTree.node r (ch ++ [(i, c)])
              else RTree.node r (insertUnderList u i c ch)) = _
            rw [if_neg hru]
          rw [hins]
          show AdjacentEdgesList r (insertUnderList u i c ch)
          exact insertUnderList_adj u i c edge hc r ch (h : AdjacentEdgesList r ch)
  /-- List version of `insertUnder_adj`. -/
  def insertUnderList_adj {BL : BddLattice} (u : BL.toLattice.Plaquette)
      (i : Fin BL.D) (c : RTree BL)
      (edge : BL.toLattice.Adjacent u (RTree.root c)) (hc : AdjacentEdges c)
      (r : BL.toLattice.Plaquette) :
      ∀ (ch : List (Fin BL.D × RTree BL)), AdjacentEdgesList r ch →
        AdjacentEdgesList r (insertUnderList u i c ch)
    | [], _ => PUnit.unit
    | (j, t) :: rest, h =>
        -- need: Adjacent r (root (insertUnder u i c t)) × AdjacentEdges (insertUnder..) × ...
        ⟨by rw [insertUnder_root u i c t]; exact h.1,
         insertUnder_adj u i c edge hc t h.2.1,
         insertUnderList_adj u i c edge hc r rest h.2.2⟩
end

/-! ### 3d. `insertUnder` preserves `Nodup` of the node list

If `t`'s nodes are distinct, `c`'s nodes are distinct, and the two node sets are
disjoint, then the inserted tree's nodes are distinct.  (For our use `c =
node w []`, a single fresh `w ∉ nodes t`.)  Proved by mutual induction using the
membership characterization `insertUnder_mem` to relocate the freshness
conditions through the recursion. -/

/-- Disjointness of two node lists: no common element. -/
def Disj {BL : BddLattice} (l₁ l₂ : List BL.toLattice.Plaquette) : Prop :=
  ∀ a, a ∈ l₁ → a ∈ l₂ → False

theorem disj_symm {BL : BddLattice} {l₁ l₂ : List BL.toLattice.Plaquette}
    (h : Disj l₁ l₂) : Disj l₂ l₁ := fun a ha hb => h a hb ha

/-- Bridge to the `nodup_append` disjointness shape. -/
theorem nodup_append_of_disj {BL : BddLattice}
    {l₁ l₂ : List BL.toLattice.Plaquette}
    (h1 : l₁.Nodup) (h2 : l₂.Nodup) (hd : Disj l₁ l₂) : (l₁ ++ l₂).Nodup :=
  List.nodup_append.mpr ⟨h1, h2, fun a ha b hb hab => hd a ha (hab ▸ hb)⟩

mutual
  theorem insertUnder_nodup {BL : BddLattice} (u : BL.toLattice.Plaquette)
      (i : Fin BL.D) (c : RTree BL) (hcnd : (RTree.nodes c).Nodup) :
      ∀ (t : RTree BL), (RTree.nodes t).Nodup →
        Disj (RTree.nodes t) (RTree.nodes c) →
        (RTree.nodes (insertUnder u i c t)).Nodup
    | .node r ch, hnd, hdisj => by
        have hndr : (r :: RTree.nodesList ch).Nodup := hnd
        have hrni : r ∉ RTree.nodesList ch := (List.nodup_cons.mp hndr).1
        have hndch : (RTree.nodesList ch).Nodup := (List.nodup_cons.mp hndr).2
        have hrin : r ∈ RTree.nodes (RTree.node r ch) := List.mem_cons_self
        have hrnc : r ∉ RTree.nodes c := fun h => hdisj r hrin h
        by_cases hru : r = u
        · have hins : insertUnder u i c (RTree.node r ch)
              = RTree.node r (ch ++ [(i, c)]) := by
            show (if r = u then RTree.node r (ch ++ [(i, c)])
              else RTree.node r (insertUnderList u i c ch)) = _
            rw [if_pos hru]
          rw [hins]
          have hnl : RTree.nodes (RTree.node r (ch ++ [(i, c)]))
              = r :: (RTree.nodesList ch ++ RTree.nodes c) := by
            show r :: RTree.nodesList (ch ++ [(i, c)])
              = r :: (RTree.nodesList ch ++ RTree.nodes c)
            rw [nodesList_append]
            have hsng : RTree.nodesList [(i, c)] = RTree.nodes c := by
              show RTree.nodes c ++ RTree.nodesList ([] : List (Fin BL.D × RTree BL))
                = RTree.nodes c
              exact List.append_nil _
            rw [hsng]
          rw [hnl]
          refine List.nodup_cons.mpr ⟨?_, ?_⟩
          · intro hmem
            rcases List.mem_append.mp hmem with hh | hh
            · exact hrni hh
            · exact hrnc hh
          · -- Nodup (nodesList ch ++ nodes c): disjoint via nodes t disjointness
            refine nodup_append_of_disj hndch hcnd ?_
            intro a ha hb
            exact hdisj a (List.mem_cons_of_mem _ ha) hb
        · have hins : insertUnder u i c (RTree.node r ch)
              = RTree.node r (insertUnderList u i c ch) := by
            show (if r = u then RTree.node r (ch ++ [(i, c)])
              else RTree.node r (insertUnderList u i c ch)) = _
            rw [if_neg hru]
          rw [hins]
          have hnl : RTree.nodes (RTree.node r (insertUnderList u i c ch))
              = r :: RTree.nodesList (insertUnderList u i c ch) := rfl
          rw [hnl]
          refine List.nodup_cons.mpr ⟨?_, ?_⟩
          · intro hmem
            rcases (insertUnderList_mem u i c ch r).mp hmem with hh | ⟨hc, _⟩
            · exact hrni hh
            · exact hrnc hc
          · refine insertUnderList_nodup u i c hcnd ch hndch ?_
            intro a ha hb
            exact hdisj a (List.mem_cons_of_mem _ ha) hb

  theorem insertUnderList_nodup {BL : BddLattice} (u : BL.toLattice.Plaquette)
      (i : Fin BL.D) (c : RTree BL) (hcnd : (RTree.nodes c).Nodup) :
      ∀ (ch : List (Fin BL.D × RTree BL)), (RTree.nodesList ch).Nodup →
        Disj (RTree.nodesList ch) (RTree.nodes c) →
        (RTree.nodesList (insertUnderList u i c ch)).Nodup
    | [], hnd, _ => hnd
    | (j, t) :: rest, hnd, hdisj => by
        have hcat : (RTree.nodes t ++ RTree.nodesList rest).Nodup := hnd
        have hp := List.nodup_append.mp hcat
        have hndt : (RTree.nodes t).Nodup := hp.1
        have hndrest : (RTree.nodesList rest).Nodup := hp.2.1
        have hdisjtr : Disj (RTree.nodes t) (RTree.nodesList rest) :=
          fun a ha hb => hp.2.2 a ha a hb rfl
        -- disjointness of each half from nodes c
        have hdisjt : Disj (RTree.nodes t) (RTree.nodes c) :=
          fun a ha hb => hdisj a (List.mem_append.mpr (Or.inl ha)) hb
        have hdisjrest : Disj (RTree.nodesList rest) (RTree.nodes c) :=
          fun a ha hb => hdisj a (List.mem_append.mpr (Or.inr ha)) hb
        have hnl : RTree.nodesList (insertUnderList u i c ((j, t) :: rest))
            = RTree.nodes (insertUnder u i c t)
              ++ RTree.nodesList (insertUnderList u i c rest) := rfl
        rw [hnl]
        refine nodup_append_of_disj
          (insertUnder_nodup u i c hcnd t hndt hdisjt)
          (insertUnderList_nodup u i c hcnd rest hndrest hdisjrest) ?_
        -- Disj between the two inserted halves.
        intro a ha hb
        -- a ∈ nodes(insertUnder u i c t) ↔ a ∈ nodes t ∨ (a ∈ nodes c ∧ u ∈ nodes t)
        rcases (insertUnder_mem u i c t a).mp ha with hat | ⟨hac, hut⟩
        · rcases (insertUnderList_mem u i c rest a).mp hb with hbr | ⟨hac2, _⟩
          · -- a ∈ nodes t and a ∈ nodesList rest: original disjoint
            exact hdisjtr a hat hbr
          · -- a ∈ nodes t and a ∈ nodes c: hdisjt
            exact hdisjt a hat hac2
        · rcases (insertUnderList_mem u i c rest a).mp hb with hbr | ⟨_, hur⟩
          · -- a ∈ nodes c and a ∈ nodesList rest: hdisjrest
            exact hdisjrest a hbr hac
          · -- u ∈ nodes t AND u ∈ nodesList rest: contradicts original Nodup disjoint
            exact hdisjtr u hut hur
end

/-! ## 4. Finding a fresh node, or certifying coverage

`findFresh X visited` either produces a node `v ∈ X` with `v ∉ visited` (data),
or certifies `X ⊆ visited` (every member of `X` is visited).  Pure list
recursion with the decidable membership instance — no `Classical`. -/

/-- Either a fresh `X`-node outside `visited`, or a proof that `visited` covers
`X`. -/
def findFresh {BL : BddLattice} (visited : List BL.toLattice.Plaquette) :
    ∀ (X : List BL.toLattice.Plaquette),
      (Σ' v : BL.toLattice.Plaquette, (v ∈ X) ×' (v ∉ visited)) ⊕'
        (∀ a, a ∈ X → a ∈ visited)
  | [] => PSum.inr (fun a ha => absurd ha (List.not_mem_nil))
  | x :: rest =>
      if hx : x ∈ visited then
        match findFresh visited rest with
        | PSum.inl ⟨v, hv, hvn⟩ =>
            PSum.inl ⟨v, List.mem_cons_of_mem _ hv, hvn⟩
        | PSum.inr hcov =>
            PSum.inr (fun a ha => by
              rcases List.mem_cons.mp ha with h | h
              · rw [h]; exact hx
              · exact hcov a h)
      else
        PSum.inl ⟨x, List.mem_cons_self, hx⟩

/-! A hand-rolled, `Classical`-free first-occurrence removal on plaquette lists.
The Mathlib-partial `List.erase` lemmas (`length_erase_of_mem`,
`mem_erase_of_ne`) drag in `Classical.choice`, so we re-derive exactly the two
facts we need (`remOne` length and membership) constructively, using only the
`BddLattice.decEq` instance. -/

/-- Remove the first occurrence of `x` from `l` (constructive, via `decEq`). -/
def remOne {BL : BddLattice} (x : BL.toLattice.Plaquette) :
    List BL.toLattice.Plaquette → List BL.toLattice.Plaquette
  | [] => []
  | a :: rest => if a = x then rest else a :: remOne x rest

/-- If `x ∈ l`, removing one occurrence drops the length by exactly one. -/
theorem remOne_length {BL : BddLattice} (x : BL.toLattice.Plaquette) :
    ∀ (l : List BL.toLattice.Plaquette), x ∈ l →
      (remOne x l).length + 1 = l.length
  | [], h => absurd h List.not_mem_nil
  | a :: rest, h => by
      show (if a = x then rest else a :: remOne x rest).length + 1
        = (a :: rest).length
      by_cases hax : a = x
      · rw [if_pos hax]; rw [List.length_cons]
      · rw [if_neg hax, List.length_cons, List.length_cons]
        have hxr : x ∈ rest := by
          rcases List.mem_cons.mp h with hh | hh
          · exact absurd hh.symm hax
          · exact hh
        have ih := remOne_length x rest hxr
        omega

/-- A member `b ≠ x` of `l` survives the removal of `x`. -/
theorem mem_remOne {BL : BddLattice} (x : BL.toLattice.Plaquette) :
    ∀ (l : List BL.toLattice.Plaquette) (b : BL.toLattice.Plaquette),
      b ∈ l → b ≠ x → b ∈ remOne x l
  | [], b, h, _ => absurd h List.not_mem_nil
  | a :: rest, b, h, hbx => by
      show b ∈ (if a = x then rest else a :: remOne x rest)
      by_cases hax : a = x
      · rw [if_pos hax]
        rcases List.mem_cons.mp h with hh | hh
        · exact absurd (hh.trans hax) hbx
        · exact hh
      · rw [if_neg hax]
        rcases List.mem_cons.mp h with hh | hh
        · rw [hh]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (mem_remOne x rest b hh hbx)

/-- **A Nodup list embedded (as a set) in `X` is no longer than `X`.**  Proved
by induction on the Nodup list, removing the head from `X` (via the
`Classical`-free `remOne`) at each step. -/
theorem nodup_subset_length_le {BL : BddLattice} :
    ∀ (l X : List BL.toLattice.Plaquette), l.Nodup → (∀ a, a ∈ l → a ∈ X) →
      l.length ≤ X.length
  | [], X, _, _ => Nat.zero_le _
  | a :: l', X, hnd, hsub => by
      have hai : a ∈ X := hsub a List.mem_cons_self
      have hndcons := List.nodup_cons.mp hnd
      have hanl : a ∉ l' := hndcons.1
      have hndl' : l'.Nodup := hndcons.2
      -- l' ⊆ remOne a X
      have hsub' : ∀ b, b ∈ l' → b ∈ remOne a X := by
        intro b hb
        have hbne : b ≠ a := fun h => hanl (h ▸ hb)
        exact mem_remOne a X b (hsub b (List.mem_cons_of_mem _ hb)) hbne
      have ih := nodup_subset_length_le l' (remOne a X) hndl' hsub'
      have hrem : (remOne a X).length + 1 = X.length := remOne_length a X hai
      show l'.length + 1 ≤ X.length
      omega

/-! ## 5. The BFS tree-build state and the `grow` recursion

`BFSState` carries the partial tree on a subset of `X` together with all the
invariants needed for `AdjSpanningTree`: the tree's root is `p`, its nodes are a
distinct subset of `X`, and the tree carries a genuine `AdjacentEdges`
annotation.  `grow` repeatedly attaches a fresh `X`-node found by
`boundaryCrossing`, terminating (fuel = `size X`) at coverage. -/

/-- The invariant-carrying partial spanning-tree state. -/
structure BFSState (BL : BddLattice) (p : BL.toLattice.Plaquette)
    (X : Polymer BL.toLattice) : Type where
  /-- The partial tree built so far. -/
  tree : RTree BL
  /-- Its root is the base plaquette `p`. -/
  root_eq : RTree.root tree = p
  /-- Its nodes are a subset of `X`. -/
  sub : ∀ a, a ∈ RTree.nodes tree → a ∈ X
  /-- Its nodes are distinct. -/
  nodup : (RTree.nodes tree).Nodup
  /-- Every tree edge is a genuine lattice adjacency. -/
  adj : AdjacentEdges tree

/-- The root `p` is always a node of the tree (it is the root). -/
theorem root_mem_nodes {BL : BddLattice} (t : RTree BL) :
    RTree.root t ∈ RTree.nodes t := by
  cases t with
  | node r ch => exact List.mem_cons_self

/-- The initial state: the single-node tree `node p []`. -/
def initBFS {BL : BddLattice} (p : BL.toLattice.Plaquette)
    (X : Polymer BL.toLattice) (hp : p ∈ X) : BFSState BL p X where
  tree := RTree.node p []
  root_eq := rfl
  sub := by
    intro a ha
    -- nodes (node p []) = [p]
    have : a ∈ [p] := ha
    rw [List.mem_singleton.mp this]; exact hp
  nodup := by
    show ([p] : List BL.toLattice.Plaquette).Nodup
    exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  adj := PUnit.unit

/-- **One growth step.**  Given a state whose nodes do NOT yet cover `X` (a fresh
node `v ∈ X`, `v ∉ nodes`) and an internal-connectivity witness, attach a fresh
`X`-node via `boundaryCrossing` + `insertUnder`, returning a state with one more
node.  All invariants are re-established by the §3 preservation lemmas. -/
def growStep {BL : BddLattice} {p : BL.toLattice.Plaquette}
    {X : Polymer BL.toLattice} (conn : connectedIn X) (hp : p ∈ X)
    (st : BFSState BL p X)
    (v : BL.toLattice.Plaquette) (hv : v ∈ X) (hvn : v ∉ RTree.nodes st.tree) :
    Σ' st' : BFSState BL p X,
      (RTree.nodes st'.tree).length = (RTree.nodes st.tree).length + 1 := by
  -- p is in the current nodes (it is the root)
  have hpnodes : p ∈ RTree.nodes st.tree := by
    have := root_mem_nodes st.tree
    rw [st.root_eq] at this; exact this
  -- internal chain p ⤳ v
  have chain : ChainIn BL.toLattice X p v := conn p v hp hv
  -- boundary crossing on visited = nodes
  obtain ⟨u, w, hu, hwX, hwn, edge⟩ :=
    boundaryCrossing chain (RTree.nodes st.tree) hpnodes hvn
  -- new child tree: node w []
  let c : RTree BL := RTree.node w []
  -- index from the adjacency (BL.D might be 0 only if no adjacency; faithIndex provides one)
  let idx : Fin BL.D := (faithIndex edge).1
  have hcroot : RTree.root c = w := rfl
  have hcnd : (RTree.nodes c).Nodup := by
    show ([w] : List BL.toLattice.Plaquette).Nodup
    exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  have hcnodes : RTree.nodes c = [w] := rfl
  -- disjointness: w ∉ nodes st.tree, and nodes c = [w]
  have hdisj : Disj (RTree.nodes st.tree) (RTree.nodes c) := by
    intro a ha hac
    rw [hcnodes] at hac
    rw [List.mem_singleton.mp hac] at ha
    exact hwn ha
  -- the inserted tree
  let newtree : RTree BL := insertUnder u idx c st.tree
  -- adjacency edge witness Adjacent u (root c) = Adjacent u w
  have edge' : BL.toLattice.Adjacent u (RTree.root c) := by rw [hcroot]; exact edge
  have hcadj : AdjacentEdges c := PUnit.unit
  refine ⟨{
    tree := newtree
    root_eq := by
      show RTree.root (insertUnder u idx c st.tree) = p
      rw [insertUnder_root u idx c st.tree]; exact st.root_eq
    sub := by
      intro a ha
      rcases (insertUnder_mem u idx c st.tree a).mp ha with h | ⟨hc, _⟩
      · exact st.sub a h
      · rw [hcnodes] at hc; rw [List.mem_singleton.mp hc]; exact hwX
    nodup := insertUnder_nodup u idx c hcnd st.tree st.nodup hdisj
    adj := insertUnder_adj u idx c edge' hcadj st.tree st.adj
  }, ?_⟩
  -- length grows by exactly 1.  `nodes newtree` and `w :: nodes st.tree` have the
  -- SAME membership set (membership char + u ∈ nodes st), and both are Nodup, so
  -- they have equal length (two-sided `nodup_subset_length_le`).
  show (RTree.nodes newtree).length = (RTree.nodes st.tree).length + 1
  have hunodes : u ∈ RTree.nodes st.tree := hu
  -- membership equivalence between nodes newtree and (w :: nodes st.tree)
  have hmemeq : ∀ a, a ∈ RTree.nodes newtree ↔ a ∈ (w :: RTree.nodes st.tree) := by
    intro a
    constructor
    · intro ha
      rcases (insertUnder_mem u idx c st.tree a).mp ha with h | ⟨hc, _⟩
      · exact List.mem_cons_of_mem _ h
      · rw [hcnodes] at hc
        rw [List.mem_singleton.mp hc]; exact List.mem_cons_self
    · intro ha
      rcases List.mem_cons.mp ha with h | h
      · -- a = w : inserted since u ∈ nodes st
        refine (insertUnder_mem u idx c st.tree a).mpr (Or.inr ⟨?_, hunodes⟩)
        rw [hcnodes, h]; exact List.mem_cons_self
      · exact (insertUnder_mem u idx c st.tree a).mpr (Or.inl h)
  -- both Nodup
  have hndnew : (RTree.nodes newtree).Nodup :=
    insertUnder_nodup u idx c hcnd st.tree st.nodup hdisj
  have hndcons : (w :: RTree.nodes st.tree).Nodup :=
    List.nodup_cons.mpr ⟨hwn, st.nodup⟩
  have hle1 : (RTree.nodes newtree).length ≤ (w :: RTree.nodes st.tree).length :=
    nodup_subset_length_le _ _ hndnew (fun a ha => (hmemeq a).mp ha)
  have hle2 : (w :: RTree.nodes st.tree).length ≤ (RTree.nodes newtree).length :=
    nodup_subset_length_le _ _ hndcons (fun a ha => (hmemeq a).mpr ha)
  have heq : (RTree.nodes newtree).length = (w :: RTree.nodes st.tree).length :=
    Nat.le_antisymm hle1 hle2
  rw [heq]
  rfl

/-! ## 6. The fuel recursion to coverage

`grow` iterates `growStep` until the tree's nodes cover `X`.  The fuel is a
`Nat` with the invariant `size X ≤ fuel + (nodes tree).length`; each step
decrements fuel and increments the node count, preserving it.  At `fuel = 0` we
have `size X ≤ (nodes tree).length`; if a fresh node still existed it would make
a Nodup subset of `X` strictly longer than `X` (`nodup_subset_length_le`),
absurd — so coverage holds. -/

/-- **The fuel recursion (PROVED).**  From any state satisfying the
fuel-deficit invariant, produce a state whose nodes cover `X`. -/
def grow {BL : BddLattice} {p : BL.toLattice.Plaquette}
    {X : Polymer BL.toLattice} (conn : connectedIn X) (hp : p ∈ X) :
    ∀ (fuel : Nat) (st : BFSState BL p X),
      Polymer.size X ≤ fuel + (RTree.nodes st.tree).length →
      Σ' st' : BFSState BL p X, (∀ a, a ∈ X → a ∈ RTree.nodes st'.tree)
  | 0, st, hinv => by
      -- size X ≤ nodes.length; with Nodup subset, equality, so coverage.
      refine ⟨st, ?_⟩
      intro a ha
      -- if a ∉ nodes, then a :: nodes is a Nodup subset of X of length+1 > size X
      by_cases hin : a ∈ RTree.nodes st.tree
      · exact hin
      · exfalso
        have hcons : (a :: RTree.nodes st.tree).Nodup :=
          List.nodup_cons.mpr ⟨hin, st.nodup⟩
        have hsub : ∀ b, b ∈ (a :: RTree.nodes st.tree) → b ∈ X := by
          intro b hb
          rcases List.mem_cons.mp hb with h | h
          · rw [h]; exact ha
          · exact st.sub b h
        have hle := nodup_subset_length_le _ _ hcons hsub
        -- (a :: nodes).length = nodes.length + 1 ≤ X.length = size X ≤ 0 + nodes.length
        have hsize : Polymer.size X = X.length := rfl
        rw [hsize] at hinv
        simp only [Nat.zero_add] at hinv
        -- hinv : X.length ≤ nodes.length ; hle : nodes.length + 1 ≤ X.length
        have : (RTree.nodes st.tree).length + 1 ≤ X.length := hle
        omega
  | fuel + 1, st, hinv => by
      match hf : findFresh (RTree.nodes st.tree) X with
      | PSum.inr hcov =>
          exact ⟨st, hcov⟩
      | PSum.inl ⟨v, hv, hvn⟩ =>
          obtain ⟨st', hlen⟩ := growStep conn hp st v hv hvn
          -- invariant: size X ≤ fuel + nodes st'.length = fuel + (nodes st.length + 1)
          have hinv' : Polymer.size X ≤ fuel + (RTree.nodes st'.tree).length := by
            rw [hlen]; omega
          exact grow conn hp fuel st' hinv'

/-! ## 7. The full internal spanning-tree existence (PROVED)

Running `grow` from `initBFS` with fuel `size X` produces a tree on exactly
`X`'s support: root `p`, node count `n`, `sameSupport X nodes`, `Nodup`, and a
genuine `AdjacentEdges` annotation.  This is the verbatim body of
`AdjSpanningTree`, for the internal lattice-animal predicate. -/

/-- **Internal spanning-tree existence (PROVED).**  For every internally
connected size-`n` lattice animal `X` through `p`, there is a rooted tree with
root `p`, `n` distinct nodes whose support is exactly `X`, every edge a genuine
lattice adjacency.  This is the full content of `AdjSpanningTree` under the
honest lattice-animal predicate `IsClusterThroughIn`. -/
theorem adjSpanningTreeInternal (BL : BddLattice) (p : BL.toLattice.Plaquette)
    (n : Nat) (X : Polymer BL.toLattice) (hX : IsClusterThroughIn BL p n X) :
    ∃ t : RTree BL,
      RTree.root t = p ∧
      (RTree.nodes t).length = n ∧
      sameSupport X (RTree.nodes t) ∧
      (RTree.nodes t).Nodup ∧
      Nonempty (AdjacentEdges t) := by
  obtain ⟨hsize, hp, hXnd, ⟨conn⟩⟩ := hX
  -- build via grow from initBFS, fuel = size X
  obtain ⟨st, hcov⟩ :=
    grow conn hp (Polymer.size X) (initBFS p X hp)
      (by
        -- size X ≤ size X + (nodes (initBFS)).length
        exact Nat.le_add_right _ _)
  -- st.tree is the spanning tree
  refine ⟨st.tree, st.root_eq, ?_, ?_, st.nodup, ⟨st.adj⟩⟩
  · -- length = n : nodes ⊆ X and X ⊆ nodes, both Nodup, so length = X.length = n
    have hle1 : (RTree.nodes st.tree).length ≤ X.length :=
      nodup_subset_length_le _ _ st.nodup st.sub
    have hle2 : X.length ≤ (RTree.nodes st.tree).length :=
      nodup_subset_length_le _ _ hXnd hcov
    have : (RTree.nodes st.tree).length = X.length := Nat.le_antisymm hle1 hle2
    rw [this]; exact hsize
  · -- sameSupport X (nodes st.tree)
    exact ⟨fun a ha => hcov a ha, fun a ha => st.sub a ha⟩

#print axioms adjSpanningTreeInternal

/-! ## 8. `AdjSpanningTree` UNCONDITIONALLY (the residual is now `id`)

In the prior shape, the only gap between `adjSpanningTreeInternal` and the
verbatim `SpanningTreeBuild.AdjSpanningTree` was a connectivity/`Nodup`
mismatch between an *ambient* cluster predicate and the honest lattice-animal
predicate, isolated as a named Prop `InternalConnRefines`.  That predicate is
now **definitionally trivial**: `IsClusterThrough` is DEFINED to be the internal
animal predicate `IsClusterThroughIn`, so the "refinement" is the identity and
`AdjSpanningTree` follows directly from the fully-proved
`adjSpanningTreeInternal` — with NO open obligation. -/

/-- **The former named residual, now PROVED as the identity.**  Every cluster
satisfying `IsClusterThrough` is an internal lattice animal `IsClusterThroughIn`
— because the two predicates are now definitionally equal.  Retained as a
proved lemma (no longer a hypothesis) to document that the gap is closed. -/
theorem internalConnRefines (BL : BddLattice) (p : BL.toLattice.Plaquette)
    (n : Nat) :
    ∀ X : Polymer BL.toLattice, IsClusterThrough BL p n X →
      IsClusterThroughIn BL p n X :=
  fun _X hX => hX

/-- **`AdjSpanningTree` UNCONDITIONALLY (PROVED).**  Since the cluster predicate
is the internal animal predicate, the fully-proved `adjSpanningTreeInternal`
discharges `SpanningTreeBuild.AdjSpanningTree` directly, with no hypothesis. -/
theorem adjSpanningTree_unconditional (BL : BddLattice)
    (p : BL.toLattice.Plaquette) (n : Nat) :
    SpanningTreeBuild.AdjSpanningTree BL p n := by
  intro X hX
  exact adjSpanningTreeInternal BL p n X (internalConnRefines BL p n X hX)

/-- **The terminal unconditional cluster-count bound over real lattice animals
(PROVED).**  The genuine cluster-count bound `ClusterCountBound` together with
the over-count guarantee — every connected size-`n` lattice animal through `p`
is represented (up to support) in the decoded enumeration `enumPolys` — with NO
named-open obligation: the spanning-tree existence is supplied unconditionally
by `adjSpanningTree_unconditional`, anchored on the fully-proved
`adjSpanningTreeInternal`.

This supersedes the former obligation-carrying `clusterCountBound_of_adj` /
`clusterCountBound_of_exists` / `clusterCountBound_genuine`: the spanning-tree
hypothesis they took is now discharged. -/
def clusterCountBound_animal (BL : BddLattice) (p : BL.toLattice.Plaquette) :
    (cc : YMGap.Continuum.KPCriterion.ClusterCountBound BL.toLattice p) ×'
      (∀ n X, IsClusterThroughIn BL p n X →
        ∃ Y, Y ∈ enumPolys BL p n ∧ sameSupport X Y) :=
  SpanningTreeBuild.clusterCountBound_of_adj BL p
    (fun n => adjSpanningTree_unconditional BL p n)

/-! ## 9. Non-vacuity of the animal predicate + the internal builder

The canonical animal predicate is inhabited on a genuine instance: the concrete
cluster `X = [0, 1]` on `zChain` (internally connected, `Nodup`, size 2) is an
internal animal, and `adjSpanningTreeInternal` builds a real adjacent-edge
spanning tree for it.  This guarantees the unconditional terminal
`clusterCountBound_animal` is NOT vacuously over an empty class of animals: the
over-count guarantee has at least this real cluster to represent. -/

/-- The integer-chain internal chain `0 ⤳ 1` (one adjacency step, `1 ∈ X`). -/
def zChainChainIn01 :
    ChainIn zChain.toLattice ([(0 : Nat), (1 : Nat)] : Polymer zChain.toLattice)
      (0 : Nat) (1 : Nat) :=
  ChainIn.step zChainAdj01 (List.mem_cons_of_mem _ List.mem_cons_self)
    (@ChainIn.refl zChain.toLattice ([(0 : Nat), (1 : Nat)] : Polymer zChain.toLattice) (1 : Nat))

/-- The integer-chain internal chain `1 ⤳ 0`. -/
def zChainChainIn10 :
    ChainIn zChain.toLattice ([(0 : Nat), (1 : Nat)] : Polymer zChain.toLattice)
      (1 : Nat) (0 : Nat) :=
  ChainIn.step (adjacentSymm zChainAdj01) List.mem_cons_self
    (@ChainIn.refl zChain.toLattice ([(0 : Nat), (1 : Nat)] : Polymer zChain.toLattice) (0 : Nat))

/-- A member of `[0,1]` is `0` or `1` (as a `Prop`, usable to `rw` a `Type`
goal). -/
theorem mem_zero_one {a : Nat} (ha : a ∈ ([(0 : Nat), (1 : Nat)] : List Nat)) :
    a = 0 ∨ a = 1 := by
  rcases List.mem_cons.mp ha with h | h
  · exact Or.inl h
  · exact Or.inr (List.mem_singleton.mp h)

/-- `X = [0,1]` on `zChain` is internally connected.  We avoid eliminating the
`Prop`-valued membership into the `Type`-valued `ChainIn` goal by extracting the
value equalities as `Prop`s (`mem_zero_one`) and rewriting. -/
def zChainConnectedIn :
    connectedIn ([(0 : Nat), (1 : Nat)] : Polymer zChain.toLattice) := by
  intro a b ha hb
  by_cases ha0 : a = (0 : Nat)
  · by_cases hb0 : b = (0 : Nat)
    · rw [ha0, hb0]; exact ChainIn.refl _
    · have hb1 : b = (1 : Nat) := (mem_zero_one hb).resolve_left hb0
      rw [ha0, hb1]; exact zChainChainIn01
  · have ha1 : a = (1 : Nat) := (mem_zero_one ha).resolve_left ha0
    by_cases hb0 : b = (0 : Nat)
    · rw [ha1, hb0]; exact zChainChainIn10
    · have hb1 : b = (1 : Nat) := (mem_zero_one hb).resolve_left hb0
      rw [ha1, hb1]; exact ChainIn.refl _

/-- **Non-vacuity of the internal animal predicate (PROVED).**  `X = [0,1]` on
`zChain` is a genuine internally connected size-2 lattice animal through `0`. -/
theorem zChainIsClusterIn :
    IsClusterThroughIn zChain (0 : Nat) 2
      ([(0 : Nat), (1 : Nat)] : Polymer zChain.toLattice) :=
  ⟨rfl, List.mem_cons_self, by
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro hm
        rcases List.mem_cons.mp hm with h | h
        · exact absurd h (by decide : (0 : Nat) ≠ 1)
        · exact absurd h List.not_mem_nil
      · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
    ⟨zChainConnectedIn⟩⟩

/-- **Non-vacuity: a real adjacent-edge spanning tree is built (PROVED).**  For
the genuine internal animal `[0,1]` on `zChain`, `adjSpanningTreeInternal`
produces a tree satisfying every conjunct of the `AdjSpanningTree` body — so the
internal builder is not vacuous. -/
theorem zChain_adjSpanning_witness :
    ∃ t : RTree zChain,
      RTree.root t = (0 : Nat) ∧
      (RTree.nodes t).length = 2 ∧
      sameSupport ([(0 : Nat), (1 : Nat)] : Polymer zChain.toLattice) (RTree.nodes t) ∧
      (RTree.nodes t).Nodup ∧
      Nonempty (AdjacentEdges t) :=
  adjSpanningTreeInternal zChain (0 : Nat) 2 _ zChainIsClusterIn

#print axioms adjSpanningTree_unconditional
#print axioms clusterCountBound_animal
#print axioms internalConnRefines
#print axioms boundaryCrossing
#print axioms insertUnder_mem
#print axioms insertUnder_adj
#print axioms insertUnder_nodup
#print axioms nodup_subset_length_le
#print axioms growStep
#print axioms grow
#print axioms zChainConnectedIn
#print axioms zChain_adjSpanning_witness

end YMGap.Continuum.AdjSpanningBuild
