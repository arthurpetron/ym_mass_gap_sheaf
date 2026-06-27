import YMGap.Continuum.DecodeComplete

/-!
# Decoder soundness on rooted-tree Euler tours

This file factors the *general* decoder-soundness conjunct out of the
`DecodeComplete.SpanningTourData` residual.  That residual previously bundled
two unrelated facts:

  1. the **spanning-tree existence** content (a connected size-`n` animal
     through `p` admits a rooted spanning tree at `p` whose node support is the
     animal), and
  2. the **decoder-soundness** content (the decoder, fed that tree's Euler
     tour, retraces exactly the tree's nodes).

(2) is a property of the decoder + the Euler tour *alone*, independent of the
animal `X`.  We prove it here as a standalone lemma `decode_tour_sound` and
re-express the residual so that (2) is discharged automatically, leaving only
(1) — pure spanning-tree existence — as `SpanningTreeExists`.

## Honest scope of `decode_tour_sound`

`decode_tour_sound` is **NOT** unconditionally true for *every* `RTree`.
The `RTree` type (`DecodeComplete.RTree`) carries, at each edge, an arbitrary
`Fin D` index, with **no** constraint that the index actually resolves — via
the lattice neighbour list `BL.nbrs` — to that child's root, and **no**
constraint that the nodes are distinct.  Concretely, on `zChain`
(`nbrs 0 = [1,0]`) the tree `node 0 [(⟨1,_⟩, node 0 [])]` descends with index
`1` to `nbrs 0 [1] = 0`, which is already visited, so the decoder no-ops and
never records the (duplicate) child; and `node 5 [(⟨0,_⟩, node 99 [])]`
descends with index `0` to `nbrs 5 [0] = 4 ≠ 99`, so the decoder visits `4`
rather than `99`.  In both cases a node of the tree is missing from the decode.

The decoder-soundness fact therefore holds exactly for trees that are
**`Faithful`** (every edge index resolves through `BL.nbrs` to that child's
root) and have **distinct nodes** (`(RTree.nodes t).Nodup`).  These are
precisely the structural properties that a genuine DFS spanning tree of a
connected animal enjoys, so folding them into the spanning-tree existence
residual keeps that residual strictly smaller than the original
`SpanningTourData` (it replaces the *runtime* decode-soundness conjunct with
*static* well-formedness conditions on the produced tree).

Everything here is proved by structural / mutual induction matching the real
`step`/`decode`/`tour`/`nodes` semantics; no foldl invariant is hand-waved.
-/

namespace YMGap.Continuum.DecodeTourSound

open YMGap.Continuum.PolymerModel
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.DecodeComplete

/-! ## 1. Well-formedness of an `RTree` for the decoder

`Faithful t` says: at every node, each child edge `(i, t')` satisfies
`BL.nbrs (root) [i.val]? = some (root t')`, and recursively the child is
faithful.  This is exactly the hypothesis `step`'s descend branch needs to
land on the intended child. -/

mutual
  /-- Every edge index of `t` resolves, through `BL.nbrs`, to that child's
  root; recursively faithful. -/
  def Faithful {BL : BddLattice} : RTree BL → Prop
    | .node r ch => FaithfulList r ch
  /-- `FaithfulList r ch`: from parent root `r`, each child `(i, t')` has
  `BL.nbrs r [i.val]? = some (RTree.root t')`, and `t'` is faithful. -/
  def FaithfulList {BL : BddLattice} (r : BL.toLattice.Plaquette) :
      List (Fin BL.D × RTree BL) → Prop
    | [] => True
    | (i, t') :: rest =>
        (BL.nbrs r)[i.val]? = some (RTree.root t') ∧
          Faithful t' ∧ FaithfulList r rest
end

/-! ## 2. The central foldl-accumulation invariant

We prove, by mutual structural induction on the tree and its child list, that
the decoder run on the Euler tour accumulates **exactly** the tree's nodes
(set-wise), while returning `current` and `stack` to their starting values.

For `sameSupport` we only need set-level membership, so the invariant is
phrased with `↔` on membership rather than list equality — this avoids any
order/`reverse` bookkeeping. -/

/-- A descend step on a faithful, fresh child actually moves there.  If
`(BL.nbrs s.current)[i]? = some q` and `q ∉ s.visited`, then the descend step
on symbol `⟨i, _⟩` (`i < D`) yields the state that moved to `q`. -/
theorem step_descend_fresh (BL : BddLattice) (s : DState BL)
    (i : Fin BL.D) (q : BL.toLattice.Plaquette)
    (hnb : (BL.nbrs s.current)[i.val]? = some q) (hfresh : q ∉ s.visited) :
    step BL s ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ =
      { current := q, stack := s.current :: s.stack, visited := q :: s.visited } := by
  unfold step
  have hlt : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (BL.D + 1)).val < BL.D := i.isLt
  simp only [dif_pos hlt]
  show (match h : (BL.nbrs s.current)[i.val]? with
    | none => s
    | some q => if q ∈ s.visited then s
        else { current := q, stack := s.current :: s.stack, visited := q :: s.visited })
    = _
  rw [hnb]
  simp only [hfresh, if_neg, not_false_iff]

/-- A backtrack step (symbol `⟨D, _⟩`) on a nonempty stack pops it. -/
theorem step_backtrack (BL : BddLattice) (s : DState BL)
    (t : BL.toLattice.Plaquette) (rest : List BL.toLattice.Plaquette)
    (hstk : s.stack = t :: rest) :
    step BL s ⟨BL.D, Nat.lt_succ_self BL.D⟩ =
      { current := t, stack := rest, visited := s.visited } := by
  unfold step
  have hlt : ¬ (⟨BL.D, Nat.lt_succ_self BL.D⟩ : Fin (BL.D + 1)).val < BL.D :=
    Nat.lt_irrefl BL.D
  simp only [dif_neg hlt]
  rw [hstk]

/-- `foldl step` over the concatenation `code₁ ++ code₂`. -/
theorem foldl_step_append (BL : BddLattice) (s : DState BL)
    (code₁ code₂ : List (Fin (BL.D + 1))) :
    (code₁ ++ code₂).foldl (step BL) s
      = code₂.foldl (step BL) (code₁.foldl (step BL) s) :=
  List.foldl_append

/-! ### The mutual invariant

`walk_tree`:  on `tour t` from a state at the tree's root with the tree's
*non-root* nodes fresh, the decoder returns `current`/`stack` and grows
`visited` by exactly `nodes t`.

`walk_list`: on `tourList ch` from a state at the parent root `r` (with the
children-subtree nodes fresh and the index list faithful from `r`), the decoder
returns `current = r`/`stack` and grows `visited` by exactly `nodesList ch`. -/

mutual
  theorem walk_tree (BL : BddLattice) :
      ∀ (t : RTree BL) (s : DState BL),
        s.current = RTree.root t →
        s.current ∈ s.visited →
        Faithful t →
        (RTree.nodes t).Nodup →
        (∀ a, a ∈ RTree.nodesList (match t with | .node _ ch => ch) → a ∉ s.visited) →
        ((List.foldl (step BL) s (RTree.tour t)).current = s.current ∧
         (List.foldl (step BL) s (RTree.tour t)).stack = s.stack ∧
         ∀ a, a ∈ (List.foldl (step BL) s (RTree.tour t)).visited ↔
              (a ∈ RTree.nodes t ∨ a ∈ s.visited))
    | .node r ch, s, hcur, hcurvis, hfa, hnd, hfresh => by
        -- tour (node r ch) = tourList ch ; nodes (node r ch) = r :: nodesList ch
        have hfa' : FaithfulList r ch := hfa
        -- r = s.current
        have hr : RTree.root (RTree.node r ch) = r := rfl
        -- Nodup of (r :: nodesList ch) gives nodesList-Nodup and r ∉ nodesList
        have hnd' : (r :: RTree.nodesList ch).Nodup := hnd
        have hndtail : (RTree.nodesList ch).Nodup := (List.nodup_cons.mp hnd').2
        have hrni : r ∉ RTree.nodesList ch := (List.nodup_cons.mp hnd').1
        -- r ∈ s.visited (root is already visited)
        have hrvis : r ∈ s.visited := by rw [hcur] at hcurvis; exact hcurvis
        -- run walk_list
        have key := walk_list BL r ch s (by rw [hcur, hr]) hcurvis hfa' hndtail hfresh
        refine ⟨key.1, key.2.1, ?_⟩
        intro a
        constructor
        · intro hmem
          rcases (key.2.2 a).mp hmem with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inr h
        · intro hmem
          rcases hmem with h | h
          · rcases List.mem_cons.mp h with hh | hh
            · -- a = r ∈ s.visited
              exact (key.2.2 a).mpr (Or.inr (hh ▸ hrvis))
            · exact (key.2.2 a).mpr (Or.inl hh)
          · exact (key.2.2 a).mpr (Or.inr h)

  theorem walk_list (BL : BddLattice) :
      ∀ (r : BL.toLattice.Plaquette) (ch : List (Fin BL.D × RTree BL))
        (s : DState BL),
        s.current = r →
        s.current ∈ s.visited →
        FaithfulList r ch →
        (RTree.nodesList ch).Nodup →
        (∀ a, a ∈ RTree.nodesList ch → a ∉ s.visited) →
        ((List.foldl (step BL) s (RTree.tourList ch)).current = s.current ∧
         (List.foldl (step BL) s (RTree.tourList ch)).stack = s.stack ∧
         ∀ a, a ∈ (List.foldl (step BL) s (RTree.tourList ch)).visited ↔
              (a ∈ RTree.nodesList ch ∨ a ∈ s.visited))
    | r, [], s, _, _, _, _, _ => by
        refine ⟨rfl, rfl, ?_⟩
        intro a; exact ⟨fun h => Or.inr h, fun h => h.elim (fun h => absurd h (List.not_mem_nil)) id⟩
    | r, (i, t') :: rest, s, hcur, hcurvis, hfa, hnd, hfresh => by
        -- decompose faithfulness
        have hnbq : (BL.nbrs r)[i.val]? = some (RTree.root t') := hfa.1
        have hfat' : Faithful t' := hfa.2.1
        have hfarest : FaithfulList r rest := hfa.2.2
        -- nodesList ((i,t')::rest) = nodes t' ++ nodesList rest
        have hndcat : (RTree.nodes t' ++ RTree.nodesList rest).Nodup := hnd
        have hpair := List.nodup_append.mp hndcat
        have hndt' : (RTree.nodes t').Nodup := hpair.1
        have hndrest : (RTree.nodesList rest).Nodup := hpair.2.1
        have hdisj := hpair.2.2  -- ∀ a ∈ nodes t', ∀ b ∈ nodesList rest, a ≠ b
        -- root of t' is fresh w.r.t. s.visited
        have hq : RTree.root t' ∈ RTree.nodes t' := by
          cases t' with
          | node rr cc => exact List.mem_cons_self
        have hqfresh : RTree.root t' ∉ s.visited :=
          hfresh _ (List.mem_append_left _ hq)
        -- tourList ((i,t')::rest)
        --   = descend :: (tour t' ++ backtrack :: tourList rest)
        -- Step 1: descend lands on root t'
        have hnb' : (BL.nbrs s.current)[i.val]? = some (RTree.root t') := by
          rw [hcur]; exact hnbq
        have s1def := step_descend_fresh BL s i (RTree.root t') hnb' hqfresh
        -- abbreviate
        let s1 : DState BL := { current := RTree.root t', stack := s.current :: s.stack, visited := RTree.root t' :: s.visited }
        have hs1 : s1 = { current := RTree.root t', stack := s.current :: s.stack, visited := RTree.root t' :: s.visited } := rfl
        -- Step 2: run tour t' from s1.  Its non-root subtree nodes are fresh
        -- w.r.t. s1.visited (= root t' :: s.visited): fresh w.r.t. s.visited by
        -- hfresh, and ≠ root t' by Nodup of nodes t'.
        have hs1cur : s1.current = RTree.root t' := rfl
        have hfresh1 :
            ∀ a, a ∈ RTree.nodesList (match t' with | .node _ cc => cc) →
              a ∉ s1.visited := by
          intro a ha hain
          -- a is a non-root node of t'
          have hanodes : a ∈ RTree.nodes t' := by
            cases t' with
            | node rr cc =>
                show a ∈ rr :: RTree.nodesList cc
                exact List.mem_cons_of_mem _ ha
          rw [hs1] at hain
          rcases List.mem_cons.mp hain with hh | hh
          · -- a = root t' : contradicts Nodup of nodes t' (root distinct from tail)
            subst hh
            cases t' with
            | node rr cc =>
                have hnotin : RTree.root (RTree.node rr cc) ∉ RTree.nodesList cc :=
                  (List.nodup_cons.mp hndt').1
                exact hnotin ha
          · exact hfresh _ (List.mem_append_left _ hanodes) hh
        have hs1cvis : s1.current ∈ s1.visited := by
          rw [hs1]; exact List.mem_cons_self
        have walk1 := walk_tree BL t' s1 hs1cur hs1cvis hfat' hndt' hfresh1
        -- after tour t', current = root t', stack = s.current :: s.stack,
        -- visited grows by nodes t'
        -- Step 3: backtrack pops, returning current to s.current
        let s2 : DState BL := List.foldl (step BL) s1 (RTree.tour t')
        have hs2 : s2 = List.foldl (step BL) s1 (RTree.tour t') := rfl
        have hs2cur : s2.current = RTree.root t' := walk1.1
        have hs2stk : s2.stack = s.current :: s.stack := walk1.2.1
        have s3def := step_backtrack BL s2 s.current s.stack hs2stk
        let s3 : DState BL := { current := s.current, stack := s.stack, visited := s2.visited }
        have hs3 : s3 = { current := s.current, stack := s.stack, visited := s2.visited } := rfl
        -- Step 4: run tourList rest from s3.  current = r = s.current, stack = s.stack.
        -- nodesList rest fresh w.r.t. s3.visited = s2.visited
        --   = (nodes t' ∪ s.visited) set-wise.
        have hs3cur : s3.current = r := by rw [hs3]; exact hcur
        have hfreshrest :
            ∀ a, a ∈ RTree.nodesList rest → a ∉ s3.visited := by
          intro a ha hain
          rw [hs3] at hain
          -- a ∈ s2.visited ↔ a ∈ nodes t' ∨ a ∈ s.visited
          rcases (walk1.2.2 a).mp hain with h | h
          · -- a ∈ nodes t' and a ∈ nodesList rest : contradicts disjointness
            exact hdisj a h a ha rfl
          · -- a ∈ s1.visited = root t' :: s.visited
            rw [hs1] at h
            rcases List.mem_cons.mp h with hh | hh
            · -- a = root t' ∈ nodes t', but a ∈ nodesList rest : disjointness
              exact hdisj a (by rw [hh]; exact hq) a ha rfl
            · -- a ∈ s.visited, but a ∈ nodesList rest fresh
              have hain' : a ∈ RTree.nodesList ((i, t') :: rest) :=
                List.mem_append_right (RTree.nodes t') ha
              exact hfresh a hain' hh
        have hs3cvis : s3.current ∈ s3.visited := by
          rw [hs3]
          -- s.current ∈ s2.visited via walk1: ∈ s1.visited (= root t' :: s.visited)
          refine (walk1.2.2 s.current).mpr (Or.inr ?_)
          rw [hs1]; exact List.mem_cons_of_mem _ hcurvis
        have walk2 := walk_list BL r rest s3 hs3cur hs3cvis hfarest hndrest hfreshrest
        -- Assemble: the full fold
        -- tourList ((i,t')::rest) = descend :: (tour t' ++ (backtrack :: tourList rest))
        -- foldl over it = foldl (tour t' ++ backtrack :: tourList rest) from s1
        --   = foldl (backtrack :: tourList rest) from s2
        --   = foldl (tourList rest) from s3
        have hunfold :
            List.foldl (step BL) s (RTree.tourList ((i, t') :: rest))
              = List.foldl (step BL) s3 (RTree.tourList rest) := by
          show List.foldl (step BL) s
                ((⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (BL.D + 1))
                  :: (RTree.tour t' ++ (⟨BL.D, Nat.lt_succ_self BL.D⟩ : Fin (BL.D + 1))
                    :: RTree.tourList rest))
              = _
          rw [List.foldl_cons, s1def, ← hs1]
          rw [foldl_step_append, ← hs2]
          rw [List.foldl_cons, s3def, ← hs3]
        rw [hunfold]
        refine ⟨walk2.1, walk2.2.1, ?_⟩
        intro a
        -- membership: a ∈ final ↔ a ∈ nodesList rest ∨ a ∈ s3.visited
        rw [walk2.2.2 a]
        constructor
        · intro h
          rcases h with h | h
          · -- a ∈ nodesList rest → into the right part of the node cat
            exact Or.inl (List.mem_append_right _ h)
          · -- a ∈ s3.visited = s2.visited
            rw [hs3] at h
            rcases (walk1.2.2 a).mp h with h2 | h2
            · exact Or.inl (List.mem_append_left _ h2)
            · -- a ∈ s1.visited = root t' :: s.visited
              rw [hs1] at h2
              rcases List.mem_cons.mp h2 with hh | hh
              · -- a = root t' ∈ nodes t'
                exact Or.inl (List.mem_append_left _ (by rw [hh]; exact hq))
              · exact Or.inr hh
        · intro h
          rcases h with h | h
          · -- a ∈ nodes t' ++ nodesList rest
            rcases List.mem_append.mp h with h2 | h2
            · -- a ∈ nodes t' → a ∈ s2.visited → s3.visited
              refine Or.inr ?_
              rw [hs3]
              exact (walk1.2.2 a).mpr (Or.inl h2)
            · exact Or.inl h2
          · -- a ∈ s.visited → a ∈ s1.visited → s2.visited → s3.visited
            refine Or.inr ?_
            rw [hs3]
            refine (walk1.2.2 a).mpr (Or.inr ?_)
            rw [hs1]; exact List.mem_cons_of_mem _ h
end

/-! ## 3. The headline decoder-soundness lemma

`decode_tour_sound`: for a faithful tree with distinct nodes rooted at `p`, the
decoder fed the tree's Euler tour visits exactly the tree's nodes (up to
`sameSupport`).  This is the general decode-soundness conjunct of
`SpanningTourData`, depending only on the tree's well-formedness — not on any
animal `X`. -/

/-- **Decoder soundness on a well-formed tree's Euler tour (PROVED).**  If `t`
is `Faithful` (every edge index resolves through `BL.nbrs` to that child's
root) and its nodes are distinct (`(RTree.nodes t).Nodup`), then running the
decoder from `RTree.root t` on `t`'s Euler tour recovers exactly `t`'s node
support:

  `sameSupport (RTree.nodes t) (decode BL (RTree.root t) (RTree.tour t))`.

Proved from the mutual foldl-accumulation invariant `walk_tree`. -/
theorem decode_tour_sound (BL : BddLattice) (t : RTree BL)
    (hfa : Faithful t) (hnd : (RTree.nodes t).Nodup) :
    sameSupport (RTree.nodes t) (decode BL (RTree.root t) (RTree.tour t)) := by
  -- decode p (tour t) = (foldl step (initState p) (tour t)).visited
  -- run walk_tree from initState (root t)
  have hcur : (initState BL (RTree.root t)).current = RTree.root t := rfl
  have hcurvis : (initState BL (RTree.root t)).current ∈ (initState BL (RTree.root t)).visited :=
    List.mem_singleton.mpr rfl
  -- freshness: non-root nodes are ≠ root, hence ∉ [root]
  have hfresh :
      ∀ a, a ∈ RTree.nodesList (match t with | .node _ ch => ch) →
        a ∉ (initState BL (RTree.root t)).visited := by
    intro a ha hain
    -- initState.visited = [root t]; so a = root t
    have ha0 : a = RTree.root t := by
      have : a ∈ [RTree.root t] := hain
      exact List.mem_singleton.mp this
    -- but root t ∉ nodesList ch by Nodup of nodes t = root :: nodesList ch
    cases t with
    | node r ch =>
        have hr : RTree.root (RTree.node r ch) = r := rfl
        have hnd' : (r :: RTree.nodesList ch).Nodup := hnd
        have hrni : r ∉ RTree.nodesList ch := (List.nodup_cons.mp hnd').1
        -- a ∈ nodesList ch and a = r
        rw [ha0] at ha
        exact hrni ha
  have key := walk_tree BL t (initState BL (RTree.root t)) hcur hcurvis hfa hnd hfresh
  -- key.2.2 : a ∈ (foldl ...).visited ↔ a ∈ nodes t ∨ a ∈ [root t]
  -- root t ∈ nodes t, so the [root t] disjunct collapses into nodes t
  have hrootmem : RTree.root t ∈ RTree.nodes t := by
    cases t with
    | node r ch => exact List.mem_cons_self
  constructor
  · -- nodes t ⊆ decode
    intro a ha
    show a ∈ (List.foldl (step BL) (initState BL (RTree.root t)) (RTree.tour t)).visited
    exact (key.2.2 a).mpr (Or.inl ha)
  · -- decode ⊆ nodes t
    intro a ha
    have ha' : a ∈ (List.foldl (step BL) (initState BL (RTree.root t)) (RTree.tour t)).visited := ha
    rcases (key.2.2 a).mp ha' with h | h
    · exact h
    · -- a ∈ [root t] → a = root t ∈ nodes t
      have : a = RTree.root t := List.mem_singleton.mp h
      rw [this]; exact hrootmem

#print axioms decode_tour_sound

/-! ## 4. The strictly smaller spanning-tree existence residual

With decoder soundness available as a general fact, the `SpanningTourData`
residual reduces to **spanning-tree existence with well-formedness**: a
connected size-`n` animal `X` through `p` admits a `Faithful` rooted tree at
`p` with distinct nodes whose node support is `X`.  The runtime
decode-soundness conjunct of `SpanningTourData` is now supplied automatically
by `decode_tour_sound`. -/

/-- **The strictly smaller residual: spanning-tree existence (well-formed).**
For each connected size-`n` polymer `X` through `p`, there is a rooted tree
with root `p`, node count `n`, node support `X` (`sameSupport`), that is
`Faithful` and has distinct nodes.  These last two are the *static*
well-formedness conditions a genuine DFS spanning tree of a connected animal
satisfies; together with `decode_tour_sound` they discharge the original
`SpanningTourData`. -/
def SpanningTreeExists (BL : BddLattice) (p : BL.toLattice.Plaquette)
    (n : Nat) : Prop :=
  ∀ X : Polymer BL.toLattice, IsClusterThrough BL p n X →
    ∃ t : RTree BL,
      RTree.root t = p ∧
      (RTree.nodes t).length = n ∧
      sameSupport X (RTree.nodes t) ∧
      Faithful t ∧
      (RTree.nodes t).Nodup

/-- **`SpanningTourData` from `SpanningTreeExists` (PROVED reduction).**  The
first three conjuncts of `SpanningTourData` are carried directly; the fourth
(decode soundness) is supplied by `decode_tour_sound` applied to the produced
`Faithful`, distinct-node tree, with `RTree.root t = p` rewriting the decoder's
root. -/
theorem spanningTourData_of_exists (BL : BddLattice)
    (p : BL.toLattice.Plaquette) (n : Nat)
    (h : SpanningTreeExists BL p n) :
    DecodeComplete.SpanningTourData BL p n := by
  intro X hX
  obtain ⟨t, hroot, hcount, hsuppX, hfa, hnd⟩ := h X hX
  refine ⟨t, hroot, hcount, hsuppX, ?_⟩
  -- decode soundness: sameSupport (nodes t) (decode p (tour t))
  have hsound := decode_tour_sound BL t hfa hnd
  -- decode_tour_sound is at root t; rewrite root t = p
  rw [hroot] at hsound
  exact hsound

#print axioms spanningTourData_of_exists

/-! ## 5. Cluster count anchored on pure spanning-tree existence

Composing with the existing `DecodeComplete` machinery, the genuine
cluster-count bound is now conditional ONLY on `SpanningTreeExists` (pure
well-formed spanning-tree existence) — the decoder-soundness brick has been
discharged. -/

/-- **`DecodeComplete` from `SpanningTreeExists` (PROVED).** -/
theorem decodeComplete_of_exists (BL : BddLattice)
    (p : BL.toLattice.Plaquette) (n : Nat)
    (h : SpanningTreeExists BL p n) :
    DecodeComplete BL p n :=
  DecodeComplete.decodeComplete BL p n (spanningTourData_of_exists BL p n h)

#print axioms decodeComplete_of_exists

/-- **The genuine cluster-count bound, anchored on spanning-tree existence
ONLY (PROVED).**  Given well-formed spanning-tree existence at every `n`, the
cluster-count bound is returned together with the over-count guarantee.  The
decoder-soundness conjunct that previously sat in the residual is now proved
(`decode_tour_sound`); the last genuine combinatorial brick is the pure
spanning-tree existence `SpanningTreeExists`. -/
def clusterCountBound_of_exists (BL : BddLattice)
    (p : BL.toLattice.Plaquette)
    (h : ∀ n, SpanningTreeExists BL p n) :
    (cc : KPCriterion.ClusterCountBound BL.toLattice p) ×'
      (∀ n X, IsClusterThrough BL p n X →
        ∃ Y, Y ∈ enumPolys BL p n ∧ sameSupport X Y) :=
  DecodeComplete.clusterCountBound_genuine BL p
    (fun n => spanningTourData_of_exists BL p n (h n))

#print axioms clusterCountBound_of_exists
#print axioms walk_tree
#print axioms walk_list
#print axioms step_descend_fresh
#print axioms step_backtrack

end YMGap.Continuum.DecodeTourSound
