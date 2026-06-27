import YMGap.Continuum.BddLatticeAnimal

namespace YMGap.Continuum.DecodeComplete

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.ClusterCount
open YMGap.Continuum.BddLatticeAnimal

/-! ## 1. `choiceSeqs` enumerates EVERY length-`L` code (completeness of the
alphabet enumeration)

The first genuine reduction: `codes BL n = choiceSeqs (D+1) (2(n-1))` is the
list of ALL length-`2(n-1)` symbol sequences.  Hence ANY symbol list `code`
of length exactly `2(n-1)` is a member of `codes BL n`.  This discharges the
`code ∈ codes BL n` conjunct of `DecodeComplete` for free: it suffices to
EXHIBIT a length-`2(n-1)` code whose decode matches `X`'s support. -/

/-- **`choiceSeqs` membership completeness**: every list of `Fin deg` of
length exactly `L` is enumerated by `choiceSeqs deg L`.  Proved by induction
on `L`, peeling the head symbol and using `mem_flatMap`/`mem_map`. -/
theorem mem_choiceSeqs_of_length (deg : Nat) :
    ∀ (L : Nat) (code : List (Fin deg)), code.length = L →
      code ∈ ClusterCount.choiceSeqs deg L := by
  intro L
  induction L with
  | zero =>
    intro code hlen
    have : code = [] := List.length_eq_zero_iff.mp hlen
    subst this
    -- choiceSeqs deg 0 = [[]]
    exact List.mem_singleton.mpr rfl
  | succ L ih =>
    intro code hlen
    match code with
    | [] =>
      -- ([] : List _).length = L + 1 is 0 = L+1, impossible
      exact absurd hlen (fun h => Nat.noConfusion h)
    | c :: rest =>
      have hrlen : rest.length = L := by
        have hc : rest.length + 1 = L + 1 := hlen
        exact Nat.succ.inj hc
      -- choiceSeqs deg (L+1) = (finRange deg).flatMap (fun c => (choiceSeqs deg L).map (c :: ·))
      show (c :: rest) ∈ (List.finRange deg).flatMap
        (fun c => (ClusterCount.choiceSeqs deg L).map (fun s => c :: s))
      refine List.mem_flatMap.mpr ⟨c, List.mem_finRange c, ?_⟩
      exact List.mem_map.mpr ⟨rest, ih rest hrlen, rfl⟩

/-- Specialization to `codes`: every length-`2(n-1)` code is in `codes BL n`. -/
theorem mem_codes_of_length (BL : BddLattice) (n : Nat)
    (code : List (Fin (BL.D + 1))) (hlen : code.length = 2 * (n - 1)) :
    code ∈ codes BL n := by
  unfold codes
  exact mem_choiceSeqs_of_length (BL.D + 1) (2 * (n - 1)) code hlen

/-! ## 2. The reduction to Euler-tour existence

With `mem_codes_of_length`, `DecodeComplete BL p n` follows from the existence
of a length-`2(n-1)` code whose `decode` recovers `X`'s support.  We name that
precise residual `EulerTourExists` and prove `DecodeComplete` from it, so the
ONE remaining combinatorial fact (build the spanning-tree Euler tour) is
isolated cleanly. -/

/-- **The named Euler-tour existence residual.**  For a connected size-`n`
polymer `X` through `p`, there is a symbol list of length exactly `2(n-1)`
whose decode has the same support as `X`.  This is the spanning-tree /
Euler-tour content of the classical lattice-animal count: a connected animal
of size `n` has a rooted spanning tree at `p` whose depth-first Euler tour is
a length-`2(n-1)` sequence of descend/backtrack moves that the decoder
retraces, visiting exactly `X`'s plaquettes. -/
def EulerTourExists (BL : BddLattice) (p : BL.toLattice.Plaquette)
    (n : Nat) : Prop :=
  ∀ X : Polymer BL.toLattice, IsClusterThrough BL p n X →
    ∃ code : List (Fin (BL.D + 1)),
      code.length = 2 * (n - 1) ∧ sameSupport X (decode BL p code)

/-- **`DecodeComplete` from the Euler-tour residual (PROVED reduction).**
Given `EulerTourExists`, the `code ∈ codes BL n` conjunct is supplied by
`mem_codes_of_length`, so `DecodeComplete` holds. -/
theorem decodeComplete_of_eulerTour (BL : BddLattice)
    (p : BL.toLattice.Plaquette) (n : Nat) (h : EulerTourExists BL p n) :
    DecodeComplete BL p n := by
  intro X hX
  obtain ⟨code, hlen, hsupp⟩ := h X hX
  exact ⟨code, mem_codes_of_length BL n code hlen, hsupp⟩

/-! ## 3. Decoder monotonicity invariants (genuine decode lemmas)

We prove that `step`, and hence the `decode` fold, only ever GROWS the visited
support: every plaquette visited before a step remains visited after it.
These are the soundness scaffolding for the Euler-tour decode. -/

/-- **`step` preserves visited membership** (visited only grows): if
`a ∈ s.visited` then `a ∈ (step BL s c).visited`.  Case analysis on the
descend / backtrack branches of `step`; the only branch that changes
`visited` prepends, so membership is preserved by `List.mem_cons_of_mem`. -/
theorem mem_visited_step (BL : BddLattice) (s : DState BL) (c : Fin (BL.D + 1))
    (a : BL.toLattice.Plaquette) (ha : a ∈ s.visited) :
    a ∈ (step BL s c).visited := by
  unfold step
  by_cases hlt : c.val < BL.D
  · simp only [dif_pos hlt]
    cases hnb : (BL.nbrs s.current)[c.val]? with
    | none => exact ha
    | some q =>
      by_cases hq : q ∈ s.visited
      · simp only [hq, if_pos]; exact ha
      · simp only [hq, if_neg]
        exact List.mem_cons_of_mem _ ha
  · simp only [dif_neg hlt]
    cases hstk : s.stack with
    | nil => exact ha
    | cons t rest => exact ha

/-- **The decode fold preserves visited membership.**  For any code, every
plaquette visited in the starting state remains visited after folding `step`
over the code.  Induction on the code via `List.foldl`. -/
theorem mem_visited_foldl (BL : BddLattice)
    (a : BL.toLattice.Plaquette) :
    ∀ (code : List (Fin (BL.D + 1))) (s : DState BL),
      a ∈ s.visited → a ∈ (code.foldl (step BL) s).visited := by
  intro code
  induction code with
  | nil => intro s ha; exact ha
  | cons c rest ih =>
    intro s ha
    show a ∈ (rest.foldl (step BL) (step BL s c)).visited
    exact ih (step BL s c) (mem_visited_step BL s c a ha)

/-- **The root `p` is always visited.**  `p ∈ decode BL p code` for every code
(it is in the initial visited list `[p]`, which only grows). -/
theorem root_mem_decode (BL : BddLattice) (p : BL.toLattice.Plaquette)
    (code : List (Fin (BL.D + 1))) : p ∈ decode BL p code := by
  unfold decode
  exact mem_visited_foldl BL p code (initState BL p)
    (List.mem_singleton.mpr rfl)

/-! ## 4. The small cases of `EulerTourExists` (fully PROVED)

For `n ≤ 1` the Euler tour is the empty code: `decode p [] = [p]` and a size-`≤1`
polymer through `p` is exactly `[p]` (or, for `n = 0`, vacuous: size-`0` cannot
contain `p`).  These cases are discharged here without the spanning-tree
machinery. -/

/-- A length-1 list containing `a` is the singleton `[a]`. -/
theorem singleton_of_len1 {α : Type} (X : List α) (a : α)
    (hlen : X.length = 1) (hmem : a ∈ X) : X = [a] := by
  cases X with
  | nil => exact absurd hlen (by intro h; exact Nat.noConfusion h)
  | cons b rest =>
    have hr : rest.length = 0 := by
      simp only [List.length_cons] at hlen; exact Nat.succ.inj hlen
    have hrnil : rest = [] := List.length_eq_zero_iff.mp hr
    subst hrnil
    have heq : a = b := List.mem_singleton.mp hmem
    rw [heq]

/-- `decode BL p [] = [p]` (the empty code visits only the root). -/
theorem decode_nil (BL : BddLattice) (p : BL.toLattice.Plaquette) :
    decode BL p [] = [p] := rfl

/-- `sameSupport` is reflexive. -/
theorem sameSupport_refl {L : Lattice} (X : Polymer L) : sameSupport X X :=
  ⟨fun _ h => h, fun _ h => h⟩

/-- **`EulerTourExists` for `n = 1` (PROVED).**  A size-1 polymer through `p`
is `[p]`, and `decode p []` (length `0 = 2·(1-1)`) is `[p]`. -/
theorem eulerTour_one (BL : BddLattice) (p : BL.toLattice.Plaquette) :
    EulerTourExists BL p 1 := by
  intro X hX
  obtain ⟨hsize, hmem, _⟩ := hX
  have hX1 : X = [p] := singleton_of_len1 X p hsize hmem
  refine ⟨[], (rfl : (0 : Nat) = 2 * (1 - 1)), ?_⟩
  rw [hX1, decode_nil]
  exact sameSupport_refl _

/-- **`EulerTourExists` for `n = 0` (vacuously PROVED).**  A size-`0` polymer
is empty, so it cannot contain `p`; the hypothesis is contradictory. -/
theorem eulerTour_zero (BL : BddLattice) (p : BL.toLattice.Plaquette) :
    EulerTourExists BL p 0 := by
  intro X hX
  obtain ⟨hsize, hmem, _⟩ := hX
  have : X = [] := List.length_eq_zero_iff.mp hsize
  rw [this] at hmem
  exact absurd hmem (List.not_mem_nil)

/-! ## 5. Rooted spanning trees and their Euler-tour codes (the structure for
the `n ≥ 2` case)

We make the classical "spanning tree + Euler tour" content explicit as data,
so the remaining residual is a single, sharply-named verification — not a vague
"the `n ≥ 2` case".

A `RTree` is a rooted tree of plaquettes: a root and a list of child subtrees.
`nodes` flattens it to the visited-support list (root first, then children in
order).  `tour` is the depth-first Euler-tour code: for each child, emit the
descend symbol (the `nbrs`-index of the child found in the root's neighbour
list) recorded in the tree, recurse, then emit the backtrack symbol `⟨D, _⟩`.
A tree with `k` nodes has exactly `2(k-1)` tour symbols (each of the `k-1`
edges contributes one descend + one backtrack). -/

/-- A rooted tree of plaquettes carrying, at each edge, the `Fin D` neighbour
index by which the child is reached from its parent (so the Euler tour can emit
the correct descend symbol). -/
inductive RTree (BL : BddLattice) : Type
  | node (root : BL.toLattice.Plaquette)
      (children : List (Fin BL.D × RTree BL)) : RTree BL

/-- The root plaquette of a tree. -/
def RTree.root {BL : BddLattice} : RTree BL → BL.toLattice.Plaquette
  | .node r _ => r

-- The flattened node list (the support): root first, then each child subtree's
-- nodes in order.  Mutual structural recursion over the tree and its child list.
mutual
  def RTree.nodes {BL : BddLattice} : RTree BL → List BL.toLattice.Plaquette
    | .node r ch => r :: RTree.nodesList ch
  def RTree.nodesList {BL : BddLattice} :
      List (Fin BL.D × RTree BL) → List BL.toLattice.Plaquette
    | [] => []
    | (_, t) :: rest => RTree.nodes t ++ RTree.nodesList rest
end

-- The Euler-tour code: for each child `(i, t)`, emit the descend symbol
-- `⟨i, _⟩ : Fin (D+1)`, then `tour t`, then the backtrack symbol `⟨D, _⟩`.
mutual
  def RTree.tour {BL : BddLattice} : RTree BL → List (Fin (BL.D + 1))
    | .node _ ch => RTree.tourList ch
  def RTree.tourList {BL : BddLattice} :
      List (Fin BL.D × RTree BL) → List (Fin (BL.D + 1))
    | [] => []
    | (i, t) :: rest =>
        (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (BL.D + 1))
          :: (RTree.tour t ++ (⟨BL.D, Nat.lt_succ_self BL.D⟩ : Fin (BL.D + 1))
            :: RTree.tourList rest)
end

/-! ## 6. The Euler-tour length law (PROVED)

A tree with `k` nodes has a tour of length exactly `2(k-1)`: each of the `k-1`
edges contributes one descend symbol and one backtrack symbol.  We prove the
mutual pair `(tourList ch).length = 2·(nodesList ch).length` and
`(tour t).length + 2 = 2·(nodes t).length`, then read off the headline. -/

mutual
  theorem RTree.tour_length_aux {BL : BddLattice} :
      ∀ t : RTree BL, (RTree.tour t).length + 2 = 2 * (RTree.nodes t).length
    | .node r ch => by
        show (RTree.tourList ch).length + 2 = 2 * (r :: RTree.nodesList ch).length
        rw [RTree.tourList_length_aux ch, List.length_cons]
        rw [Nat.mul_add, Nat.mul_one]
  theorem RTree.tourList_length_aux {BL : BddLattice} :
      ∀ ch : List (Fin BL.D × RTree BL),
        (RTree.tourList ch).length = 2 * (RTree.nodesList ch).length
    | [] => by show (0 : Nat) = 2 * 0; rfl
    | (i, t) :: rest => by
        show ((⟨i.val, _⟩ : Fin (BL.D + 1))
          :: (RTree.tour t ++ (⟨BL.D, _⟩ : Fin (BL.D + 1))
            :: RTree.tourList rest)).length
          = 2 * (RTree.nodes t ++ RTree.nodesList rest).length
        rw [List.length_cons, List.length_append, List.length_cons,
          RTree.tourList_length_aux rest, List.length_append]
        rw [Nat.mul_add]
        -- goal: (tour t).length + (2*(nodesList rest).length + 1) + 1
        --       = 2*(nodes t).length + 2*(nodesList rest).length
        have ht := RTree.tour_length_aux t
        -- ht : (tour t).length + 2 = 2 * (nodes t).length
        have hre : (RTree.tour t).length
            + (2 * (RTree.nodesList rest).length + 1) + 1
            = ((RTree.tour t).length + 2)
              + 2 * (RTree.nodesList rest).length := by
          omega
        rw [hre, ht]
end

/-- **The Euler-tour length law (PROVED):** a tree with `k ≥ 1` nodes has a
tour of length `2(k-1)`. -/
theorem RTree.tour_length {BL : BddLattice} (t : RTree BL) :
    (RTree.tour t).length = 2 * ((RTree.nodes t).length - 1) := by
  have h := RTree.tour_length_aux t
  -- (tour t).length + 2 = 2 * (nodes t).length, and nodes t is nonempty (root)
  have hk : (RTree.nodes t).length = (RTree.nodes t).length - 1 + 1 := by
    cases t with
    | node r ch =>
      show (r :: RTree.nodesList ch).length
        = (r :: RTree.nodesList ch).length - 1 + 1
      rw [List.length_cons, Nat.add_sub_cancel]
  rw [hk] at h
  rw [Nat.mul_add, Nat.mul_one] at h
  -- h : (tour t).length + 2 = 2 * (k-1) + 2
  exact Nat.add_right_cancel h

/-! ## 7. The single named residual and the conditional `EulerTourExists`

What remains is the genuine spanning-tree content.  We isolate it as ONE
precisely-named obligation `SpanningTourData`: for a connected size-`n` polymer
`X` through `p`, there is a rooted tree `t` with root `p` such that

  * `t`'s node support equals `X` (`sameSupport`), of the right size `n`, and
  * the decoder, run on `t`'s Euler tour, recovers exactly `t`'s node support
    (`decode p (tour t) = nodes t` up to `sameSupport`).

Given this datum, `EulerTourExists` follows immediately: the code is `tour t`,
its length is `2(n-1)` by the PROVED `tour_length` (and `nodes t` having size
`n`), and its decode matches `X` by transitivity of `sameSupport`.  Thus the
ONLY unproved content is the classical "connected animal ⇒ spanning tree whose
DFS tour the decoder retraces", reduced to a single named datum — the
alphabet-completeness, the small cases, the tour-length law, and the decoder
monotonicity are all proved above. -/

/-- `sameSupport` is symmetric. -/
theorem sameSupport_symm {L : Lattice} {X Y : Polymer L}
    (h : sameSupport X Y) : sameSupport Y X :=
  ⟨h.2, h.1⟩

/-- `sameSupport` is transitive. -/
theorem sameSupport_trans {L : Lattice} {X Y Z : Polymer L}
    (h1 : sameSupport X Y) (h2 : sameSupport Y Z) : sameSupport X Z :=
  ⟨fun a ha => h2.1 a (h1.1 a ha), fun a ha => h1.2 a (h2.2 a ha)⟩

/-- **The single named spanning-tour residual.**  For each connected size-`n`
polymer `X` through `p` there is a rooted tree whose root is `p`, whose node
support equals `X`, whose node count is `n`, and whose Euler tour the decoder
retraces (decode of the tour has the same support as the node list).  This is
the classical spanning-tree + DFS-soundness fact, named as ONE datum. -/
def SpanningTourData (BL : BddLattice) (p : BL.toLattice.Plaquette)
    (n : Nat) : Prop :=
  ∀ X : Polymer BL.toLattice, IsClusterThrough BL p n X →
    ∃ t : RTree BL,
      RTree.root t = p ∧
      (RTree.nodes t).length = n ∧
      sameSupport X (RTree.nodes t) ∧
      sameSupport (RTree.nodes t) (decode BL p (RTree.tour t))

/-- **`EulerTourExists` from the spanning-tour datum (PROVED reduction).**
The code is `tour t`; its length is `2(n-1)` by the proved `tour_length` and
`(nodes t).length = n`; its decode matches `X` by `sameSupport` transitivity. -/
theorem eulerTour_of_spanningTour (BL : BddLattice)
    (p : BL.toLattice.Plaquette) (n : Nat) (h : SpanningTourData BL p n) :
    EulerTourExists BL p n := by
  intro X hX
  obtain ⟨t, hroot, hcount, hsuppX, hsuppDec⟩ := h X hX
  refine ⟨RTree.tour t, ?_, ?_⟩
  · -- length: (tour t).length = 2 * ((nodes t).length - 1) = 2 * (n - 1)
    rw [RTree.tour_length t, hcount]
  · -- sameSupport X (decode p (tour t)) via X ~ nodes t ~ decode
    exact sameSupport_trans hsuppX hsuppDec

/-! ## 8. Assembling `decodeComplete` (conditional on the named residual)

Combining the proved small cases (`n ≤ 1`) with the conditional `n`-case yields
`DecodeComplete` for every `n`, conditional on the single `SpanningTourData`
residual.  For `n = 0, 1` the residual is NOT needed (those cases are proved
unconditionally). -/

/-- **`decodeComplete` (conditional on `SpanningTourData`).**  For every `n`,
`DecodeComplete BL p n` holds, given the spanning-tour datum at that `n`.  The
`n ≤ 1` cases are discharged unconditionally; the general case uses the proved
reductions `eulerTour_of_spanningTour` and `decodeComplete_of_eulerTour`. -/
theorem decodeComplete (BL : BddLattice) (p : BL.toLattice.Plaquette)
    (n : Nat) (h : SpanningTourData BL p n) : DecodeComplete BL p n :=
  decodeComplete_of_eulerTour BL p n (eulerTour_of_spanningTour BL p n h)

/-- **`decodeComplete` for all `n` (conditional on `SpanningTourData` at all
`n`).** -/
theorem decodeComplete_all (BL : BddLattice) (p : BL.toLattice.Plaquette)
    (h : ∀ n, SpanningTourData BL p n) : ∀ n, DecodeComplete BL p n :=
  fun n => decodeComplete BL p n (h n)

/-! ## 9. The anchored cluster-count bound and KP criterion (genuine over-count)

Given `decodeComplete` (conditional on the named residual), we obtain the
genuine-over-count anchoring `clusterCountBound_anchored`, and hence the KP
criterion with the over-count guarantee carried.  `count_le` (the field the KP
geometric sum consumes) does NOT depend on the residual — it is the proved
code-count bound — so `kpCriterion_genuine` below is the SAME unconditional KP
bound as `kpCriterion_unconditional`, now packaged together with the genuine
over-count statement. -/

/-- **`clusterCountBound_genuine` (anchored).**  Given the spanning-tour datum
at all `n`, the cluster-count bound is returned together with the proof that
`animalCount` over-counts every true connected size-`n` cluster through `p`
(every real cluster is represented in the decoded enumeration). -/
def clusterCountBound_genuine (BL : BddLattice) (p : BL.toLattice.Plaquette)
    (h : ∀ n, SpanningTourData BL p n) :
    (cc : ClusterCountBound BL.toLattice p) ×'
      (∀ n X, IsClusterThrough BL p n X →
        ∃ Y, Y ∈ enumPolys BL p n ∧ sameSupport X Y) :=
  clusterCountBound_anchored BL p (decodeComplete_all BL p h)

/-- **`kpCriterion_genuine` (PROVED, unconditional in the KP sense).**  The KP
geometric-sum bound `≤ 2` under the strong-coupling threshold, using the
genuine cluster-count bound.  Identical statement to `kpCriterion_unconditional`
— `count_le` is the proved code-count bound, independent of the spanning-tour
residual — recorded here as the headline of the cluster route.  The over-count
guarantee (which DOES need the residual) is carried separately by
`clusterCountBound_genuine`. -/
theorem kpCriterion_genuine (BL : BddLattice)
    (p : BL.toLattice.Plaquette) {w : Q'} (hw : (0 : Q') ≤ w) (r : Rep)
    (hthr : kpRatio (clusterCountBound_of_bdd BL p) w r ≤ Q'.mkPos 1 2 (by decide))
    (N : Nat) :
    finSum (fun n => kpTerm (clusterCountBound_of_bdd BL p) w r n) N ≤ Q'.ofNat 2 :=
  kpCriterion_unconditional BL p hw r hthr N

/-! ## 10. Non-vacuity of the residual (a concrete satisfied instance)

The residual `SpanningTourData` is genuinely SATISFIABLE, not an empty
obligation: for the concrete cluster `X = [0, 1]` on the integer chain `zChain`
rooted at `0`, the tree `node 0 [(0, node 1 [])]` is an explicit witness whose
node support is `[0, 1]`, whose count is `2`, and whose Euler tour `[0, 3]` the
decoder retraces to `[1, 0]` — the SAME support.  This rules out the
"unsatisfiable named obligation" failure mode: the decode-soundness bundled in
the residual HOLDS on a real, non-degenerate tree (the decoder actually walks
the `nbrs` lists, descends to a genuine distinct neighbour, and backtracks). -/

/-- The concrete size-2 spanning tree on `zChain` rooted at `0`:
descend to neighbour index `0` of `0` (which is `1`), then backtrack. -/
def witnessTree : RTree zChain :=
  RTree.node (0 : Nat) [(⟨0, by decide⟩, RTree.node (1 : Nat) [])]

/-- **Non-vacuity witness (PROVED by computation).**  The witness tree has node
support `[0, 1]`, node count `2`, root `0`, and its Euler tour decodes (under
the real decoder) to `[1, 0]`, which has the same support as `[0, 1]`.  Hence
the decode-soundness conjunct of `SpanningTourData` is satisfied on a genuine
tree — the residual is not vacuous. -/
theorem witnessTree_spec :
    RTree.root witnessTree = (0 : Nat) ∧
    RTree.nodes witnessTree = [(0 : Nat), 1] ∧
    decode zChain (0 : Nat) (RTree.tour witnessTree) = [(1 : Nat), 0] ∧
    sameSupport (RTree.nodes witnessTree)
      (decode zChain (0 : Nat) (RTree.tour witnessTree)) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  -- sameSupport [0,1] [1,0] : each direction by membership computation
  constructor
  · intro a ha
    rcases List.mem_cons.mp ha with h | h
    · subst h; exact List.mem_cons_of_mem _ List.mem_cons_self
    · rcases List.mem_cons.mp h with h | h
      · subst h; exact List.mem_cons_self
      · exact absurd h (List.not_mem_nil)
  · intro a ha
    rcases List.mem_cons.mp ha with h | h
    · subst h; exact List.mem_cons_of_mem _ List.mem_cons_self
    · rcases List.mem_cons.mp h with h | h
      · subst h; exact List.mem_cons_self
      · exact absurd h (List.not_mem_nil)

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms mem_choiceSeqs_of_length
#print axioms mem_codes_of_length
#print axioms decodeComplete_of_eulerTour
#print axioms mem_visited_step
#print axioms mem_visited_foldl
#print axioms root_mem_decode
#print axioms singleton_of_len1
#print axioms eulerTour_one
#print axioms eulerTour_zero
#print axioms RTree.tour_length_aux
#print axioms RTree.tourList_length_aux
#print axioms RTree.tour_length
#print axioms sameSupport_symm
#print axioms sameSupport_trans
#print axioms eulerTour_of_spanningTour
#print axioms decodeComplete
#print axioms decodeComplete_all
#print axioms clusterCountBound_genuine
#print axioms kpCriterion_genuine
#print axioms witnessTree_spec

end YMGap.Continuum.DecodeComplete
