/-
# Leg (C′) closed: injectivity of the BFS parent-map encoder `parentCode`.

`Continuum/CayleyLooseInjection.lean` reduced the loose Cayley bound
`CayleyLooseBound` to a single named residual: injectivity of the concrete BFS
parent-map encoder `parentCode` on the spanning trees of a simple graph
(`ParentInjSpec`), with `cayleyLooseBound_of_parentInj : ParentInjSpec →
CayleyLooseBound` already PROVED there.  This module discharges the combinatorial
reconstruction that closes `ParentInjSpec` down to ONE genuinely-analytic BFS
input, and derives `ParentInjSpec` / `CayleyLooseBound` from it.

## The reconstruction (the load-bearing combinatorial content — PROVED here)

For a spanning tree `A` of a simple graph on `{0,…,n-1}`, each non-root vertex
`i ∈ (range n).tail` has a BFS parent `parentOf n A i`, and the CANONICAL parent
edge `pedge n A i = (min i p, max i p)` (with `p = parentOf n A i`).  The
`n-1` parent edges are:

  * each IN `A` (the parent is a genuine `A`-neighbour) — the residual clause 1;
  * DISTINCT — because `i` is recoverable from `pedge n A i` as the endpoint of
    strictly LARGER BFS distance (`childEnd`), using residual clause 2
    (`distA (parent) < distA i`).  This is `pedge_injOn` / `parentEdges_nodup`.

So `parentEdges n A` is a `Nodup` list of `n-1` edges contained in `A`, and `A`
itself is a length-`(n-1)` list, whence by the finite pigeonhole
(`subset_of_length_le`, the reverse of the module's `nodup_subset_length_le`)
`A ⊆ parentEdges n A` as well — i.e. `A` and `parentEdges n A` have the SAME edge
set.  Crucially this bypasses acyclicity: the cardinality identity, not a
uniqueness-of-path argument, forces the two edge sets to coincide.

Since `parentEdges n A` depends only on `parentOf n A` (which `parentCode n A`
records), equal codes force `parentEdges n A = parentEdges n B`, hence equal edge
sets, hence `A = B` by `CayleyInjection.spanningTree_eq_of_mem_iff`.  This is
`parentInjSpec_of_recon` (**PROVED**): `ParentReconSpec → ParentInjSpec`.

## The single named residual (`ParentReconSpec`)

`ParentReconSpec` bundles, for every spanning tree `A` of a simple graph and every
non-root vertex `i`:

  (1) `pedge n A i ∈ A`         (the parent edge lies in the tree);
  (2) `distA (parentOf i) < distA i`  (the parent is strictly closer to the root).

Both are the genuine BFS layer/connectivity content: every non-root vertex is
reached by the layered BFS `bfsReach` at some positive finite distance, and it
was added because it has an already-reached neighbour (one BFS layer nearer).
This is the several-hundred-line `bfsReach` sub-project alluded to in the encoder
module's docstring; it is NON-VACUOUS (the triangle's three spanning trees give
the three distinct codes `parentCode_triangle_examples`), TRUE, and strictly
smaller than `ParentInjSpec` (it concerns a SINGLE tree, no two-tree injectivity).
It is carried as a named `Prop` hypothesis per AGENTS.md Rule 6a.

## Honest scope

`parentInjSpec_of_recon` / `cayleyLooseBound_of_recon` are PROVED unconditionally
(they take `ParentReconSpec` as input).  The reconstruction combinatorics — the
real deliverable here — are all axiom-clean and complete.  Whether leg (C′) is
FULLY closed depends on whether `ParentReconSpec` is inhabited below; see the
final section.  Fixed-spacing strong-coupling combinatorics; not the
spacing-uniform continuum modulus; Clay YM mass gap remains OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1/6/8)

Mathlib-free; only `Nat` / `List` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `sorry` / new `axiom`.  Every load-bearing declaration is
gated with `#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.CayleyLooseInjection

namespace YMGap.Continuum.CayleyParentInj

open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.CayleyMaxBound
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyLooseInjection

/-! ## 1. Generic `List` helpers (Mathlib-free) -/

/-- If two maps of the same list agree, the functions agree pointwise on it. -/
theorem map_eq_pointwise {α β : Type _} (f g : α → β) (l : List α)
    (h : l.map f = l.map g) : ∀ x ∈ l, f x = g x := by
  induction l with
  | nil => intro x hx; exact absurd hx List.not_mem_nil
  | cons a l ih =>
      rw [List.map_cons, List.map_cons] at h
      injection h with hhead htail
      intro x hx
      rcases List.mem_cons.mp hx with h1 | h1
      · rw [h1]; exact hhead
      · exact ih htail x h1

/-- If two functions agree pointwise on a list, their maps agree. -/
theorem map_congr_mem {α β : Type _} (f g : α → β) (l : List α)
    (h : ∀ x ∈ l, f x = g x) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.map_cons, List.map_cons, h a List.mem_cons_self,
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- **The reverse finite pigeonhole.**  A `Nodup` list `l` set-embedded in `X`
with `|X| ≤ |l|` has `X ⊆ l` (every member of `X` is a member of `l`).  Proof:
if some `b ∈ X` were missing from `l`, then `l` would embed into `remOne b X`,
which is one shorter, contradicting `nodup_subset_length_le`. -/
theorem subset_of_length_le {γ : Type _} [DecidableEq γ] (l X : List γ)
    (hl : l.Nodup) (hsub : ∀ a ∈ l, a ∈ X) (hlen : X.length ≤ l.length) :
    ∀ b ∈ X, b ∈ l := by
  intro b hb
  by_cases hbl : b ∈ l
  · exact hbl
  · exfalso
    have hsub' : ∀ a ∈ l, a ∈ remOne b X := by
      intro a ha
      have hab : a ≠ b := fun h => hbl (h ▸ ha)
      exact mem_remOne b X a (hsub a ha) hab
    have hle := nodup_subset_length_le l (remOne b X) hl hsub'
    have hrem := remOne_length b X hb
    omega

/-- `range n` is `Nodup` (axiom-clean; the core `List.nodup_range` is classical
in this toolchain, so re-proved here via `range_succ`). -/
theorem range_nodup (n : Nat) : (List.range n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ k ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro x hx b hb heq
      have hbk : b = k := List.mem_singleton.mp hb
      rw [heq, hbk] at hx
      exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl k)

/-- The tail of `range n` is `Nodup` (a sublist of the `Nodup` `range n`). -/
theorem tail_nodup (n : Nat) : ((List.range n).tail).Nodup :=
  (List.tail_sublist (List.range n)).nodup (range_nodup n)

/-! ## 2. The canonical parent edge and its child-endpoint extractor -/

/-- The canonical (orientation `≤`) parent edge of vertex `i`: `(i,p)` if
`i < p`, else `(p,i)`, where `p = parentOf n A i`. -/
def pedge (n : Nat) (A : List Edge) (i : Nat) : Edge :=
  if i < parentOf n A i then (i, parentOf n A i) else (parentOf n A i, i)

/-- The endpoint of an edge with the strictly LARGER BFS distance (the BFS
child).  On a genuine parent edge this recovers the vertex being parented. -/
def childEnd (n : Nat) (A : List Edge) (e : Edge) : Nat :=
  if distA n A e.1 < distA n A e.2 then e.2 else e.1

/-- The list of the `n-1` canonical parent edges (over the non-root vertices). -/
def parentEdges (n : Nat) (A : List Edge) : List Edge :=
  ((List.range n).tail).map (pedge n A)

/-- **`childEnd` recovers the parented vertex.**  If the parent of `i` is
strictly closer to the root, then `i` is the larger-distance endpoint of its
parent edge. -/
theorem childEnd_pedge (n : Nat) (A : List Edge) (i : Nat)
    (hd : distA n A (parentOf n A i) < distA n A i) :
    childEnd n A (pedge n A i) = i := by
  unfold pedge childEnd
  by_cases hlt : i < parentOf n A i
  · rw [if_pos hlt]
    show (if distA n A i < distA n A (parentOf n A i) then parentOf n A i else i) = i
    rw [if_neg (Nat.not_lt.mpr (Nat.le_of_lt hd))]
  · rw [if_neg hlt]
    show (if distA n A (parentOf n A i) < distA n A i then i else parentOf n A i) = i
    rw [if_pos hd]

/-- The parent-edge map is injective on the non-root vertices (given the
strict-distance-decrease clause), via `childEnd`. -/
theorem pedge_injOn (n : Nat) (A : List Edge)
    (hd : ∀ i ∈ (List.range n).tail, distA n A (parentOf n A i) < distA n A i) :
    ∀ i ∈ (List.range n).tail, ∀ i' ∈ (List.range n).tail,
      pedge n A i = pedge n A i' → i = i' := by
  intro i hi i' hi' heq
  have e1 := childEnd_pedge n A i (hd i hi)
  have e2 := childEnd_pedge n A i' (hd i' hi')
  rw [← e1, ← e2, heq]

/-- The parent-edge list is `Nodup` (given the strict-distance-decrease clause). -/
theorem parentEdges_nodup (n : Nat) (A : List Edge)
    (hd : ∀ i ∈ (List.range n).tail, distA n A (parentOf n A i) < distA n A i) :
    (parentEdges n A).Nodup :=
  nodup_map_of_injOn (pedge n A) ((List.range n).tail) (tail_nodup n) (pedge_injOn n A hd)

/-- The parent-edge list has length `n-1`, by construction. -/
theorem parentEdges_length (n : Nat) (A : List Edge) :
    (parentEdges n A).length = n - 1 := by
  unfold parentEdges
  rw [List.length_map, List.length_tail, List.length_range]

/-! ## 3. The named BFS residual -/

/-- **`ParentReconSpec` — the single named BFS residual (Rule 6a).**  For every
spanning tree `A` of a simple graph, every non-root vertex `i`:

  (1) `pedge n A i ∈ A`                — the canonical parent edge lies in `A`;
  (2) `distA (parentOf i) < distA i`   — the parent is strictly closer to root.

Both are the genuine layered-BFS content (every non-root vertex is BFS-reached at
positive finite distance and was added via an already-reached neighbour one layer
nearer).  NON-VACUOUS (`parentCode_triangle_examples`), TRUE, and strictly weaker
than `ParentInjSpec` (single tree, no two-tree injectivity). -/
def ParentReconSpec : Prop :=
  ∀ (n : Nat) (edges : List Edge), SimpleEdges n edges →
    ∀ A ∈ spanningTreeList n edges,
      (∀ i ∈ (List.range n).tail, pedge n A i ∈ A)
      ∧ (∀ i ∈ (List.range n).tail, distA n A (parentOf n A i) < distA n A i)

/-! ## 4. `ParentInjSpec` from the residual -/

/-- For a spanning tree, `A` and `parentEdges n A` have the SAME edge set. -/
theorem mem_iff_parentEdges (n : Nat) (edges : List Edge)
    (A : List Edge) (hA : A ∈ spanningTreeList n edges)
    (hmem : ∀ i ∈ (List.range n).tail, pedge n A i ∈ A)
    (hd : ∀ i ∈ (List.range n).tail, distA n A (parentOf n A i) < distA n A i) :
    ∀ e, e ∈ A ↔ e ∈ parentEdges n A := by
  have hAlen : A.length = n - 1 := by
    have hp := (List.mem_filter.mp hA).2
    have h2 : decide (A.length = n - 1) = true := ((Bool.and_eq_true _ _).mp hp).2
    exact of_decide_eq_true h2
  have hsub : ∀ e ∈ parentEdges n A, e ∈ A := by
    intro e he
    obtain ⟨i, hi, hie⟩ := List.mem_map.mp he
    rw [← hie]; exact hmem i hi
  have hnd : (parentEdges n A).Nodup := parentEdges_nodup n A hd
  have hlen : (parentEdges n A).length = n - 1 := parentEdges_length n A
  have hAsub : ∀ e ∈ A, e ∈ parentEdges n A :=
    subset_of_length_le (parentEdges n A) A hnd hsub (Nat.le_of_eq (by rw [hAlen, hlen]))
  intro e
  exact ⟨fun he => hAsub e he, fun he => hsub e he⟩

/-- **`ParentInjSpec` from the BFS residual (PROVED).**  Equal codes force equal
`parentOf`, hence equal `parentEdges`, hence equal edge sets, hence equal trees
via `spanningTree_eq_of_mem_iff`. -/
theorem parentInjSpec_of_recon (h : ParentReconSpec) : ParentInjSpec := by
  intro n edges hS A hA B hB hcode
  obtain ⟨hmemA, hdA⟩ := h n edges hS A hA
  obtain ⟨hmemB, hdB⟩ := h n edges hS B hB
  have hiffA := mem_iff_parentEdges n edges A hA hmemA hdA
  have hiffB := mem_iff_parentEdges n edges B hB hmemB hdB
  -- parentOf agrees pointwise on the non-root vertices
  have hcode' : ((List.range n).tail).map (parentOf n A)
      = ((List.range n).tail).map (parentOf n B) := hcode
  have hpt : ∀ i ∈ (List.range n).tail, parentOf n A i = parentOf n B i :=
    map_eq_pointwise (parentOf n A) (parentOf n B) ((List.range n).tail) hcode'
  have hpedge : ∀ i ∈ (List.range n).tail, pedge n A i = pedge n B i := by
    intro i hi; unfold pedge; rw [hpt i hi]
  have hPE : parentEdges n A = parentEdges n B :=
    map_congr_mem (pedge n A) (pedge n B) ((List.range n).tail) hpedge
  apply spanningTree_eq_of_mem_iff n edges hS.1 A B hA hB
  intro e
  constructor
  · intro heA
    have h1 : e ∈ parentEdges n A := (hiffA e).mp heA
    rw [hPE] at h1
    exact (hiffB e).mpr h1
  · intro heB
    have h1 : e ∈ parentEdges n B := (hiffB e).mp heB
    rw [← hPE] at h1
    exact (hiffA e).mpr h1

/-- **`CayleyLooseBound` from the BFS residual (PROVED).** -/
theorem cayleyLooseBound_of_recon (h : ParentReconSpec) :
    CayleyLooseReduction.CayleyLooseBound :=
  cayleyLooseBound_of_parentInj (parentInjSpec_of_recon h)

/-! ## 5. Closing the BFS residual: the layered-BFS parent-extraction

This section discharges the layer/ordering half of `ParentReconSpec` in full and
reduces it to the single connectivity fact `BfsReachAll` (every vertex of a
spanning tree is reached by `bfsReach` within `n` layers). -/

/-! ### 5a. `bfsReach` step structure -/

theorem bfsStep_eq (n : Nat) (A : List Edge) (R : List Nat) :
    bfsStep n A R
      = R ++ (List.range n).filter (fun v => decide (v ∉ R) && hasNbrIn A R v) := rfl

/-- One BFS step never drops a vertex. -/
theorem mem_bfsStep_of_mem (n : Nat) (A : List Edge) (R : List Nat) (v : Nat)
    (h : v ∈ R) : v ∈ bfsStep n A R := by
  rw [bfsStep_eq]; exact List.mem_append_left _ h

/-- Every vertex in a BFS step was already present or is a new in-range vertex
with an already-reached neighbour. -/
theorem bfsStep_cases (n : Nat) (A : List Edge) (R : List Nat) (v : Nat)
    (h : v ∈ bfsStep n A R) :
    v ∈ R ∨ (v ∈ List.range n ∧ hasNbrIn A R v = true) := by
  rw [bfsStep_eq] at h
  rcases List.mem_append.mp h with hl | hr
  · exact Or.inl hl
  · rcases List.mem_filter.mp hr with ⟨hmem, hpred⟩
    exact Or.inr ⟨hmem, ((Bool.and_eq_true _ _).mp hpred).2⟩

/-- `hasNbrIn` yields an already-reached genuine neighbour. -/
theorem hasNbrIn_elim (A : List Edge) (R : List Nat) (v : Nat)
    (h : hasNbrIn A R v = true) : ∃ w, w ∈ R ∧ isNbr A v w = true := by
  unfold hasNbrIn at h
  rcases List.any_eq_true.mp h with ⟨e, he, hterm⟩
  rcases (Bool.or_eq_true _ _).mp hterm with h1 | h1
  · rcases (Bool.and_eq_true _ _).mp h1 with ⟨he1, he2⟩
    exact ⟨e.2, of_decide_eq_true he2,
      List.any_eq_true.mpr ⟨e, he, (Bool.or_eq_true _ _).mpr (Or.inl
        ((Bool.and_eq_true _ _).mpr ⟨he1, decide_eq_true rfl⟩))⟩⟩
  · rcases (Bool.and_eq_true _ _).mp h1 with ⟨he2, he1⟩
    exact ⟨e.1, of_decide_eq_true he1,
      List.any_eq_true.mpr ⟨e, he, (Bool.or_eq_true _ _).mpr (Or.inr
        ((Bool.and_eq_true _ _).mpr ⟨decide_eq_true rfl, he2⟩))⟩⟩

/-- A neighbour (in a graph with endpoints `< n`) is itself `< n`. -/
theorem isNbr_lt (A : List Edge) (v w n : Nat)
    (hcanon : ∀ e ∈ A, e.1 < e.2 ∧ e.2 < n) (h : isNbr A v w = true) : w < n := by
  unfold isNbr at h
  rcases List.any_eq_true.mp h with ⟨e, he, hterm⟩
  obtain ⟨h1, h2⟩ := hcanon e he
  rcases (Bool.or_eq_true _ _).mp hterm with hc | hc
  · rcases (Bool.and_eq_true _ _).mp hc with ⟨_, hw⟩
    exact (of_decide_eq_true hw) ▸ h2
  · rcases (Bool.and_eq_true _ _).mp hc with ⟨hw, _⟩
    exact (of_decide_eq_true hw) ▸ Nat.lt_trans h1 h2

/-- `isNbr` yields the canonical edge in the (canonically-oriented) tree. -/
theorem isNbr_edge_mem (A : List Edge) (i j : Nat)
    (hcanon : ∀ e ∈ A, e.1 < e.2) (h : isNbr A i j = true) :
    (if i < j then (i, j) else (j, i)) ∈ A := by
  unfold isNbr at h
  rcases List.any_eq_true.mp h with ⟨e, he, hterm⟩
  rcases (Bool.or_eq_true _ _).mp hterm with h1 | h1
  · rcases (Bool.and_eq_true _ _).mp h1 with ⟨he1, he2⟩
    have hi : e.1 = i := of_decide_eq_true he1
    have hj : e.2 = j := of_decide_eq_true he2
    have hlt : i < j := by have hc := hcanon e he; rw [hi, hj] at hc; exact hc
    rw [if_pos hlt, ← (Prod.ext hi hj : e = (i, j))]; exact he
  · rcases (Bool.and_eq_true _ _).mp h1 with ⟨he1, he2⟩
    have hi : e.1 = j := of_decide_eq_true he1
    have hj : e.2 = i := of_decide_eq_true he2
    have hlt : j < i := by have hc := hcanon e he; rw [hi, hj] at hc; exact hc
    rw [if_neg (Nat.not_lt.mpr (Nat.le_of_lt hlt)), ← (Prod.ext hi hj : e = (j, i))]; exact he

/-! ### 5b. `bfsReach` monotonicity and `distA` ordering -/

/-- `bfsReach` is monotone in the layer index. -/
theorem bfsReach_mono (n : Nat) (A : List Edge) :
    ∀ (k m : Nat), k ≤ m → ∀ v, v ∈ bfsReach n A k → v ∈ bfsReach n A m := by
  intro k m
  induction m with
  | zero => intro hle v hv; rw [Nat.le_zero.mp hle] at hv; exact hv
  | succ m ih =>
      intro hle v hv
      rcases Nat.lt_or_eq_of_le hle with hlt | heq
      · exact mem_bfsStep_of_mem n A (bfsReach n A m) v (ih (Nat.le_of_lt_succ hlt) v hv)
      · rw [← heq]; exact hv

/-- Increasing sorted structure of `List.range`. -/
theorem range_pairwise (N : Nat) : (List.range N).Pairwise (· < ·) := by
  induction N with
  | zero => exact List.Pairwise.nil
  | succ k ih =>
      rw [List.range_succ, List.pairwise_append]
      refine ⟨ih, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton.mp hb]; exact List.mem_range.mp ha

/-- `find?` over `List.range` returns the least witness: everything before it
fails the predicate. -/
theorem find?_range_least (N : Nat) (Q : Nat → Bool) (d : Nat)
    (hf : (List.range N).find? Q = some d) : ∀ k, k < d → Q k = false := by
  intro k hk
  obtain ⟨_, as, bs, hsplit, hasfalse⟩ := List.find?_eq_some_iff_append.mp hf
  have hdN : d < N := List.mem_range.mp (List.mem_of_find?_eq_some hf)
  have hkmem : k ∈ List.range N := List.mem_range.mpr (Nat.lt_trans hk hdN)
  have hpw : (List.range N).Pairwise (· < ·) := range_pairwise N
  rw [hsplit] at hkmem
  rw [hsplit, List.pairwise_append] at hpw
  rcases List.mem_append.mp hkmem with hkas | hkd
  · simpa using hasfalse k hkas
  · rcases List.mem_cons.mp hkd with hkeq | hkbs
    · exact absurd hkeq (Nat.ne_of_lt hk)
    · obtain ⟨_, hpwcons, _⟩ := hpw
      exact absurd hk
        (Nat.not_lt.mpr (Nat.le_of_lt ((List.pairwise_cons.mp hpwcons).1 k hkbs)))

/-- If `v` is reached by layer `m ≤ n`, its BFS distance is `≤ m`. -/
theorem dist_le_of_mem (n : Nat) (A : List Edge) (v m : Nat)
    (hm : v ∈ bfsReach n A m) (hmn : m ≤ n) : distA n A v ≤ m := by
  have hQm : (decide (v ∈ bfsReach n A m)) = true := decide_eq_true hm
  show ((List.range (n + 1)).find? (fun k => decide (v ∈ bfsReach n A k))).getD n ≤ m
  cases hf : (List.range (n + 1)).find? (fun k => decide (v ∈ bfsReach n A k)) with
  | none =>
      exfalso
      exact (List.find?_eq_none.mp hf) m (List.mem_range.mpr (Nat.lt_succ_of_le hmn)) hQm
  | some d =>
      simp only [Option.getD_some]
      apply Nat.le_of_not_lt
      intro hmd
      have h2 : decide (v ∈ bfsReach n A m) = false :=
        find?_range_least (n + 1) (fun k => decide (v ∈ bfsReach n A k)) d hf m hmd
      rw [hQm] at h2; exact absurd h2 (by decide)

/-- If `v` is reached by some layer `≤ n`, then `v` is present at layer
`distA n A v`. -/
theorem dist_mem (n : Nat) (A : List Edge) (v m : Nat)
    (hm : v ∈ bfsReach n A m) (hmn : m ≤ n) : v ∈ bfsReach n A (distA n A v) := by
  have hQm : (decide (v ∈ bfsReach n A m)) = true := decide_eq_true hm
  show v ∈ bfsReach n A
    (((List.range (n + 1)).find? (fun k => decide (v ∈ bfsReach n A k))).getD n)
  cases hf : (List.range (n + 1)).find? (fun k => decide (v ∈ bfsReach n A k)) with
  | none =>
      exfalso
      exact (List.find?_eq_none.mp hf) m (List.mem_range.mpr (Nat.lt_succ_of_le hmn)) hQm
  | some d =>
      simp only [Option.getD_some]
      have hd := List.find?_some hf
      exact of_decide_eq_true hd

/-! ### 5c. The layer-parent lemma: a reached non-root vertex has a
strictly-closer neighbour -/

theorem layer_parent (n : Nat) (A : List Edge)
    (hcanon : ∀ e ∈ A, e.1 < e.2 ∧ e.2 < n) :
    ∀ (k : Nat), k ≤ n → ∀ v, v ∈ bfsReach n A k → v ≠ 0 →
      ∃ w, w < n ∧ isNbr A v w = true ∧ distA n A w < distA n A v := by
  intro k
  induction k with
  | zero =>
      intro _ v hv hv0
      exact absurd (List.mem_singleton.mp hv) hv0
  | succ k ih =>
      intro hkn v hv hv0
      have hkn' : k ≤ n := Nat.le_of_succ_le hkn
      by_cases hvk : v ∈ bfsReach n A k
      · exact ih hkn' v hvk hv0
      · rcases bfsStep_cases n A (bfsReach n A k) v hv with hin | ⟨_, hnbr⟩
        · exact absurd hin hvk
        · obtain ⟨w, hwR, hwnbr⟩ := hasNbrIn_elim A (bfsReach n A k) v hnbr
          have hdw : distA n A w ≤ k := dist_le_of_mem n A w k hwR hkn'
          have hwlt : w < n := isNbr_lt A v w n hcanon hwnbr
          have hdv : k < distA n A v := by
            apply Nat.lt_of_not_le
            intro hle
            exact hvk (bfsReach_mono n A (distA n A v) k hle v (dist_mem n A v (k + 1) hv hkn))
          exact ⟨w, hwlt, hwnbr, Nat.lt_of_le_of_lt hdw hdv⟩

/-! ### 5d. From the crux to the two residual clauses -/

/-- Given a strictly-closer in-range neighbour of `i`, the concrete `parentOf`
finds one, so both residual clauses hold for `i`. -/
theorem recon_clauses_of_crux (n : Nat) (A : List Edge) (i : Nat)
    (hcanon : ∀ e ∈ A, e.1 < e.2 ∧ e.2 < n)
    (hcrux : ∃ w, w < n ∧ isNbr A i w = true ∧ distA n A w < distA n A i) :
    pedge n A i ∈ A ∧ distA n A (parentOf n A i) < distA n A i := by
  obtain ⟨w, hwn, hwnbr, hwd⟩ := hcrux
  have hPw : (isNbr A i w && decide (distA n A w < distA n A i)) = true :=
    (Bool.and_eq_true _ _).mpr ⟨hwnbr, decide_eq_true hwd⟩
  cases hf : (List.range n).find?
      (fun j => isNbr A i j && decide (distA n A j < distA n A i)) with
  | none =>
      exact absurd hPw ((List.find?_eq_none.mp hf) w (List.mem_range.mpr hwn))
  | some j0 =>
      have hj0 := List.find?_some hf
      have hpar : parentOf n A i = j0 := by
        show ((List.range n).find?
          (fun j => isNbr A i j && decide (distA n A j < distA n A i))).getD 0 = j0
        rw [hf]; rfl
      obtain ⟨hnbr0, hdist0⟩ := (Bool.and_eq_true _ _).mp hj0
      refine ⟨?_, ?_⟩
      · show pedge n A i ∈ A
        unfold pedge
        rw [hpar]
        exact isNbr_edge_mem A i j0 (fun e he => (hcanon e he).1) hnbr0
      · rw [hpar]; exact of_decide_eq_true hdist0

/-! ### 5e. The connectivity residual and the reduction of `ParentReconSpec` -/

/-- **`BfsReachAll` — the single connectivity residual (Rule 6a).**  Every vertex
of a spanning tree is reached by the layered BFS within `n` layers.  This is the
genuine connectivity content (that `spans`-connectivity, computed by the foldr
`reachClosure`, is matched by the clean layered `bfsReach`).  TRUE and
non-vacuous; strictly the reachability core of `ParentReconSpec` — all of the
layer/ordering content is discharged above. -/
def BfsReachAll : Prop :=
  ∀ (n : Nat) (edges : List Edge), SimpleEdges n edges →
    ∀ A ∈ spanningTreeList n edges, ∀ i, i < n → i ∈ bfsReach n A n

/-- The canonical-orientation facts for the edges of a spanning tree. -/
theorem tree_canon (n : Nat) (edges : List Edge) (hS : SimpleEdges n edges)
    (A : List Edge) (hA : A ∈ spanningTreeList n edges) :
    ∀ e ∈ A, e.1 < e.2 ∧ e.2 < n := by
  intro e he
  have hAsub : A ∈ sublists edges := (List.mem_filter.mp hA).1
  exact hS.2 e (mem_of_mem_sublists edges A hAsub e he)

/-- `(range n).tail` consists of the non-root vertices `1,…,n-1`. -/
theorem mem_tail_range (n i : Nat) (h : i ∈ (List.range n).tail) :
    i ≠ 0 ∧ i < n := by
  have hlt : i < n := List.mem_range.mp (List.mem_of_mem_tail h)
  refine ⟨?_, hlt⟩
  cases n with
  | zero => exact absurd hlt (Nat.not_lt_zero i)
  | succ m =>
      rw [List.range_succ_eq_map, List.tail_cons] at h
      obtain ⟨x, _, hx⟩ := List.mem_map.mp h
      rw [← hx]; exact Nat.succ_ne_zero x

/-- **`ParentReconSpec` from the connectivity residual (PROVED).**  All the
layer/ordering content (`layer_parent`, `recon_clauses_of_crux`) is discharged;
only reachability (`BfsReachAll`) is consumed. -/
theorem parentReconSpec_of_reachAll (h : BfsReachAll) : ParentReconSpec := by
  intro n edges hS A hA
  have hcanon := tree_canon n edges hS A hA
  have hclause : ∀ i ∈ (List.range n).tail,
      pedge n A i ∈ A ∧ distA n A (parentOf n A i) < distA n A i := by
    intro i hi
    obtain ⟨hi0, hin⟩ := mem_tail_range n i hi
    have hreach : i ∈ bfsReach n A n := h n edges hS A hA i hin
    exact recon_clauses_of_crux n A i hcanon
      (layer_parent n A hcanon n (Nat.le_refl n) i hreach hi0)
  exact ⟨fun i hi => (hclause i hi).1, fun i hi => (hclause i hi).2⟩

/-! ## 6. Closing `BfsReachAll`: saturation + the `reachClosure`→`bfsReach` bridge

The layered BFS saturates by layer `n` (only `n` vertices to add), so
`bfsReach n A n` is closed under adjacency; and the foldr `reachClosure` used by
`spans` never escapes any adjacency-closed superset of `{0}`.  Together they force
every `spans`-reachable vertex into `bfsReach n A n`. -/

/-! ### 6a. `bfsReach` is `Nodup`, range-bounded, length-monotone -/

theorem bfsReach_nodup (n : Nat) (A : List Edge) : ∀ k, (bfsReach n A k).Nodup := by
  intro k
  induction k with
  | zero => exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | succ k ih =>
      show (bfsStep n A (bfsReach n A k)).Nodup
      rw [bfsStep_eq]
      refine List.nodup_append.mpr ⟨ih, (List.filter_sublist).nodup (range_nodup n), ?_⟩
      intro a ha b hb heq
      rcases List.mem_filter.mp hb with ⟨_, hpred⟩
      exact (of_decide_eq_true ((Bool.and_eq_true _ _).mp hpred).1) (heq ▸ ha)

theorem bfsReach_sub_range (n : Nat) (A : List Edge) (hn : 0 < n) :
    ∀ k v, v ∈ bfsReach n A k → v ∈ List.range n := by
  intro k
  induction k with
  | zero => intro v hv; rw [List.mem_singleton.mp hv]; exact List.mem_range.mpr hn
  | succ k ih =>
      intro v hv
      rcases bfsStep_cases n A (bfsReach n A k) v hv with hin | ⟨hr, _⟩
      · exact ih v hin
      · exact hr

theorem bfsReach_length_le (n : Nat) (A : List Edge) (hn : 0 < n) (k : Nat) :
    (bfsReach n A k).length ≤ n := by
  have h := nodup_subset_length_le (bfsReach n A k) (List.range n)
    (bfsReach_nodup n A k) (bfsReach_sub_range n A hn k)
  rwa [List.length_range] at h

theorem bfsReach_len_mono (n : Nat) (A : List Edge) (k : Nat) :
    (bfsReach n A k).length ≤ (bfsReach n A (k + 1)).length :=
  nodup_subset_length_le (bfsReach n A k) (bfsReach n A (k + 1)) (bfsReach_nodup n A k)
    (fun v hv => bfsReach_mono n A k (k + 1) (Nat.le_succ k) v hv)

/-! ### 6b. Saturation: `bfsReach n A n = bfsReach n A (n+1)` -/

theorem bfsReach_fix_of_len (n : Nat) (A : List Edge) (k : Nat)
    (h : (bfsReach n A (k + 1)).length = (bfsReach n A k).length) :
    bfsReach n A (k + 1) = bfsReach n A k := by
  show bfsStep n A (bfsReach n A k) = bfsReach n A k
  rw [bfsStep_eq]
  have hlen : (bfsStep n A (bfsReach n A k)).length = (bfsReach n A k).length := h
  rw [bfsStep_eq, List.length_append] at hlen
  have hz : ((List.range n).filter
      (fun v => decide (v ∉ bfsReach n A k) && hasNbrIn A (bfsReach n A k) v)).length = 0 := by
    omega
  rw [List.length_eq_zero_iff.mp hz, List.append_nil]

theorem bfsReach_const (n : Nat) (A : List Edge) (k : Nat)
    (hfix : bfsReach n A (k + 1) = bfsReach n A k) :
    ∀ m, k ≤ m → bfsReach n A m = bfsReach n A k := by
  intro m
  induction m with
  | zero => intro hle; rw [Nat.le_zero.mp hle]
  | succ m ih =>
      intro hle
      rcases Nat.lt_or_eq_of_le hle with hlt | heq
      · have hm := ih (Nat.le_of_lt_succ hlt)
        show bfsStep n A (bfsReach n A m) = bfsReach n A k
        rw [hm]; exact hfix
      · rw [heq]

theorem bfsReach_grow (n : Nat) (A : List Edge) :
    ∀ m, (∀ k, k < m → (bfsReach n A k).length < (bfsReach n A (k + 1)).length) →
      m + 1 ≤ (bfsReach n A m).length := by
  intro m
  induction m with
  | zero => intro _; show 1 ≤ (bfsReach n A 0).length; exact Nat.le_refl 1
  | succ m ih =>
      intro hstrict
      have h1 := ih (fun k hk => hstrict k (Nat.lt_succ_of_lt hk))
      have h2 := hstrict m (Nat.lt_succ_self m)
      omega

/-- Constructive bounded search: a decidable bounded universal that fails has a
concrete counterexample below the bound (no classical `not_forall`). -/
theorem bounded_find (P : Nat → Prop) [DecidablePred P] :
    ∀ N, (¬ ∀ k, k < N → P k) → ∃ k, k < N ∧ ¬ P k := by
  intro N
  induction N with
  | zero => intro h; exact absurd (fun k hk => absurd hk (Nat.not_lt_zero k)) h
  | succ N ih =>
      intro h
      by_cases hPN : P N
      · have hnot : ¬ ∀ k, k < N → P k := by
          intro hall
          exact h (fun k hk => by
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | heq
            · exact hall k hlt
            · rw [heq]; exact hPN)
        obtain ⟨k, hk, hnp⟩ := ih hnot
        exact ⟨k, Nat.lt_succ_of_lt hk, hnp⟩
      · exact ⟨N, Nat.lt_succ_self N, hPN⟩

theorem exists_fix (n : Nat) (A : List Edge) (hn : 0 < n) :
    ∃ k, k ≤ n ∧ bfsReach n A (k + 1) = bfsReach n A k := by
  have hnot : ¬ ∀ k, k < n + 1 →
      (bfsReach n A k).length < (bfsReach n A (k + 1)).length := by
    intro hall
    have hg := bfsReach_grow n A (n + 1) hall
    have hle := bfsReach_length_le n A hn (n + 1)
    omega
  obtain ⟨k, hk, hnp⟩ := bounded_find
    (fun k => (bfsReach n A k).length < (bfsReach n A (k + 1)).length) (n + 1) hnot
  have heq : (bfsReach n A (k + 1)).length = (bfsReach n A k).length :=
    Nat.le_antisymm (Nat.le_of_not_lt hnp) (bfsReach_len_mono n A k)
  exact ⟨k, Nat.le_of_lt_succ hk, bfsReach_fix_of_len n A k heq⟩

theorem saturation (n : Nat) (A : List Edge) (hn : 0 < n) :
    bfsReach n A n = bfsReach n A (n + 1) := by
  obtain ⟨k0, hk0n, hfix⟩ := exists_fix n A hn
  have hc := bfsReach_const n A k0 hfix
  rw [hc n hk0n, hc (n + 1) (Nat.le_succ_of_le hk0n)]

/-! ### 6c. `bfsReach n A n` is adjacency-closed -/

theorem mem_bfsStep_of_nbr (n : Nat) (A : List Edge) (R : List Nat) (e : Edge)
    (hc : e.1 < e.2 ∧ e.2 < n) (heA : e ∈ A) (h1 : e.1 ∈ R) : e.2 ∈ bfsStep n A R := by
  by_cases he2 : e.2 ∈ R
  · exact mem_bfsStep_of_mem n A R e.2 he2
  · rw [bfsStep_eq]
    apply List.mem_append_right
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr hc.2, (Bool.and_eq_true _ _).mpr ⟨decide_eq_true he2, ?_⟩⟩
    unfold hasNbrIn
    exact List.any_eq_true.mpr ⟨e, heA, (Bool.or_eq_true _ _).mpr (Or.inr
      ((Bool.and_eq_true _ _).mpr ⟨decide_eq_true rfl, decide_eq_true h1⟩))⟩

theorem mem_bfsStep_of_nbr' (n : Nat) (A : List Edge) (R : List Nat) (e : Edge)
    (hc : e.1 < e.2 ∧ e.2 < n) (heA : e ∈ A) (h2 : e.2 ∈ R) : e.1 ∈ bfsStep n A R := by
  by_cases he1 : e.1 ∈ R
  · exact mem_bfsStep_of_mem n A R e.1 he1
  · rw [bfsStep_eq]
    apply List.mem_append_right
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr (Nat.lt_trans hc.1 hc.2),
      (Bool.and_eq_true _ _).mpr ⟨decide_eq_true he1, ?_⟩⟩
    unfold hasNbrIn
    exact List.any_eq_true.mpr ⟨e, heA, (Bool.or_eq_true _ _).mpr (Or.inl
      ((Bool.and_eq_true _ _).mpr ⟨decide_eq_true rfl, decide_eq_true h2⟩))⟩

theorem bfsReach_adjClosed (n : Nat) (A : List Edge) (hn : 0 < n)
    (hcanon : ∀ e ∈ A, e.1 < e.2 ∧ e.2 < n) :
    (0 ∈ bfsReach n A n) ∧
    (∀ e ∈ A, (e.1 ∈ bfsReach n A n → e.2 ∈ bfsReach n A n)
            ∧ (e.2 ∈ bfsReach n A n → e.1 ∈ bfsReach n A n)) := by
  refine ⟨bfsReach_mono n A 0 n (Nat.zero_le n) 0 (List.mem_singleton.mpr rfl), ?_⟩
  intro e heA
  refine ⟨fun h1 => ?_, fun h2 => ?_⟩
  · have h : e.2 ∈ bfsReach n A (n + 1) :=
      mem_bfsStep_of_nbr n A (bfsReach n A n) e (hcanon e heA) heA h1
    rw [← saturation n A hn] at h; exact h
  · have h : e.1 ∈ bfsReach n A (n + 1) :=
      mem_bfsStep_of_nbr' n A (bfsReach n A n) e (hcanon e heA) heA h2
    rw [← saturation n A hn] at h; exact h

/-! ### 6d. `reachClosure` never escapes an adjacency-closed superset of `{0}` -/

theorem mem_addV (x : Nat) (R : List Nat) (v : Nat) (h : v ∈ addV x R) :
    v = x ∨ v ∈ R := by
  unfold addV at h
  by_cases hx : x ∈ R
  · rw [if_pos hx] at h; exact Or.inr h
  · rw [if_neg hx] at h
    rcases List.mem_cons.mp h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1

theorem mem_relaxEdge (e : Edge) (R : List Nat) (v : Nat) (h : v ∈ relaxEdge e R) :
    v ∈ R ∨ (v = e.2 ∧ e.1 ∈ R) ∨ (v = e.1 ∧ e.2 ∈ R) := by
  unfold relaxEdge at h
  by_cases h1 : e.1 ∈ R
  · rw [if_pos h1] at h
    rcases mem_addV e.2 R v h with hv | hv
    · exact Or.inr (Or.inl ⟨hv, h1⟩)
    · exact Or.inl hv
  · rw [if_neg h1] at h
    by_cases h2 : e.2 ∈ R
    · rw [if_pos h2] at h
      rcases mem_addV e.1 R v h with hv | hv
      · exact Or.inr (Or.inr ⟨hv, h2⟩)
      · exact Or.inl hv
    · rw [if_neg h2] at h; exact Or.inl h

theorem relaxList_sub (A : List Edge) (T : List Nat)
    (hclosed : ∀ e ∈ A, (e.1 ∈ T → e.2 ∈ T) ∧ (e.2 ∈ T → e.1 ∈ T)) :
    ∀ (as : List Edge), (∀ e ∈ as, e ∈ A) → ∀ (R : List Nat), (∀ v ∈ R, v ∈ T) →
      ∀ v ∈ as.foldr relaxEdge R, v ∈ T := by
  intro as
  induction as with
  | nil => intro _ R hR v hv; exact hR v hv
  | cons e as ih =>
      intro hsub R hR v hv
      have heA : e ∈ A := hsub e List.mem_cons_self
      have hR' : ∀ w ∈ as.foldr relaxEdge R, w ∈ T :=
        ih (fun e' he' => hsub e' (List.mem_cons_of_mem _ he')) R hR
      rw [List.foldr_cons] at hv
      rcases mem_relaxEdge e (as.foldr relaxEdge R) v hv with hv0 | ⟨hveq, h1⟩ | ⟨hveq, h2⟩
      · exact hR' v hv0
      · rw [hveq]; exact (hclosed e heA).1 (hR' e.1 h1)
      · rw [hveq]; exact (hclosed e heA).2 (hR' e.2 h2)

theorem reachClosure_sub (A : List Edge) (T : List Nat)
    (hclosed : ∀ e ∈ A, (e.1 ∈ T → e.2 ∈ T) ∧ (e.2 ∈ T → e.1 ∈ T)) :
    ∀ (k : Nat) (R : List Nat), (∀ v ∈ R, v ∈ T) → ∀ v ∈ reachClosure k A R, v ∈ T := by
  intro k
  induction k with
  | zero => intro R hR v hv; exact hR v hv
  | succ k ih =>
      intro R hR v hv
      have hrelax : ∀ w ∈ relax A R, w ∈ T :=
        fun w hw => relaxList_sub A T hclosed A (fun e he => he) R hR w hw
      exact ih (relax A R) hrelax v hv

/-! ### 6e. The connectivity residual, DISCHARGED -/

/-- **`BfsReachAll` — PROVED.**  Every vertex of a spanning tree is reached by the
layered BFS within `n` layers.  Proof: `spans`-connectivity (`reachClosure`) lands
in any adjacency-closed superset of `{0}`, and `bfsReach n A n` is exactly such a
set (adjacency-closed by saturation). -/
theorem bfsReachAll_holds : BfsReachAll := by
  intro n edges hS A hA i hin
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i) hin
  have hcanon := tree_canon n edges hS A hA
  have hspans : spans n A = true :=
    ((Bool.and_eq_true _ _).mp (List.mem_filter.mp hA).2).1
  have hreach0 : ∀ j, j < n → j ∈ reachClosure n A [0] := of_decide_eq_true hspans
  obtain ⟨h0, hcl⟩ := bfsReach_adjClosed n A hn hcanon
  have hsub : ∀ v ∈ reachClosure n A [0], v ∈ bfsReach n A n :=
    reachClosure_sub A (bfsReach n A n) hcl n [0]
      (fun v hv => by rw [List.mem_singleton.mp hv]; exact h0)
  exact hsub i (hreach0 i hin)

/-! ## 7. Leg (C′) CLOSED -/

/-- **`ParentReconSpec` — PROVED** (all analytic BFS content discharged). -/
theorem parentReconSpec_holds : ParentReconSpec :=
  parentReconSpec_of_reachAll bfsReachAll_holds

/-- **`ParentInjSpec` — PROVED unconditionally.**  Injectivity of the concrete BFS
parent-map encoder on spanning trees of a simple graph. -/
theorem parentInjSpec : CayleyLooseInjection.ParentInjSpec :=
  parentInjSpec_of_recon parentReconSpec_holds

/-- **Leg (C′) CLOSED: `CayleyLooseBound` inhabited unconditionally.** -/
theorem cayleyLooseBound_closed : CayleyLooseReduction.CayleyLooseBound :=
  cayleyLooseBound_of_parentInj parentInjSpec

end YMGap.Continuum.CayleyParentInj

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CayleyParentInj.map_eq_pointwise
#print axioms YMGap.Continuum.CayleyParentInj.map_congr_mem
#print axioms YMGap.Continuum.CayleyParentInj.subset_of_length_le
#print axioms YMGap.Continuum.CayleyParentInj.range_nodup
#print axioms YMGap.Continuum.CayleyParentInj.tail_nodup
#print axioms YMGap.Continuum.CayleyParentInj.childEnd_pedge
#print axioms YMGap.Continuum.CayleyParentInj.pedge_injOn
#print axioms YMGap.Continuum.CayleyParentInj.parentEdges_nodup
#print axioms YMGap.Continuum.CayleyParentInj.mem_iff_parentEdges
#print axioms YMGap.Continuum.CayleyParentInj.parentInjSpec_of_recon
#print axioms YMGap.Continuum.CayleyParentInj.cayleyLooseBound_of_recon
#print axioms YMGap.Continuum.CayleyParentInj.layer_parent
#print axioms YMGap.Continuum.CayleyParentInj.recon_clauses_of_crux
#print axioms YMGap.Continuum.CayleyParentInj.parentReconSpec_of_reachAll
#print axioms YMGap.Continuum.CayleyParentInj.saturation
#print axioms YMGap.Continuum.CayleyParentInj.bfsReach_adjClosed
#print axioms YMGap.Continuum.CayleyParentInj.reachClosure_sub
#print axioms YMGap.Continuum.CayleyParentInj.bfsReachAll_holds
#print axioms YMGap.Continuum.CayleyParentInj.parentReconSpec_holds
#print axioms YMGap.Continuum.CayleyParentInj.parentInjSpec
#print axioms YMGap.Continuum.CayleyParentInj.cayleyLooseBound_closed
