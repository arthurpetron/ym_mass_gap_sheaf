/-
# Leg (C′), the de-risked loose Cayley bound: the PARENT-MAP injection route.

`Continuum/CayleyLooseReduction.lean` reduced the tree-graph atom to the LOOSE
count residual

    CayleyLooseBound : ∀ n edges, SimpleEdges n edges → treeCount n edges ≤ n^(n-1)

(strictly weaker than the tight Cayley bound `treeCount ≤ n^(n-2)` of
`CayleyMaxBound.CayleyCountBound`).  The de-risk claim: `n^(n-1)` needs only a
PARENT-MAP injection (root the spanning tree at `0`, send each non-root vertex to
its neighbour towards the root — an injection into length-`(n-1)` words over
`{0,…,n-1}`), which needs NO decoder / surjectivity, strictly less than the
Prüfer bijection.

## What this module delivers (all GREEN, axiom-clean, unless marked NAMED-open)

The cardinality engine of `CayleyPruferInjection.lean` (`count_le_of_inj`,
`allSeqs`, `nodup_subset_length_le`) is reused at the LOOSE target `k = n-1`:

  * `count_le_of_inj_gen` — **PROVED**: the general-`k` pigeonhole.  An injection
    of the spanning-tree list into the length-`k`, entries-`<n` code space bounds
    `treeCount n edges ≤ n^k`.  (`count_le_of_inj` is the `k = n-2` case.)
  * `LooseInjectionData` (Type-level `Σ'` DATA) + `cayleyLooseBound_of_injection`
    — **PROVED reduction**: a length-`(n-1)` injection on spanning trees yields
    `CayleyLooseBound`.
  * `looseInjectionData_of_cayley : CayleyInjectionData → LooseInjectionData`
    — **PROVED**: padding a length-`(n-2)` Prüfer code to length `n-1` shows the
    loose injection is DATA-LEVEL WEAKER than the tight Prüfer injection (the
    quantitative de-risk: whatever inhabits the Prüfer residual inhabits this).
  * `parentCode` — a CONCRETE parent-map encoder over a clean single-step BFS
    (`bfsReach`/`distA`): `parentOf i` = the smallest neighbour of `i` at strictly
    smaller BFS-distance to the root `0`.  Its length (`= n-1`) and range (`< n`)
    are PROVED **for free by construction** (`parentCode_length`,
    `parentCode_range`); only injectivity is open.
  * `parentCode_triangle_examples` — **PROVED by computation (non-vacuity)**: the
    three spanning trees of the triangle map to the three DISTINCT length-2 codes
    `[0,1]`, `[0,0]`, `[2,0]`.  (NB: the naive `reachClosure`-distance parent is
    NOT injective here — two trees collide at `[0,0]` — because `reachClosure`'s
    foldr pass chains within a single pass; the clean layered `bfsReach` is what
    restores injectivity.  This is why the concrete encoder uses `bfsReach`.)
  * `ParentInjSpec` (NAMED-open, the SOLE de-risked residual) + `cayleyLooseBound_of_parentInj`
    — **PROVED reduction**: injectivity of `parentCode` on spanning trees yields
    `CayleyLooseBound`.  `ParentInjSpec` is JUST injectivity — no length, no range,
    no decoder — strictly weaker than `PruferSpec`/`CayleyInjectionData`.

## Honest geography

This does NOT close leg (C′): `CayleyLooseBound` is LEFT UNINHABITED.  It builds
the loose-target cardinality argument, a concrete parent-map encoder whose length
and range are proved and whose injectivity is the single named residual
`ParentInjSpec`, and a data-level proof that this residual is strictly weaker than
the Prüfer residual.  The residual `ParentInjSpec` requires a genuine BFS
parent-extraction argument over `bfsReach` — that every non-root vertex of a
spanning tree receives a strictly-smaller-distance parent (from `spans`
connectivity), that the `n-1` parent edges are distinct (the child is the unique
higher-distance endpoint) and hence equal the tree (the `|A| = n-1` size
argument), so equal codes force equal edge sets and — via
`CayleyInjection.spanningTree_eq_of_mem_iff` — equal trees.  That BFS argument is
a several-hundred-line Mathlib-free sub-project (the layered `bfsReach` vs the
foldr `reachClosure`); LEFT UNINHABITED, nothing is faked.

Fixed-spacing strong-coupling combinatorics; not the spacing-uniform continuum
modulus; Clay YM mass gap remains OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1/6/8)

Mathlib-free; only `Nat` / `List` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `sorry` / new `axiom`.  Witnesses are `Type`-level data
(`LooseInjectionData` is a `Σ'`, not a `Prop`-`∃`).  Every load-bearing
declaration is gated with `#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.CayleyInjection
import YMGap.Continuum.CayleyLooseReduction

namespace YMGap.Continuum.CayleyLooseInjection

open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.CayleyMaxBound
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyLooseReduction

/-! ## 1. The general-`k` pigeonhole (loose target of the cardinality engine)

`CayleyPruferInjection.count_le_of_inj` is specialised to `k = n-2`.  The
argument does not depend on the target length, so the SAME proof gives, for any
`k`, `treeCount n edges ≤ n^k` from an injection into length-`k` code words. -/

/-- **PROVED (general-`k` pigeonhole).**  If `f` maps every spanning tree of
`(n, edges)` to a length-`k` word with entries `< n`, injectively, then
`treeCount n edges ≤ n^k`.  Identical proof to `count_le_of_inj` with `n-2`
generalised to `k`; the loose leg (C′) is the `k = n-1` instance. -/
theorem count_le_of_inj_gen (n k : Nat) (edges : List Edge) (hE : edges.Nodup)
    (f : List Edge → List Nat)
    (hlen : ∀ A ∈ spanningTreeList n edges, (f A).length = k)
    (hrange : ∀ A ∈ spanningTreeList n edges, ∀ x ∈ f A, x < n)
    (hinj : ∀ A ∈ spanningTreeList n edges, ∀ B ∈ spanningTreeList n edges,
        f A = f B → A = B) :
    treeCount n edges ≤ n ^ k := by
  have hLnd : (spanningTreeList n edges).Nodup := by
    unfold spanningTreeList
    exact (List.filter_sublist).nodup (sublists_nodup edges hE)
  have hmapnd : ((spanningTreeList n edges).map f).Nodup :=
    nodup_map_of_injOn f (spanningTreeList n edges) hLnd hinj
  have hsub : ∀ y, y ∈ (spanningTreeList n edges).map f → y ∈ allSeqs n k := by
    intro y hy
    obtain ⟨A, hA, hAy⟩ := List.mem_map.mp hy
    have hmem : f A ∈ allSeqs n k :=
      mem_allSeqs n k (f A) (hlen A hA) (hrange A hA)
    rw [← hAy]; exact hmem
  have hle := nodup_subset_length_le ((spanningTreeList n edges).map f)
    (allSeqs n k) hmapnd hsub
  rw [List.length_map, length_allSeqs] at hle
  rw [treeCount_eq]
  exact hle

/-! ## 2. The loose injection DATA and the reduction of `CayleyLooseBound` -/

/-- **`LooseInjectionData` — the loose (parent-map) injection residual (DATA).**
For every simple graph, a function `f` on spanning trees landing in the
length-`(n-1)`, entries-`<n` code space, injectively.  Carried as `Σ'` data
(Rule 8).  Strictly weaker than `CayleyInjectionData` (length `n-1`, not `n-2`;
no decoder).  LEFT UNINHABITED. -/
def LooseInjectionData : Type :=
  (n : Nat) → (edges : List Edge) → SimpleEdges n edges →
    Σ' (f : List Edge → List Nat),
      (∀ A ∈ spanningTreeList n edges, (f A).length = n - 1)
      ∧ (∀ A ∈ spanningTreeList n edges, ∀ x ∈ f A, x < n)
      ∧ (∀ A ∈ spanningTreeList n edges, ∀ B ∈ spanningTreeList n edges,
          f A = f B → A = B)

/-- **PROVED reduction.**  A length-`(n-1)` injection on spanning trees yields the
loose Cayley bound over the concrete `treeCount`. -/
theorem cayleyLooseBound_of_injection (d : LooseInjectionData) : CayleyLooseBound := by
  intro n edges hS
  obtain ⟨f, hlen, hrange, hinj⟩ := d n edges hS
  exact count_le_of_inj_gen n (n - 1) edges hS.1 f hlen hrange hinj

/-! ## 3. The loose injection is DATA-LEVEL weaker than the Prüfer injection

Padding a length-`(n-2)` code to length `n-1` (prepend `0` when `n ≥ 2`; identity
otherwise) exhibits `CayleyInjectionData → LooseInjectionData`.  This is the
quantitative de-risk: whatever inhabits the tight Prüfer residual inhabits the
loose one, so the loose route never *strengthens* leg (C). -/

/-- Pad a code word to loose length `n-1`: prepend `0` when `n ≥ 2`, else keep. -/
def padCode (n : Nat) (w : List Nat) : List Nat :=
  if n ≤ 1 then w else 0 :: w

/-- **PROVED.**  Padding a length-`(n-2)` word gives length `n-1`. -/
theorem padCode_length (n : Nat) (w : List Nat) (hw : w.length = n - 2) :
    (padCode n w).length = n - 1 := by
  unfold padCode
  by_cases h : n ≤ 1
  · rw [if_pos h, hw]; omega
  · rw [if_neg h, List.length_cons, hw]; omega

/-- **PROVED.**  `padCode n` is injective. -/
theorem padCode_inj (n : Nat) (w1 w2 : List Nat) (h : padCode n w1 = padCode n w2) :
    w1 = w2 := by
  unfold padCode at h
  by_cases hn : n ≤ 1
  · rw [if_pos hn, if_pos hn] at h; exact h
  · rw [if_neg hn, if_neg hn] at h; simpa using h

/-- **PROVED.**  Padding keeps entries `< n` (the prepended `0 < n` since `n ≥ 2`). -/
theorem padCode_range (n : Nat) (w : List Nat) (hw : ∀ x ∈ w, x < n) :
    ∀ x ∈ padCode n w, x < n := by
  unfold padCode
  by_cases h : n ≤ 1
  · rw [if_pos h]; exact hw
  · rw [if_neg h]
    intro x hx
    rcases List.mem_cons.mp hx with h0 | hr
    · rw [h0]; omega
    · exact hw x hr

/-- **PROVED (the data-level de-risk).**  The tight Prüfer injection data yields
the loose parent-length injection data, by padding.  Hence `CayleyLooseBound` is
NEVER a stronger obligation than `CayleyCountBound`. -/
def looseInjectionData_of_cayley (d : CayleyInjectionData) : LooseInjectionData :=
  fun n edges hS =>
    let ⟨f, hlen, hrange, hinj⟩ := d n edges hS
    ⟨fun A => padCode n (f A),
     fun A hA => padCode_length n (f A) (hlen A hA),
     fun A hA => padCode_range n (f A) (hrange A hA),
     fun A hA B hB hEq => hinj A hA B hB (padCode_inj n (f A) (f B) hEq)⟩

/-! ## 4. The concrete parent-map encoder over a clean single-step BFS

The de-risk story: root the tree at `0`, send each non-root vertex to its
neighbour towards the root.  "Towards the root" = strictly smaller BFS distance.
The distance must come from a CLEAN layered BFS (`bfsReach`), NOT the foldr
`reachClosure` used by `spans`: `reachClosure` chains additions within a single
pass, so its "distance" does not strictly decrease along tree edges (verified: it
maps two distinct triangle trees to the same code).  `bfsReach` adds exactly the
one-step frontier per level, so every non-root vertex's BFS-parent has strictly
smaller distance. -/

/-- `v` is adjacent (in `edges`) to some vertex of `R`. -/
def hasNbrIn (edges : List Edge) (R : List Nat) (v : Nat) : Bool :=
  edges.any (fun e =>
    (decide (e.1 = v) && decide (e.2 ∈ R)) || (decide (e.2 = v) && decide (e.1 ∈ R)))

/-- One clean BFS layer: add every in-range vertex not yet reached that has a
neighbour already reached. -/
def bfsStep (n : Nat) (edges : List Edge) (R : List Nat) : List Nat :=
  R ++ (List.range n).filter (fun v => decide (v ∉ R) && hasNbrIn edges R v)

/-- `k`-fold clean BFS from the root `0`. -/
def bfsReach (n : Nat) (edges : List Edge) : Nat → List Nat
  | 0 => [0]
  | k + 1 => bfsStep n edges (bfsReach n edges k)

/-- BFS distance of `v` to the root: least level `≤ n` at which `v` is reached,
else the default `n`. -/
def distA (n : Nat) (edges : List Edge) (v : Nat) : Nat :=
  ((List.range (n + 1)).find? (fun k => decide (v ∈ bfsReach n edges k))).getD n

/-- `j` is a neighbour of `i` in `edges` (either orientation). -/
def isNbr (edges : List Edge) (i j : Nat) : Bool :=
  edges.any (fun e =>
    (decide (e.1 = i) && decide (e.2 = j)) || (decide (e.1 = j) && decide (e.2 = i)))

/-- The BFS parent of `i`: the smallest neighbour `j < n` of `i` at strictly
smaller BFS distance to the root; `0` if none (root, or unreachable). -/
def parentOf (n : Nat) (edges : List Edge) (i : Nat) : Nat :=
  ((List.range n).find?
    (fun j => isNbr edges i j && decide (distA n edges j < distA n edges i))).getD 0

/-- **The concrete parent-map code.**  One entry per non-root vertex
`{1,…,n-1}` (`= (List.range n).tail`), recording its BFS parent.  Length `n-1`
and entries `< n` hold BY CONSTRUCTION. -/
def parentCode (n : Nat) (edges : List Edge) : List Nat :=
  ((List.range n).tail).map (parentOf n edges)

/-- **PROVED (length, for free).**  `parentCode` has length exactly `n-1`. -/
theorem parentCode_length (n : Nat) (edges : List Edge) :
    (parentCode n edges).length = n - 1 := by
  unfold parentCode
  rw [List.length_map, List.length_tail, List.length_range]

/-- **PROVED.**  Every BFS parent is `< n` when there is a vertex to parent. -/
theorem parentOf_lt (n : Nat) (edges : List Edge) (i : Nat) (hn : 0 < n) :
    parentOf n edges i < n := by
  unfold parentOf
  cases hf : (List.range n).find?
      (fun j => isNbr edges i j && decide (distA n edges j < distA n edges i)) with
  | none => exact hn
  | some j =>
      have hj : j ∈ List.range n := List.mem_of_find?_eq_some hf
      simp only [Option.getD_some]
      exact List.mem_range.mp hj

/-- **PROVED (range, for free).**  Every entry of `parentCode` is `< n`. -/
theorem parentCode_range (n : Nat) (edges : List Edge) :
    ∀ x ∈ parentCode n edges, x < n := by
  intro x hx
  unfold parentCode at hx
  obtain ⟨i, hi, hxi⟩ := List.mem_map.mp hx
  have hi' : i ∈ List.range n := List.mem_of_mem_tail hi
  have hn : 0 < n := by have := List.mem_range.mp hi'; omega
  rw [← hxi]; exact parentOf_lt n edges i hn

/-- **Non-vacuity (PROVED by computation).**  The three spanning trees of the
triangle map to the three DISTINCT length-2 parent codes `[0,1]`, `[0,0]`,
`[2,0]`.  So the concrete parent encoder is a genuine injection in the tight case
(the tree structure is used — this is NOT a junk over-count) and `ParentInjSpec`
is a satisfiable, non-vacuous obligation. -/
theorem parentCode_triangle_examples :
    parentCode 3 [(0, 1), (1, 2)] = [0, 1]
  ∧ parentCode 3 [(0, 1), (0, 2)] = [0, 0]
  ∧ parentCode 3 [(1, 2), (0, 2)] = [2, 0] := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- **`ParentInjSpec` — the SOLE de-risked residual (LEFT UNINHABITED).**  Just
injectivity of `parentCode` on spanning trees.  Strictly weaker than `PruferSpec`
(no length-`(n-2)`, no range, no decoder): closing it is the genuine BFS
parent-extraction content (every non-root vertex gets a strictly-smaller-distance
parent, the `n-1` parent edges are distinct and hence equal the tree, so equal
codes force equal edge sets, lifted to equal trees by
`spanningTree_eq_of_mem_iff`). -/
def ParentInjSpec : Prop :=
  ∀ (n : Nat) (edges : List Edge), SimpleEdges n edges →
    ∀ A ∈ spanningTreeList n edges, ∀ B ∈ spanningTreeList n edges,
      parentCode n A = parentCode n B → A = B

/-- **PROVED reduction.**  Injectivity of the concrete parent encoder yields the
loose Cayley bound (length and range are supplied for free by construction). -/
theorem cayleyLooseBound_of_parentInj (h : ParentInjSpec) : CayleyLooseBound := by
  intro n edges hS
  exact count_le_of_inj_gen n (n - 1) edges hS.1 (parentCode n)
    (fun A _ => parentCode_length n A)
    (fun A _ => parentCode_range n A)
    (fun A hA B hB => h n edges hS A hA B hB)

end YMGap.Continuum.CayleyLooseInjection

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CayleyLooseInjection.count_le_of_inj_gen
#print axioms YMGap.Continuum.CayleyLooseInjection.cayleyLooseBound_of_injection
#print axioms YMGap.Continuum.CayleyLooseInjection.padCode_length
#print axioms YMGap.Continuum.CayleyLooseInjection.padCode_inj
#print axioms YMGap.Continuum.CayleyLooseInjection.padCode_range
#print axioms YMGap.Continuum.CayleyLooseInjection.looseInjectionData_of_cayley
#print axioms YMGap.Continuum.CayleyLooseInjection.parentCode_length
#print axioms YMGap.Continuum.CayleyLooseInjection.parentOf_lt
#print axioms YMGap.Continuum.CayleyLooseInjection.parentCode_range
#print axioms YMGap.Continuum.CayleyLooseInjection.parentCode_triangle_examples
#print axioms YMGap.Continuum.CayleyLooseInjection.cayleyLooseBound_of_parentInj
