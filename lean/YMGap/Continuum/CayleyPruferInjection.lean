/-
# Leg (C), sharpened: the Cayley count bound via a Prüfer injection into a
#   finite code-space, reduced to ONE named injection residual.

`Continuum/CayleyMaxBound.lean` reduced the `cayleyMax` field of
`TreeGraphReduction` to a single uninhabited residual:

    CayleyCountBound : ∀ n edges, SimpleEdges n edges → treeCount n edges ≤ n^(n-2)

with `treeCount n edges = #{ A ⊆ edges : A spans, |A| = n-1 }` the concrete
spanning-tree count over the Mathlib-free `sublists` power-set enumeration.  This
module builds the *cardinality half* of Cayley's theorem as REAL, axiom-clean
Lean, and cuts the residual down to a single named injection fact.

## What is PROVED here (all axiom-clean, Mathlib-free)

The whole Cayley bound is a counting statement: the list of spanning trees
injects into the list of all length-`(n-2)` code words over `{0,…,n-1}`, whose
length is `n^(n-2)`.  This module supplies EVERYTHING except the injection:

  * `sublists_nodup` — the power-set enumeration of a `Nodup` list is `Nodup`
    (so the spanning-tree list, a `filter` of it, is `Nodup` — needed for the
    pigeonhole).
  * `nodup_map_of_injOn` — a `Nodup` list mapped by a function injective on its
    members stays `Nodup`.
  * `remOne` / `remOne_length` / `mem_remOne` / `nodup_subset_length_le` — the
    generic (`DecidableEq`) finite pigeonhole: a `Nodup` list set-embedded in
    `X` is no longer than `X`.
  * `allSeqs` / `length_allSeqs` / `mem_allSeqs` — the code-space enumeration:
    `allSeqs n k` lists every length-`k` word with entries `< n`, has length
    exactly `n^k`, and contains every such word.
  * `count_le_of_inj` — **the cardinality theorem**: if `f` sends every spanning
    tree to a length-`(n-2)` word with entries `< n`, injectively, then
    `treeCount n edges ≤ n^(n-2)`.  This is the entire pigeonhole argument, in
    real Lean, resting only on the injection.

## The named residual (the single honest frontier)

  * `CayleyInjectionData` — the DATA (`Σ'`, Type-level per the constructive
    contract) of a Prüfer-type injection: for each simple graph, a function `f`
    on spanning trees with the length/range/injectivity properties above.  This
    is exactly the content of Prüfer's theorem; LEFT UNINHABITED.
  * `cayleyCountBound_of_injection : CayleyInjectionData → CayleyCountBound`
    (**PROVED**) — with the injection data, the whole Cayley bound follows from
    `count_le_of_inj`.

## The concrete encoder (non-vacuity of the residual)

  * `prufer` — the genuine, faithful leaf-stripping Prüfer encoder (repeatedly
    strip the smallest-labelled leaf, record its neighbour).  Not junk: on the
    three spanning trees of the triangle it returns the three DISTINCT length-1
    codes `[1] , [0] , [2]` (`prufer_triangle_examples`, PROVED by computation),
    exactly the tight `3 = 3^(3-2)` case.  This rules out the "unsatisfiable
    obligation" failure mode.
  * `PruferSpec` — the concrete correctness conjecture for THIS encoder
    (length `n-2`, entries `< n`, injective on spanning trees); the sharpest
    named refinement of `CayleyInjectionData`.
  * `injectionData_of_pruferSpec` / `cayleyCountBound_of_pruferSpec`
    (**PROVED**) — the concrete encoder discharges the abstract residual, and
    hence `CayleyCountBound`, once its spec holds.

## Honest scope

This does NOT close leg (C).  It builds the cardinality argument in real Lean and
reduces `CayleyCountBound` from an opaque inequality to ONE named injection fact
(`CayleyInjectionData`, refined by the concrete `PruferSpec`).  The `SimpleEdges`
hypothesis is genuinely load-bearing (the multigraph counterexample in the
`CayleyMaxBound` header): the injection cannot exist for a multigraph.  The
residual is LEFT UNINHABITED; nothing is faked.

Fixed-spacing strong-coupling combinatorics; not the spacing-uniform continuum
modulus; Clay YM mass gap remains OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1/6/8)

Mathlib-free; only `Nat` / `List` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `sorry` / new `axiom`.  Witnesses are `Type`-level data
(`CayleyInjectionData` is a `Σ'`, not a `Prop`-`∃`).  Every load-bearing
declaration is gated with `#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.CayleyMaxBound

namespace YMGap.Continuum.CayleyPruferInjection

open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.CayleyMaxBound

/-! ## 1. The spanning-tree list and its `Nodup` -/

/-- The list of spanning trees of `(n, edges)`: the `sublists` (power-set)
entries that span and have exactly `n-1` edges.  `treeCount` is its length. -/
def spanningTreeList (n : Nat) (edges : List Edge) : List (List Edge) :=
  (sublists edges).filter (fun A => spans n A && decide (A.length = n - 1))

/-- `treeCount` is the length of the spanning-tree list (definitional). -/
theorem treeCount_eq (n : Nat) (edges : List Edge) :
    treeCount n edges = (spanningTreeList n edges).length := rfl

/-- The `sublists` cons split (definitional). -/
theorem sublists_cons' {α : Type _} (a : α) (l : List α) :
    sublists (a :: l) = sublists l ++ (sublists l).map (fun s => a :: s) := rfl

/-- Every element of every `sublists`-entry of `l` is an element of `l`. -/
theorem mem_of_mem_sublists {α : Type _} :
    ∀ (l S : List α), S ∈ sublists l → ∀ x, x ∈ S → x ∈ l
  | [], S, hS, x, hx => by
      have hS' : S ∈ ([[]] : List (List α)) := hS
      have hSnil : S = [] := List.mem_singleton.mp hS'
      rw [hSnil] at hx
      exact absurd hx List.not_mem_nil
  | a :: l', S, hS, x, hx => by
      rw [sublists_cons'] at hS
      rcases List.mem_append.mp hS with hl | hr
      · exact List.mem_cons_of_mem _ (mem_of_mem_sublists l' S hl x hx)
      · obtain ⟨T, hT, hST⟩ := List.mem_map.mp hr
        rw [← hST] at hx
        rcases List.mem_cons.mp hx with hh | hh
        · rw [hh]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (mem_of_mem_sublists l' T hT x hh)

/-- Mapping a `Nodup` list by `(a :: ·)` (always injective) stays `Nodup`. -/
theorem nodup_map_of_cons_injOn {α : Type _} {a : α} :
    ∀ (l : List (List α)), l.Nodup → (l.map (fun s => a :: s)).Nodup
  | [], _ => List.nodup_nil
  | S :: rest, hnd => by
      have hrest : rest.Nodup := (List.nodup_cons.mp hnd).2
      have hSr : S ∉ rest := (List.nodup_cons.mp hnd).1
      have ih : (rest.map (fun s => a :: s)).Nodup := nodup_map_of_cons_injOn rest hrest
      show ((a :: S) :: rest.map (fun s => a :: s)).Nodup
      refine List.nodup_cons.mpr ⟨?_, ih⟩
      intro hmem
      obtain ⟨T, hT, hTeq⟩ := List.mem_map.mp hmem
      have : S = T := by injection hTeq with _ h; exact h.symm
      exact hSr (this ▸ hT)

/-- **The power-set enumeration of a `Nodup` list is `Nodup`.**  Induction on the
list: the two `sublists`-halves are each `Nodup` (right by injectivity of
`(a :: ·)`), and disjoint (a left entry cannot equal `a :: T`, else it would
contain `a ∉ l`). -/
theorem sublists_nodup {α : Type _} :
    ∀ (l : List α), l.Nodup → (sublists l).Nodup
  | [], _ => by
      have h0 : sublists ([] : List α) = [[]] := rfl
      rw [h0]
      exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | a :: l', hnd => by
      rw [sublists_cons']
      have hl' : l'.Nodup := (List.nodup_cons.mp hnd).2
      have hanl : a ∉ l' := (List.nodup_cons.mp hnd).1
      have ihnd : (sublists l').Nodup := sublists_nodup l' hl'
      have hmapnd : ((sublists l').map (fun s => a :: s)).Nodup :=
        nodup_map_of_cons_injOn (sublists l') ihnd
      refine List.nodup_append.mpr ⟨ihnd, hmapnd, ?_⟩
      intro S hS U hU hcontra
      obtain ⟨T, hT, hUeq⟩ := List.mem_map.mp hU
      rw [← hUeq] at hcontra
      have haS : a ∈ S := by rw [hcontra]; exact List.mem_cons_self
      exact hanl (mem_of_mem_sublists l' S hS a haS)

/-! ## 2. A `Nodup`-preserving map under an injectivity-on-members hypothesis -/

/-- **A `Nodup` list mapped by a member-injective function stays `Nodup`.** -/
theorem nodup_map_of_injOn {α β : Type _} (f : α → β) :
    ∀ (l : List α), l.Nodup →
      (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l', hnd, hinj => by
      have hl' : l'.Nodup := (List.nodup_cons.mp hnd).2
      have hanl : a ∉ l' := (List.nodup_cons.mp hnd).1
      have ih : (l'.map f).Nodup :=
        nodup_map_of_injOn f l' hl'
          (fun x hx y hy => hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
      show (f a :: l'.map f).Nodup
      refine List.nodup_cons.mpr ⟨?_, ih⟩
      intro hmem
      obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hmem
      have : a = b := hinj a List.mem_cons_self b (List.mem_cons_of_mem _ hb) hfb.symm
      exact hanl (this ▸ hb)

/-! ## 3. The generic finite pigeonhole (`DecidableEq` port of `remOne`) -/

section RemOne
variable {γ : Type _} [DecidableEq γ]

/-- Remove one occurrence of `x` from a list. -/
def remOne (x : γ) : List γ → List γ
  | [] => []
  | a :: rest => if a = x then rest else a :: remOne x rest

/-- Removing one occurrence of a member drops the length by exactly one. -/
theorem remOne_length (x : γ) :
    ∀ (l : List γ), x ∈ l → (remOne x l).length + 1 = l.length
  | [], h => absurd h List.not_mem_nil
  | a :: rest, h => by
      show (if a = x then rest else a :: remOne x rest).length + 1
        = (a :: rest).length
      by_cases hax : a = x
      · rw [if_pos hax, List.length_cons]
      · rw [if_neg hax, List.length_cons, List.length_cons]
        have hxr : x ∈ rest := by
          rcases List.mem_cons.mp h with hh | hh
          · exact absurd hh.symm hax
          · exact hh
        have ih := remOne_length x rest hxr
        omega

/-- A member `b ≠ x` survives the removal of `x`. -/
theorem mem_remOne (x : γ) :
    ∀ (l : List γ) (b : γ), b ∈ l → b ≠ x → b ∈ remOne x l
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

/-- **A `Nodup` list set-embedded in `X` is no longer than `X`.** -/
theorem nodup_subset_length_le :
    ∀ (l X : List γ), l.Nodup → (∀ a, a ∈ l → a ∈ X) → l.length ≤ X.length
  | [], _, _, _ => Nat.zero_le _
  | a :: l', X, hnd, hsub => by
      have hai : a ∈ X := hsub a List.mem_cons_self
      have hndcons := List.nodup_cons.mp hnd
      have hanl : a ∉ l' := hndcons.1
      have hndl' : l'.Nodup := hndcons.2
      have hsub' : ∀ b, b ∈ l' → b ∈ remOne a X := by
        intro b hb
        have hbne : b ≠ a := fun h => hanl (h ▸ hb)
        exact mem_remOne a X b (hsub b (List.mem_cons_of_mem _ hb)) hbne
      have ih := nodup_subset_length_le l' (remOne a X) hndl' hsub'
      have hrem : (remOne a X).length + 1 = X.length := remOne_length a X hai
      show l'.length + 1 ≤ X.length
      omega

end RemOne

/-! ## 4. The code-space enumeration `allSeqs` -/

/-- Every length-`k` word over `{0,…,n-1}`, enumerated. -/
def allSeqs (n : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 => (List.range n).flatMap (fun c => (allSeqs n k).map (fun s => c :: s))

/-- `flatMap` of a constant-length family: total length is `|L| · c`. -/
theorem length_flatMap_const {α β : Type _} (g : α → List β) (c : Nat) :
    ∀ (L : List α), (∀ x ∈ L, (g x).length = c) →
      (L.flatMap g).length = L.length * c
  | [], _ => (Nat.zero_mul c).symm
  | a :: L, h => by
      have ha : (g a).length = c := h a List.mem_cons_self
      have ih := length_flatMap_const g c L (fun x hx => h x (List.mem_cons_of_mem _ hx))
      rw [List.flatMap_cons, List.length_append, ha, ih, List.length_cons,
        Nat.add_mul, Nat.one_mul]
      exact Nat.add_comm _ _

/-- **`allSeqs n k` has length exactly `n^k`.** -/
theorem length_allSeqs (n : Nat) : ∀ k, (allSeqs n k).length = n ^ k
  | 0 => rfl
  | k + 1 => by
      show ((List.range n).flatMap
        (fun c => (allSeqs n k).map (fun s => c :: s))).length = n ^ (k + 1)
      rw [length_flatMap_const (fun c => (allSeqs n k).map (fun s => c :: s))
            ((allSeqs n k).length) (List.range n) (fun _ _ => List.length_map _),
        List.length_range, length_allSeqs n k, Nat.pow_succ, Nat.mul_comm]

/-- **`allSeqs n k` contains every length-`k` word with entries `< n`.** -/
theorem mem_allSeqs (n : Nat) : ∀ (k : Nat) (code : List Nat),
    code.length = k → (∀ x ∈ code, x < n) → code ∈ allSeqs n k
  | 0, code, hlen, _ => by
      have hnil : code = [] := List.length_eq_zero_iff.mp hlen
      rw [hnil]; exact List.mem_singleton.mpr rfl
  | k + 1, code, hlen, hrange => by
      match code with
      | [] => exact absurd hlen (fun h => Nat.noConfusion h)
      | c :: rest =>
          have hrlen : rest.length = k := Nat.succ.inj hlen
          have hc : c < n := hrange c List.mem_cons_self
          have hrest : ∀ x ∈ rest, x < n :=
            fun x hx => hrange x (List.mem_cons_of_mem _ hx)
          show (c :: rest) ∈ (List.range n).flatMap
            (fun c => (allSeqs n k).map (fun s => c :: s))
          refine List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, ?_⟩
          exact List.mem_map.mpr ⟨rest, mem_allSeqs n k rest hrlen hrest, rfl⟩

/-! ## 5. The cardinality theorem (the whole Cayley bound, minus the injection) -/

/-- **The pigeonhole cardinality theorem.**  If `f` maps every spanning tree of
`(n, edges)` to a length-`(n-2)` word with entries `< n`, injectively, then
`treeCount n edges ≤ n^(n-2)`.  Proof: the spanning-tree list is `Nodup`
(`sublists_nodup` + `filter`), its `f`-image is `Nodup` (`nodup_map_of_injOn`)
and set-embedded in `allSeqs n (n-2)`, so by `nodup_subset_length_le` its length
`= treeCount` is `≤ (allSeqs n (n-2)).length = n^(n-2)`. -/
theorem count_le_of_inj (n : Nat) (edges : List Edge) (hE : edges.Nodup)
    (f : List Edge → List Nat)
    (hlen : ∀ A ∈ spanningTreeList n edges, (f A).length = n - 2)
    (hrange : ∀ A ∈ spanningTreeList n edges, ∀ x ∈ f A, x < n)
    (hinj : ∀ A ∈ spanningTreeList n edges, ∀ B ∈ spanningTreeList n edges,
        f A = f B → A = B) :
    treeCount n edges ≤ n ^ (n - 2) := by
  have hLnd : (spanningTreeList n edges).Nodup := by
    unfold spanningTreeList
    exact (List.filter_sublist).nodup (sublists_nodup edges hE)
  have hmapnd : ((spanningTreeList n edges).map f).Nodup :=
    nodup_map_of_injOn f (spanningTreeList n edges) hLnd hinj
  have hsub : ∀ y, y ∈ (spanningTreeList n edges).map f → y ∈ allSeqs n (n - 2) := by
    intro y hy
    obtain ⟨A, hA, hAy⟩ := List.mem_map.mp hy
    have hmem : f A ∈ allSeqs n (n - 2) :=
      mem_allSeqs n (n - 2) (f A) (hlen A hA) (hrange A hA)
    rw [← hAy]; exact hmem
  have hle := nodup_subset_length_le ((spanningTreeList n edges).map f)
    (allSeqs n (n - 2)) hmapnd hsub
  rw [List.length_map, length_allSeqs] at hle
  rw [treeCount_eq]
  exact hle

/-! ## 6. The named injection residual and the reduction of `CayleyCountBound` -/

/-- **`CayleyInjectionData` — the Prüfer-injection residual (Type-level DATA).**
For every simple graph, a function `f` on spanning trees landing in the
length-`(n-2)`, entries-`< n` code-space, injectively.  This is exactly the
content of Prüfer's theorem.  Carried as `Σ'` data (Rule 8: existence conclusions
are `Σ`, not `Prop`-`∃`).  LEFT UNINHABITED — the single honest residual. -/
def CayleyInjectionData : Type :=
  (n : Nat) → (edges : List Edge) → SimpleEdges n edges →
    Σ' (f : List Edge → List Nat),
      (∀ A ∈ spanningTreeList n edges, (f A).length = n - 2)
      ∧ (∀ A ∈ spanningTreeList n edges, ∀ x ∈ f A, x < n)
      ∧ (∀ A ∈ spanningTreeList n edges, ∀ B ∈ spanningTreeList n edges,
          f A = f B → A = B)

/-- **`CayleyCountBound` from the injection data (PROVED reduction).** -/
theorem cayleyCountBound_of_injection (d : CayleyInjectionData) : CayleyCountBound := by
  intro n edges hS
  obtain ⟨f, hlen, hrange, hinj⟩ := d n edges hS
  exact count_le_of_inj n edges hS.1 f hlen hrange hinj

/-! ## 7. The concrete Prüfer encoder (non-vacuity of the residual) -/

/-- `e` is incident to vertex `v`. -/
def incident (v : Nat) (e : Edge) : Bool := decide (e.1 = v) || decide (e.2 = v)

/-- Degree of `v` in an edge list. -/
def degreeE (v : Nat) (edges : List Edge) : Nat :=
  (edges.filter (incident v)).length

/-- The smallest-labelled leaf (degree-1 vertex) `< n`, or `0` if none. -/
def firstLeaf (n : Nat) (edges : List Edge) : Nat :=
  match (List.range n).find? (fun v => decide (degreeE v edges = 1)) with
  | some v => v
  | none => 0

/-- The neighbour of `v` along its first incident edge, or `0`. -/
def neighborE (v : Nat) (edges : List Edge) : Nat :=
  match edges.find? (incident v) with
  | some e => if e.1 = v then e.2 else e.1
  | none => 0

/-- Delete every edge incident to the leaf `v`. -/
def removeLeafE (v : Nat) (edges : List Edge) : List Edge :=
  edges.filter (fun e => ! incident v e)

/-- The Prüfer leaf-stripping recursion (fuel = vertex count). -/
def pruferAux : Nat → Nat → List Edge → List Nat
  | 0, _, _ => []
  | fuel + 1, n, edges =>
      if edges.length ≤ 1 then []
      else neighborE (firstLeaf n edges) edges
        :: pruferAux fuel n (removeLeafE (firstLeaf n edges) edges)

/-- **The faithful Prüfer encoder.**  Repeatedly strip the smallest-labelled
leaf and record its neighbour; a tree on `n` vertices yields an `(n-2)`-word. -/
def prufer (n : Nat) (edges : List Edge) : List Nat := pruferAux n n edges

/-- **Non-vacuity (PROVED by computation).**  The three spanning trees of the
triangle map to the three DISTINCT length-1 codes `[1], [0], [2]` — the tight
`3 = 3^(3-2)` case.  The encoder is a genuine injection here, not junk. -/
theorem prufer_triangle_examples :
    prufer 3 [(0, 1), (1, 2)] = [1]
  ∧ prufer 3 [(0, 1), (0, 2)] = [0]
  ∧ prufer 3 [(1, 2), (0, 2)] = [2] := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- **`PruferSpec` — the concrete correctness conjecture for `prufer`.**  The
sharpest named refinement of `CayleyInjectionData`: on the spanning trees of a
simple graph, `prufer n` has length `n-2`, entries `< n`, and is injective.
`prufer_triangle_examples` witnesses that this is satisfiable in the tight case
(so it is not an unsatisfiable obligation).  LEFT UNINHABITED. -/
def PruferSpec (n : Nat) (edges : List Edge) : Prop :=
  SimpleEdges n edges →
    (∀ A ∈ spanningTreeList n edges, (prufer n A).length = n - 2)
    ∧ (∀ A ∈ spanningTreeList n edges, ∀ x ∈ prufer n A, x < n)
    ∧ (∀ A ∈ spanningTreeList n edges, ∀ B ∈ spanningTreeList n edges,
        prufer n A = prufer n B → A = B)

/-- **The concrete encoder discharges the abstract residual (PROVED).** -/
def injectionData_of_pruferSpec (h : ∀ n edges, PruferSpec n edges) :
    CayleyInjectionData :=
  fun n edges hS =>
    ⟨prufer n, (h n edges hS).1, (h n edges hS).2.1, (h n edges hS).2.2⟩

/-- **`CayleyCountBound` from the concrete Prüfer spec (PROVED).** -/
theorem cayleyCountBound_of_pruferSpec (h : ∀ n edges, PruferSpec n edges) :
    CayleyCountBound :=
  cayleyCountBound_of_injection (injectionData_of_pruferSpec h)

end YMGap.Continuum.CayleyPruferInjection

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CayleyPruferInjection.sublists_nodup
#print axioms YMGap.Continuum.CayleyPruferInjection.nodup_map_of_injOn
#print axioms YMGap.Continuum.CayleyPruferInjection.nodup_subset_length_le
#print axioms YMGap.Continuum.CayleyPruferInjection.length_allSeqs
#print axioms YMGap.Continuum.CayleyPruferInjection.mem_allSeqs
#print axioms YMGap.Continuum.CayleyPruferInjection.count_le_of_inj
#print axioms YMGap.Continuum.CayleyPruferInjection.cayleyCountBound_of_injection
#print axioms YMGap.Continuum.CayleyPruferInjection.prufer_triangle_examples
#print axioms YMGap.Continuum.CayleyPruferInjection.cayleyCountBound_of_pruferSpec
