/-
# Leg (C), leg-C injection: the SET→LIST lifting that reduces Prüfer injectivity
#   to a strictly-weaker set-membership identity, plus the honest residual.

`Continuum/CayleyPruferInjection.lean` reduced the Cayley count bound
`CayleyCountBound` to ONE named injection residual `∀ n edges, PruferSpec n edges`
for the concrete leaf-stripping `prufer` encoder.  `PruferSpec` bundles three
per-tree facts on the spanning-tree list of a simple graph:

  (a) `(prufer n A).length = n - 2`;
  (b) entries `< n`;
  (c) **injectivity as LISTS**: `prufer n A = prufer n B → A = B`.

This module does the ONE genuinely-landing structural reduction of that residual:
it proves — Mathlib-free and axiom-clean — that for spanning trees, injectivity
as *lists* (c) is EQUIVALENT to injectivity modulo *set membership*.  The engine
is `sublists_eq_of_mem_iff`: two `sublists`-entries (subsequences) of a `Nodup`
list with the same element set are the *same list*.  So the injectivity half of
Prüfer's theorem may be discharged by proving only

  (c') `prufer n A = prufer n B → (∀ e, e ∈ A ↔ e ∈ B)`,

a strictly weaker conclusion than (c) (a set identity, not a list identity — the
recursion no longer has to track edge order).

## What is PROVED here (all axiom-clean, Mathlib-free)

  * `sublists_eq_of_mem_iff` — **the SET→LIST lifting** (support lemma 5 of the
    plan, `SublistEqOfMemEq`): `L.Nodup → A,B ∈ sublists L → (∀ x, x∈A ↔ x∈B) →
    A = B`.  Real new content: subsequences of a `Nodup` list are determined by
    their element set.
  * `spanningTree_eq_of_mem_iff` — its specialisation to the spanning-tree list:
    two spanning trees of a simple graph with the same edge set are equal.
  * `mem_removeLeafE` / `mem_of_mem_removeLeafE` / `not_incident_of_mem_removeLeafE`
    — the computational content of the leaf-deletion step (`removeLeafE` keeps
    exactly the non-incident edges).
  * `pruferAux_length_le` — the encoder never exceeds its fuel (a length ceiling
    the length-half will refine to the exact `n-2`).
  * `pruferSpec_of_memEqSpec` (**the reduction**): the weakened residual
    `PruferMemEqSpec` (with (c')) yields the full `PruferSpec` (with (c)), via
    `spanningTree_eq_of_mem_iff`.
  * `cayleyCountBound_of_memEqSpec` (**PROVED**): hence `CayleyCountBound`
    follows from `PruferMemEqSpec`, composing with the existing
    `cayleyCountBound_of_pruferSpec`.

## The named residual (the single honest frontier)

  * `PruferMemEqSpec` — the sharpened residual: (a), (b), and the SET form (c').
    LEFT UNINHABITED.  This is `PruferSpec` with its injectivity conclusion
    replaced by the strictly weaker set-membership identity; closing it is the
    genuine content of Prüfer's theorem (the leaf-determinacy identity
    `degreeE v A = 1 + count v (prufer n A)` plus the connectivity-preserving
    leaf-deletion recursion over `reachClosure`), a several-hundred-line
    Mathlib-free mini-project.  The sub-atoms are named in the prose below.

## Honest scope

This does NOT close leg (C).  It is a genuine, sharp REDUCTION of the standing
injection residual: the list-injectivity conclusion (c) is reduced — via the
new axiom-clean `sublists_eq_of_mem_iff` — to the strictly weaker set-membership
conclusion (c').  The remaining `PruferMemEqSpec` is LEFT UNINHABITED; nothing is
faked.  The honest sub-atoms that would inhabit it (NOT built here):

  * `DegreeOccurrence` / `FirstLeafFromCode` — `degreeE v A = 1 + count v
    (prufer n A)`; determines the stripped leaf and its neighbour from the code.
  * `TreeHasTwoLeaves` — a tree on ≥2 edges has an active leaf (so `firstLeaf`
    never hits its `0` default), extracted from the `reachClosure` fixpoint.
  * `RemoveLeafPreservesTree` — `removeLeafE (firstLeaf n A) A` is again a tree on
    one fewer active vertex (well-foundedness + length `= n-2`).
  * `LeafEdgeUnique` — a leaf has a unique incident edge, recovered by
    `neighborE` (⟹ the range fact (b)).

Not on the mass-gap critical path: `cayleyMax` feeds `TreeGraphReduction`, whose
datum is itself uninhabited for a physical lattice, and KP/Penrose convergence is
served by the parallel Euler-tour route.  Fixed-spacing strong-coupling
combinatorics; not the spacing-uniform continuum modulus; Clay YM mass gap
remains OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1/6/8)

Mathlib-free; only `Nat` / `List` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `sorry` / new `axiom`.  Witnesses are `Type`-level data where
they are data.  Every load-bearing declaration is gated with `#print axioms`
(permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.CayleyPruferInjection

namespace YMGap.Continuum.CayleyInjection

open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.CayleyMaxBound
open YMGap.Continuum.CayleyPruferInjection

/-! ## 1. The SET→LIST lifting: `sublists`-entries are determined by element set -/

/-- **`SublistEqOfMemEq` — the SET→LIST lifting.**  Two power-set (`sublists`)
entries of a `Nodup` list with the *same element set* are the *same list*.  A
`sublists`-entry is a subsequence, so it preserves the order of `L`; on a `Nodup`
list each element occurs once, so a subsequence is pinned down by which elements
it contains.  Induction on `L`, splitting each entry into the two `sublists`
halves; the cross cases are impossible because the head `a ∉ l` cannot appear in
a left-half entry. -/
theorem sublists_eq_of_mem_iff {α : Type _} :
    ∀ (L A B : List α), L.Nodup → A ∈ sublists L → B ∈ sublists L →
      (∀ x, x ∈ A ↔ x ∈ B) → A = B
  | [], A, B, _, hA, hB, _ => by
      have hA' : A = [] := List.mem_singleton.mp hA
      have hB' : B = [] := List.mem_singleton.mp hB
      rw [hA', hB']
  | a :: l, A, B, hnd, hA, hB, hmem => by
      rw [sublists_cons'] at hA hB
      have hal : a ∉ l := (List.nodup_cons.mp hnd).1
      have hl : l.Nodup := (List.nodup_cons.mp hnd).2
      have a_notin : ∀ C, C ∈ sublists l → a ∉ C :=
        fun C hC haC => hal (mem_of_mem_sublists l C hC a haC)
      rcases List.mem_append.mp hA with hAl | hAr
      · rcases List.mem_append.mp hB with hBl | hBr
        · -- A, B both in `sublists l`
          exact sublists_eq_of_mem_iff l A B hl hAl hBl hmem
        · -- A ∈ sublists l (a ∉ A), B = a :: B' (a ∈ B): impossible
          obtain ⟨B', _, hBeq⟩ := List.mem_map.mp hBr
          have haB : a ∈ B := by rw [← hBeq]; exact List.mem_cons_self
          have haA : a ∈ A := (hmem a).mpr haB
          exact absurd haA (a_notin A hAl)
      · obtain ⟨A', hA'l, hAeq⟩ := List.mem_map.mp hAr
        rcases List.mem_append.mp hB with hBl | hBr
        · -- A = a :: A' (a ∈ A), B ∈ sublists l (a ∉ B): impossible
          have haA : a ∈ A := by rw [← hAeq]; exact List.mem_cons_self
          have haB : a ∈ B := (hmem a).mp haA
          exact absurd haB (a_notin B hBl)
        · -- A = a :: A', B = a :: B'
          obtain ⟨B', hB'l, hBeq⟩ := List.mem_map.mp hBr
          have hmem' : ∀ x, x ∈ A' ↔ x ∈ B' := by
            intro x
            constructor
            · intro hxA'
              have hxA : x ∈ A := by rw [← hAeq]; exact List.mem_cons_of_mem a hxA'
              have hxB : x ∈ B := (hmem x).mp hxA
              have hxB' : x ∈ a :: B' := by rw [hBeq]; exact hxB
              rcases List.mem_cons.mp hxB' with h | h
              · exact absurd (h ▸ hxA') (a_notin A' hA'l)
              · exact h
            · intro hxB'
              have hxB : x ∈ B := by rw [← hBeq]; exact List.mem_cons_of_mem a hxB'
              have hxA : x ∈ A := (hmem x).mpr hxB
              have hxA' : x ∈ a :: A' := by rw [hAeq]; exact hxA
              rcases List.mem_cons.mp hxA' with h | h
              · exact absurd (h ▸ hxB') (a_notin B' hB'l)
              · exact h
          have hAB' : A' = B' := sublists_eq_of_mem_iff l A' B' hl hA'l hB'l hmem'
          rw [← hAeq, ← hBeq, hAB']

/-- **The spanning-tree specialisation.**  Two spanning trees of a simple graph
with the same edge set are the same list.  (The `sublists` structure supplies
order-determinacy; `edges.Nodup` from `SimpleEdges` supplies member-uniqueness.) -/
theorem spanningTree_eq_of_mem_iff (n : Nat) (edges : List Edge)
    (hE : edges.Nodup) (A B : List Edge)
    (hA : A ∈ spanningTreeList n edges) (hB : B ∈ spanningTreeList n edges)
    (hmem : ∀ e, e ∈ A ↔ e ∈ B) : A = B := by
  have hAsub : A ∈ sublists edges := (List.mem_filter.mp hA).1
  have hBsub : B ∈ sublists edges := (List.mem_filter.mp hB).1
  exact sublists_eq_of_mem_iff edges A B hE hAsub hBsub hmem

/-! ## 2. Computational content of the leaf-deletion step -/

/-- `removeLeafE` keeps exactly the edges NOT incident to the leaf. -/
theorem mem_removeLeafE (v : Nat) (edges : List Edge) (e : Edge) :
    e ∈ removeLeafE v edges ↔ e ∈ edges ∧ (! incident v e) = true := by
  unfold removeLeafE
  exact List.mem_filter

/-- An edge surviving leaf-deletion was in the original graph. -/
theorem mem_of_mem_removeLeafE {v : Nat} {edges : List Edge} {e : Edge}
    (h : e ∈ removeLeafE v edges) : e ∈ edges :=
  ((mem_removeLeafE v edges e).mp h).1

/-- A surviving edge is not incident to the deleted leaf. -/
theorem not_incident_of_mem_removeLeafE {v : Nat} {edges : List Edge} {e : Edge}
    (h : e ∈ removeLeafE v edges) : incident v e = false := by
  have := ((mem_removeLeafE v edges e).mp h).2
  cases hi : incident v e with
  | false => rfl
  | true => rw [hi] at this; exact absurd this (by decide)

/-! ## 3. The encoder respects its fuel -/

/-- **The encoder never exceeds its fuel.**  `pruferAux fuel n edges` records at
most one label per unit of fuel; the length-half of the spec refines this ceiling
to the exact `n-2` (each recorded label is one stripped leaf). -/
theorem pruferAux_length_le : ∀ (fuel n : Nat) (edges : List Edge),
    (pruferAux fuel n edges).length ≤ fuel
  | 0, _, _ => Nat.le_refl 0
  | fuel + 1, n, edges => by
      show (if edges.length ≤ 1 then []
        else neighborE (firstLeaf n edges) edges
          :: pruferAux fuel n (removeLeafE (firstLeaf n edges) edges)).length ≤ fuel + 1
      by_cases h : edges.length ≤ 1
      · rw [if_pos h]; exact Nat.zero_le _
      · rw [if_neg h, List.length_cons]
        have ih := pruferAux_length_le fuel n (removeLeafE (firstLeaf n edges) edges)
        omega

/-! ## 4. The sharpened residual and the reduction of `CayleyCountBound` -/

/-- **`PruferMemEqSpec` — the sharpened Prüfer residual (LEFT UNINHABITED).**
`PruferSpec` with its list-injectivity conclusion (c) replaced by the strictly
weaker SET-membership conclusion (c'): `prufer n A = prufer n B → (∀ e, e∈A ↔
e∈B)`.  The recursion no longer has to track edge order — the order is restored
for free by `sublists_eq_of_mem_iff`.  This is the single honest frontier of leg
(C); closing it is the genuine content of Prüfer's theorem.  Non-vacuous:
`prufer_triangle_examples` (in the encoder module) already witnesses the tight
`3 = 3^(3-2)` case. -/
def PruferMemEqSpec (n : Nat) (edges : List Edge) : Prop :=
  SimpleEdges n edges →
    (∀ A ∈ spanningTreeList n edges, (prufer n A).length = n - 2)
    ∧ (∀ A ∈ spanningTreeList n edges, ∀ x ∈ prufer n A, x < n)
    ∧ (∀ A ∈ spanningTreeList n edges, ∀ B ∈ spanningTreeList n edges,
        prufer n A = prufer n B → ∀ e, e ∈ A ↔ e ∈ B)

/-- **The reduction (PROVED): the SET form yields the full `PruferSpec`.**  The
length (a) and range (b) halves pass through unchanged; the injectivity half (c)
is recovered from the set-membership half (c') by `spanningTree_eq_of_mem_iff`. -/
theorem pruferSpec_of_memEqSpec (h : ∀ n edges, PruferMemEqSpec n edges) :
    ∀ n edges, PruferSpec n edges := by
  intro n edges hS
  obtain ⟨hlen, hrange, hmemeq⟩ := h n edges hS
  refine ⟨hlen, hrange, ?_⟩
  intro A hA B hB hcode
  exact spanningTree_eq_of_mem_iff n edges hS.1 A B hA hB (hmemeq A hA B hB hcode)

/-- **`CayleyCountBound` from the sharpened residual (PROVED).**  Composes the
reduction with the encoder module's `cayleyCountBound_of_pruferSpec`. -/
theorem cayleyCountBound_of_memEqSpec (h : ∀ n edges, PruferMemEqSpec n edges) :
    CayleyCountBound :=
  cayleyCountBound_of_pruferSpec (pruferSpec_of_memEqSpec h)

end YMGap.Continuum.CayleyInjection

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CayleyInjection.sublists_eq_of_mem_iff
#print axioms YMGap.Continuum.CayleyInjection.spanningTree_eq_of_mem_iff
#print axioms YMGap.Continuum.CayleyInjection.mem_removeLeafE
#print axioms YMGap.Continuum.CayleyInjection.not_incident_of_mem_removeLeafE
#print axioms YMGap.Continuum.CayleyInjection.pruferAux_length_le
#print axioms YMGap.Continuum.CayleyInjection.pruferSpec_of_memEqSpec
#print axioms YMGap.Continuum.CayleyInjection.cayleyCountBound_of_memEqSpec
