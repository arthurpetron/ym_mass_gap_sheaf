/-
# `SpansMinEdges` — "a connected spanning subgraph on `n` vertices has `≥ n-1`
#   edges", PROVED axiom-clean over the concrete BFS `reachClosure`.

`Continuum/PenroseDCContract.lean` carries the weightless treeCount residual

    SpansMinEdges : ∀ (n : Nat) (A : List Edge), spans n A = true → n ≤ A.length + 1

as a NAMED-open `Prop`.  This module CLOSES it.

## The argument

`spans n A = true` unfolds to `∀ i, i < n → i ∈ reachClosure n A [0]`.  The
reachable list `reach = reachClosure n A [0]` is built from `addV`, which never
creates duplicates, so `reach` is `Nodup`.  Since it contains every `i < n`,
`List.range n` set-embeds into `reach`, so by the finite pigeonhole
(`nodup_subset_length_le`) `n = |range n| ≤ |reach|`.

The core is the **spanning-forest length bound**

    (reachClosure k A R).length ≤ R.length + A.length          (`reachClosure_length_le`)

proved via the monovariant  `pot A R = R.length + unsatCount A R`, where
`unsatCount A R` counts the edges of `A` with at most one endpoint reached.
Each undirected relaxation step (`relaxEdge`) that adds a NEW vertex saturates
the triggering edge — `|R|` goes up by one while `unsatCount` drops by at least
one — so `pot` is monovariant along the ENTIRE BFS run
(`pot_relaxEdge_le` ⟶ `pot_foldr_le` ⟶ `pot_reachClosure_le`).  Hence

    |reach| ≤ pot A reach ≤ pot A [0] = 1 + unsatCount A [0] ≤ 1 + |A|,

which combined with `n ≤ |reach|` gives `n ≤ |A| + 1`.  This is exactly the
"each edge introduces at most one new reachable vertex over the entire run"
injection, formalized as a potential.

## Constructive contract (`lean/AGENTS.md` Rules 1/6/8)

Mathlib-free; only `Nat` / `List` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `sorry` / new `axiom`.  `by_cases`/`decide` are on decidable
`Nat`/`List`/`Bool` propositions only (no `Classical` dependency — verified by
the `#print axioms` gates: permitted `propext` / `Quot.sound`).
-/

import YMGap.Continuum.PenroseDCContract
import YMGap.Continuum.CayleyPruferInjection

namespace YMGap.Continuum.SpansMinEdgesProof

open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.CayleyPruferInjection

/-! ## 0. A self-contained `filter`-length toolkit (no Mathlib name guessing) -/

/-- `(l.filter p).length ≤ l.length`. -/
theorem filter_length_le {α : Type _} (p : α → Bool) :
    ∀ l : List α, (l.filter p).length ≤ l.length
  | [] => Nat.le_refl _
  | a :: t => by
      rw [List.filter_cons]
      by_cases hp : p a = true
      · rw [if_pos hp, List.length_cons, List.length_cons]
        exact Nat.succ_le_succ (filter_length_le p t)
      · rw [if_neg hp, List.length_cons]
        exact Nat.le_succ_of_le (filter_length_le p t)

/-- **Filter-length monotonicity.**  If `q a → p a` pointwise then the `q`-filter
is no longer than the `p`-filter. -/
theorem filter_len_le_of_imp {α : Type _} (p q : α → Bool)
    (himp : ∀ a, q a = true → p a = true) :
    ∀ l : List α, (l.filter q).length ≤ (l.filter p).length
  | [] => Nat.le_refl _
  | a :: t => by
      rw [List.filter_cons, List.filter_cons]
      by_cases hqa : q a = true
      · have hpa : p a = true := himp a hqa
        rw [if_pos hqa, if_pos hpa, List.length_cons, List.length_cons]
        have ih := filter_len_le_of_imp p q himp t
        omega
      · rw [if_neg hqa]
        by_cases hpa : p a = true
        · rw [if_pos hpa, List.length_cons]
          have ih := filter_len_le_of_imp p q himp t
          omega
        · rw [if_neg hpa]
          exact filter_len_le_of_imp p q himp t

/-- **Strict filter-length drop.**  If `q ⟹ p` pointwise and some member `a₀`
has `p a₀` but not `q a₀`, then the `q`-filter is strictly shorter. -/
theorem filter_len_lt_of_witness {α : Type _} (p q : α → Bool)
    (himp : ∀ a, q a = true → p a = true) :
    ∀ (l : List α) (a₀ : α), a₀ ∈ l → p a₀ = true → q a₀ = false →
      (l.filter q).length + 1 ≤ (l.filter p).length := by
  intro l
  induction l with
  | nil => intro a₀ ha _ _; exact absurd ha List.not_mem_nil
  | cons a t ih =>
      intro a₀ ha hp0 hq0
      rw [List.filter_cons, List.filter_cons]
      rcases List.mem_cons.mp ha with hh | hh
      · subst hh
        rw [if_pos hp0, if_neg (by rw [hq0]; exact Bool.false_ne_true), List.length_cons]
        have hle := filter_len_le_of_imp p q himp t
        omega
      · have ihlt := ih a₀ hh hp0 hq0
        by_cases hqa : q a = true
        · have hpa : p a = true := himp a hqa
          rw [if_pos hqa, if_pos hpa, List.length_cons, List.length_cons]
          omega
        · rw [if_neg hqa]
          by_cases hpa : p a = true
          · rw [if_pos hpa, List.length_cons]; omega
          · rw [if_neg hpa]; exact ihlt

/-! ## 1. The saturation predicate and the monovariant `pot` -/

/-- `satB R e` is `true` iff BOTH endpoints of `e` are already reached. -/
def satB (R : List Nat) (e : Edge) : Bool := decide (e.1 ∈ R ∧ e.2 ∈ R)

/-- `unsatB R e` — the edge `e` is not yet saturated (`< 2` endpoints reached). -/
def unsatB (R : List Nat) (e : Edge) : Bool := ! satB R e

/-- Number of edges of `A` not yet saturated by `R`. -/
def unsatCount (A : List Edge) (R : List Nat) : Nat := (A.filter (unsatB R)).length

/-- The monovariant potential: reached count `+` unsaturated-edge count. -/
def pot (A : List Edge) (R : List Nat) : Nat := R.length + unsatCount A R

/-- If `e.1 ∉ R` then `e` is unsaturated by `R`. -/
theorem unsatB_true_of_not_mem1 (R : List Nat) (e : Edge) (h : e.1 ∉ R) :
    unsatB R e = true := by
  have hns : ¬ (e.1 ∈ R ∧ e.2 ∈ R) := fun hc => h hc.1
  have hs : satB R e = false := decide_eq_false_iff_not.mpr hns
  show (! satB R e) = true
  rw [hs]; exact Bool.not_false

/-- If `e.2 ∉ R` then `e` is unsaturated by `R`. -/
theorem unsatB_true_of_not_mem2 (R : List Nat) (e : Edge) (h : e.2 ∉ R) :
    unsatB R e = true := by
  have hns : ¬ (e.1 ∈ R ∧ e.2 ∈ R) := fun hc => h hc.2
  have hs : satB R e = false := decide_eq_false_iff_not.mpr hns
  show (! satB R e) = true
  rw [hs]; exact Bool.not_false

/-- If both endpoints of `e` are in `S` then `e` is saturated by `S`. -/
theorem unsatB_false_of_mem (S : List Nat) (e : Edge) (h1 : e.1 ∈ S) (h2 : e.2 ∈ S) :
    unsatB S e = false := by
  have hs : satB S e = true := by
    show decide (e.1 ∈ S ∧ e.2 ∈ S) = true
    rw [decide_eq_true_eq]; exact ⟨h1, h2⟩
  show (! satB S e) = false
  rw [hs]; exact Bool.not_true

/-- Saturation is monotone: growing `R` cannot un-saturate an edge, so
un-saturation w.r.t. the larger set implies un-saturation w.r.t. the smaller. -/
theorem unsatB_imp (v : Nat) (R : List Nat) (e : Edge)
    (h : unsatB (v :: R) e = true) : unsatB R e = true := by
  by_cases hb : e.2 ∈ R
  · by_cases ha : e.1 ∈ R
    · have hf : unsatB (v :: R) e = false :=
        unsatB_false_of_mem (v :: R) e (List.mem_cons_of_mem _ ha) (List.mem_cons_of_mem _ hb)
      rw [hf] at h
      exact absurd h (by decide)
    · exact unsatB_true_of_not_mem1 R e ha
  · exact unsatB_true_of_not_mem2 R e hb

/-! ## 2. `pot` does not increase under one relaxation step -/

/-- **The key monovariant step.**  For any edge `e ∈ A`, one relaxation of `e`
does not increase `pot`: if it adds a new vertex, the triggering edge `e`
saturates, so the `+1` in `|R|` is paid for by a `-1` in `unsatCount`. -/
theorem pot_relaxEdge_le (A : List Edge) (e : Edge) (heA : e ∈ A) (R : List Nat) :
    pot A (relaxEdge e R) ≤ pot A R := by
  by_cases h1 : e.1 ∈ R
  · by_cases h2 : e.2 ∈ R
    · have hre : relaxEdge e R = R := by
        unfold relaxEdge addV; rw [if_pos h1, if_pos h2]
      rw [hre]; exact Nat.le_refl _
    · have hre : relaxEdge e R = e.2 :: R := by
        unfold relaxEdge addV; rw [if_pos h1, if_neg h2]
      rw [hre]
      have hwit : unsatCount A (e.2 :: R) + 1 ≤ unsatCount A R :=
        filter_len_lt_of_witness (unsatB R) (unsatB (e.2 :: R))
          (fun e' hq => unsatB_imp e.2 R e' hq) A e heA
          (unsatB_true_of_not_mem2 R e h2)
          (unsatB_false_of_mem (e.2 :: R) e (List.mem_cons_of_mem _ h1) List.mem_cons_self)
      unfold pot; rw [List.length_cons]; omega
  · by_cases h2 : e.2 ∈ R
    · have hre : relaxEdge e R = e.1 :: R := by
        unfold relaxEdge addV; rw [if_neg h1, if_pos h2, if_neg h1]
      rw [hre]
      have hwit : unsatCount A (e.1 :: R) + 1 ≤ unsatCount A R :=
        filter_len_lt_of_witness (unsatB R) (unsatB (e.1 :: R))
          (fun e' hq => unsatB_imp e.1 R e' hq) A e heA
          (unsatB_true_of_not_mem1 R e h1)
          (unsatB_false_of_mem (e.1 :: R) e List.mem_cons_self (List.mem_cons_of_mem _ h2))
      unfold pot; rw [List.length_cons]; omega
    · have hre : relaxEdge e R = R := by
        unfold relaxEdge; rw [if_neg h1, if_neg h2]
      rw [hre]; exact Nat.le_refl _

/-! ## 3. `pot` is monovariant across a whole pass and the whole BFS -/

/-- One `foldr`-pass of relaxation over a sublist of `A` does not increase `pot`. -/
theorem pot_foldr_le (A : List Edge) :
    ∀ (B : List Edge), (∀ e, e ∈ B → e ∈ A) → ∀ (R : List Nat),
      pot A (B.foldr relaxEdge R) ≤ pot A R
  | [], _, R => Nat.le_refl _
  | e :: rest, hsub, R => by
      have hrest : ∀ e', e' ∈ rest → e' ∈ A := fun e' h => hsub e' (List.mem_cons_of_mem _ h)
      have heA : e ∈ A := hsub e List.mem_cons_self
      have ih : pot A (rest.foldr relaxEdge R) ≤ pot A R := pot_foldr_le A rest hrest R
      have hstep : pot A (relaxEdge e (rest.foldr relaxEdge R))
          ≤ pot A (rest.foldr relaxEdge R) :=
        pot_relaxEdge_le A e heA (rest.foldr relaxEdge R)
      show pot A (relaxEdge e (rest.foldr relaxEdge R)) ≤ pot A R
      exact Nat.le_trans hstep ih

/-- One full relaxation pass `relax A` does not increase `pot`. -/
theorem pot_relax_le (A : List Edge) (R : List Nat) : pot A (relax A R) ≤ pot A R := by
  show pot A (A.foldr relaxEdge R) ≤ pot A R
  exact pot_foldr_le A A (fun _ h => h) R

/-- The whole `n`-fold BFS closure does not increase `pot`. -/
theorem pot_reachClosure_le (A : List Edge) :
    ∀ (k : Nat) (R : List Nat), pot A (reachClosure k A R) ≤ pot A R
  | 0, R => Nat.le_refl _
  | k + 1, R => by
      have h1 : pot A (reachClosure k A (relax A R)) ≤ pot A (relax A R) :=
        pot_reachClosure_le A k (relax A R)
      have h2 : pot A (relax A R) ≤ pot A R := pot_relax_le A R
      show pot A (reachClosure k A (relax A R)) ≤ pot A R
      exact Nat.le_trans h1 h2

/-- **The spanning-forest length bound.**  The reachable set after any number of
BFS passes has size at most `|R| + |A|` — each edge contributes at most one new
reachable vertex over the entire run. -/
theorem reachClosure_length_le (A : List Edge) (k : Nat) (R : List Nat) :
    (reachClosure k A R).length ≤ R.length + A.length := by
  have hpot : pot A (reachClosure k A R) ≤ pot A R := pot_reachClosure_le A k R
  have hlen : (reachClosure k A R).length ≤ pot A (reachClosure k A R) := by
    unfold pot; exact Nat.le_add_right _ _
  have hf : (A.filter (unsatB R)).length ≤ A.length := filter_length_le _ _
  have hpotR : pot A R ≤ R.length + A.length := by
    unfold pot unsatCount; omega
  omega

/-! ## 4. `reachClosure` preserves `Nodup` -/

/-- `addV` preserves `Nodup` (it inserts only when absent). -/
theorem addV_nodup (x : Nat) (R : List Nat) (h : R.Nodup) : (addV x R).Nodup := by
  unfold addV
  by_cases hx : x ∈ R
  · rw [if_pos hx]; exact h
  · rw [if_neg hx]; exact List.nodup_cons.mpr ⟨hx, h⟩

/-- One relaxation across a single edge preserves `Nodup`. -/
theorem relaxEdge_nodup (e : Edge) (R : List Nat) (h : R.Nodup) : (relaxEdge e R).Nodup := by
  unfold relaxEdge
  by_cases h1 : e.1 ∈ R
  · rw [if_pos h1]; exact addV_nodup e.2 R h
  · rw [if_neg h1]
    by_cases h2 : e.2 ∈ R
    · rw [if_pos h2]; exact addV_nodup e.1 R h
    · rw [if_neg h2]; exact h

/-- A `foldr` of relaxations preserves `Nodup`. -/
theorem foldr_relaxEdge_nodup :
    ∀ (B : List Edge) (R : List Nat), R.Nodup → (B.foldr relaxEdge R).Nodup
  | [], R, h => h
  | e :: rest, R, h =>
      relaxEdge_nodup e (rest.foldr relaxEdge R) (foldr_relaxEdge_nodup rest R h)

/-- The full BFS closure preserves `Nodup`. -/
theorem reachClosure_nodup :
    ∀ (k : Nat) (A : List Edge) (R : List Nat), R.Nodup → (reachClosure k A R).Nodup
  | 0, _, R, h => h
  | k + 1, A, R, h =>
      reachClosure_nodup k A (relax A R) (foldr_relaxEdge_nodup A R h)

/-! ## 5. An axiom-clean `{0,…,n-1}` list (Lean core's `List.range` uses `Classical`) -/

/-- The descending list `[n-1, …, 1, 0]` of all vertices `< n`. -/
def downRange : Nat → List Nat
  | 0 => []
  | k + 1 => k :: downRange k

theorem length_downRange : ∀ n, (downRange n).length = n
  | 0 => rfl
  | k + 1 => by show (k :: downRange k).length = k + 1; rw [List.length_cons, length_downRange k]

theorem mem_downRange : ∀ (n i : Nat), i ∈ downRange n ↔ i < n
  | 0, i => by
      show i ∈ ([] : List Nat) ↔ i < 0
      constructor
      · intro h; exact absurd h List.not_mem_nil
      · intro h; exact absurd h (Nat.not_lt_zero i)
  | k + 1, i => by
      show i ∈ (k :: downRange k) ↔ i < k + 1
      rw [List.mem_cons, mem_downRange k i]
      constructor
      · rintro (heq | h)
        · rw [heq]; exact Nat.lt_succ_self k
        · exact Nat.lt_succ_of_lt h
      · intro h
        rcases Nat.lt_or_ge i k with h' | h'
        · exact Or.inr h'
        · exact Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ h) h')

theorem nodup_downRange : ∀ n, (downRange n).Nodup
  | 0 => List.nodup_nil
  | k + 1 => by
      show (k :: downRange k).Nodup
      refine List.nodup_cons.mpr ⟨?_, nodup_downRange k⟩
      intro h
      exact absurd ((mem_downRange k k).mp h) (Nat.lt_irrefl k)

/-! ## 6. `SpansMinEdges` — CLOSED -/

/-- **`SpansMinEdges` (PROVED).**  A connected spanning subgraph on `n` vertices
has at least `n-1` edges: if every vertex `< n` is reachable from `0` in `(n, A)`
then `n ≤ |A| + 1`.  Combines the pigeonhole `n = |range n| ≤ |reach|` (from
`Nodup reach` + `range n ⊆ reach`) with the spanning-forest bound
`|reach| ≤ 1 + |A|`. -/
theorem spansMinEdges : PenroseDCContract.SpansMinEdges := by
  intro n A hspan
  have hmem : ∀ i, i < n → i ∈ reachClosure n A [0] := of_decide_eq_true hspan
  have hsub : ∀ a, a ∈ downRange n → a ∈ reachClosure n A [0] :=
    fun a ha => hmem a ((mem_downRange n a).mp ha)
  have hle1 : (downRange n).length ≤ (reachClosure n A [0]).length :=
    nodup_subset_length_le (downRange n) (reachClosure n A [0]) (nodup_downRange n) hsub
  have hle2 : (reachClosure n A [0]).length ≤ ([0] : List Nat).length + A.length :=
    reachClosure_length_le A n [0]
  rw [length_downRange] at hle1
  have hone : ([0] : List Nat).length = 1 := rfl
  rw [hone] at hle2
  omega

end YMGap.Continuum.SpansMinEdgesProof

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SpansMinEdgesProof.filter_len_lt_of_witness
#print axioms YMGap.Continuum.SpansMinEdgesProof.pot_relaxEdge_le
#print axioms YMGap.Continuum.SpansMinEdgesProof.pot_reachClosure_le
#print axioms YMGap.Continuum.SpansMinEdgesProof.reachClosure_length_le
#print axioms YMGap.Continuum.SpansMinEdgesProof.reachClosure_nodup
#print axioms YMGap.Continuum.SpansMinEdgesProof.spansMinEdges
