/-
# The weightless spanning-tree deletion–contraction count `TreeCountContract`:
#   the counting combinatorics PROVED, reduced to ONE correctly-guarded
#   connectivity residual + an adversarial refutation of the un-guarded form.

`Continuum/PenroseDCContract.lean` names the weightless residual

    TreeCountContract : ∀ (n a b : Nat) (rest : List Edge), a ≠ b →
      treeCount n ((a, b) :: rest)
        = treeCount n rest + treeCount (n - 1) (contractEdges a b rest)

and its companion `Continuum/PenroseWeightedRepair.lean` names the connectivity
half `SpansContract` with guards `a ≠ b, a < n, b < n`.  Working this out
adversarially (exhaustive machine search over the concrete BFS `spans` /
`contractEdges` / `treeCount`) reveals the residual **as stated is FALSE**, for
two independent reasons:

  1. **No lower bound on `n`.**  With Lean's *truncated* `Nat` subtraction,
     `treeCount 0 edges = 1` (only `[]` has `length = 0 - 1 = 0`), so at
     `n = 0, (a,b) = (0,1), rest = []`:
         LHS `treeCount 0 [(0,1)] = 1`,
         RHS `treeCount 0 [] + treeCount 0 [] = 1 + 1 = 2`.
     Refuted by `treeCountContract_unguarded_false`.

  2. **Orientation.**  `contractEdges a b` merges `b` into `a` **and shifts every
     label `> b` down by one** (`relabelV`).  That collapses the vertex set to
     `{0,…,n-2}` only when `a < b`; for `a > b` the merged endpoint `a` is itself
     shifted, so both the count identity and the connectivity invariance fail
     in-range (e.g. `n=3,(a,b)=(1,0),rest=[(0,1)]`).  Hence the companion
     `SpansContract` (which lacks `a < b`) is *also* false as stated.

The genuinely TRUE statement carries the guard `a < b, b < n` (which implies
`a ≠ b`, `a < n`, and `2 ≤ n`).  Under it every finite piece of the counting
bijection is discharged here axiom-clean, reducing the whole identity to ONE
clean connectivity fact.

## What is PROVED here (all axiom-clean)

  * `length_filter_map` — `((L.map f).filter p).length =
    (L.filter (p ∘ f)).length` (filtering commutes with a `map`, length form).
  * `decLen` — the `Nat`-subtraction length bookkeeping: for `2 ≤ n`,
    `decide (L + 1 = n - 1) = decide (L = n - 1 - 1)` (the `|(a,b)::s| = n-1`
    vs `|contractEdges a b s| = (n-1)-1` guard, `Bool`-level).
  * `treeCount_cons_split` — the DELETE half: `treeCount n (e :: rest) =
    treeCount n rest + (head-containing branch count)`, a `sublists`/`filter`
    append split (general head, weightless).
  * `treeCount_contract_as_filter` — the contracted count re-expressed as a
    `filter` over `sublists rest` (via `sublists_map` + `length_filter_map`).
  * **`treeCountContractGuarded`** — THE DELIVERABLE.  For `a < b`, `b < n`:
        treeCount n ((a,b)::rest)
          = treeCount n rest + treeCount (n-1) (contractEdges a b rest),
    the spanning-tree deletion–contraction identity, PROVED from the single
    named connectivity residual `SpansContractLt` by the head/no-head
    `sublists` split, the length-preserving `map` bijection, and the length
    bookkeeping.  This is the true content the un-guarded `TreeCountContract`
    was meant to capture.

## The single named residual consumed (genuinely TRUE, uninhabited here)

  * `SpansContractLt` — the CORRECTLY-guarded weightless edge-contraction
    invariance of connectivity:
        a < b → b < n →
          spans n ((a,b)::A) = spans (n-1) (contractEdges a b A).
    Exhaustively machine-verified TRUE (0 counterexamples over all graphs on
    ≤ 5 vertices, `|A| ≤ 2`); false without `a < b` (see reason 2 above), so
    this supersedes the mis-guarded `PenroseWeightedRepair.SpansContract`.
    Left UNINHABITED — the pure BFS-reachability contraction fact, the sole
    combinatorial core the count identity rests on.  Nothing is faked.

## What is REFUTED here (adversarial correction)

  * `treeCountContract_unguarded_false : ¬ TreeCountContract` — the residual as
    literally stated in `PenroseDCContract` is not inhabitable (reason 1).

## Constructive contract (`lean/AGENTS.md` Rules 1/6/8)

Mathlib-free; only `Nat` / `List` / `Bool` core.  No `Classical.*`, no `Real`,
no `native_decide`, no `sorry` / new `axiom`.  `by_cases`/`decide` are on
decidable `Nat`/`Bool`/`List` propositions only.  Every load-bearing
declaration is gated with `#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.PenroseWeightedRepair

namespace YMGap.Continuum.TreeCountContractProof

open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.PenroseDCContract

/-! ## 1. Filtering commutes with `map` (length form) -/

/-- **`length_filter_map`.**  Filtering a mapped list has the same length as
filtering the pre-image by the pre-composed predicate:
`((L.map f).filter p).length = (L.filter (fun x => p (f x))).length`. -/
theorem length_filter_map {α β : Type _} (f : α → β) (p : β → Bool) :
    ∀ L : List α,
      ((L.map f).filter p).length = (L.filter (fun x => p (f x))).length
  | [] => rfl
  | a :: t => by
      show (((f a) :: (t.map f)).filter p).length
         = ((a :: t).filter (fun x => p (f x))).length
      rw [List.filter_cons, List.filter_cons]
      by_cases hp : p (f a) = true
      · rw [if_pos hp, if_pos hp, List.length_cons, List.length_cons,
            length_filter_map f p t]
      · rw [if_neg hp, if_neg hp, length_filter_map f p t]

/-! ## 2. The `Nat`-subtraction length bookkeeping -/

/-- **`decLen`.**  For `2 ≤ n`, the `Bool` guards
`|(a,b)::s| = n-1` (i.e. `s.length + 1 = n - 1`) and
`|contractEdges a b s| = (n-1)-1` (i.e. `s.length = n - 1 - 1`) agree.  The
`2 ≤ n` hypothesis is essential: at `n ≤ 1` truncated subtraction breaks the
equivalence (this is reason 1 the un-guarded residual fails). -/
theorem decLen (n L : Nat) (h : 2 ≤ n) :
    decide (L + 1 = n - 1) = decide (L = n - 1 - 1) := by
  by_cases hp : L + 1 = n - 1
  · have hq : L = n - 1 - 1 := by omega
    have e1 : decide (L + 1 = n - 1) = true := by rw [decide_eq_true_eq]; exact hp
    have e2 : decide (L = n - 1 - 1) = true := by rw [decide_eq_true_eq]; exact hq
    rw [e1, e2]
  · have hq : ¬ (L = n - 1 - 1) := by omega
    have e1 : decide (L + 1 = n - 1) = false := decide_eq_false_iff_not.mpr hp
    have e2 : decide (L = n - 1 - 1) = false := decide_eq_false_iff_not.mpr hq
    rw [e1, e2]

/-! ## 3. The delete half: a `sublists`/`filter` head split -/

/-- **The delete half (general head `e`, weightless).**  Splitting the
`sublists` power-set of `e :: rest` into subsets that OMIT vs CONTAIN the head
edge gives `treeCount n (e :: rest) = treeCount n rest + (branch count)`, where
the branch count runs over `s ⊆ rest` with `spans n (e :: s)` and
`|(e::s)| = n-1`. -/
theorem treeCount_cons_split (n : Nat) (e : Edge) (rest : List Edge) :
    treeCount n (e :: rest)
      = treeCount n rest
        + ((sublists rest).filter
            (fun s => spans n (e :: s) && decide ((e :: s).length = n - 1))).length := by
  have key : sublists (e :: rest)
      = sublists rest ++ (sublists rest).map (fun s => e :: s) := rfl
  show (((sublists (e :: rest)).filter
          (fun A => spans n A && decide (A.length = n - 1))).length)
     = ((sublists rest).filter (fun A => spans n A && decide (A.length = n - 1))).length
       + ((sublists rest).filter
            (fun s => spans n (e :: s) && decide ((e :: s).length = n - 1))).length
  rw [key, List.filter_append, List.length_append]
  have hB : (((sublists rest).map (fun s => e :: s)).filter
              (fun A => spans n A && decide (A.length = n - 1))).length
      = ((sublists rest).filter
          (fun s => spans n (e :: s) && decide ((e :: s).length = n - 1))).length :=
    length_filter_map (fun s => e :: s)
      (fun A => spans n A && decide (A.length = n - 1)) (sublists rest)
  rw [hB]

/-! ## 4. The contracted count as a `filter` over `sublists rest` -/

/-- The contracted spanning-tree count re-expressed as a `filter` over the same
`sublists rest`, via `sublists_map` (contraction is a `map` on edges) and
`length_filter_map`. -/
theorem treeCount_contract_as_filter (n a b : Nat) (rest : List Edge) :
    treeCount (n - 1) (contractEdges a b rest)
      = ((sublists rest).filter
          (fun s => spans (n - 1) (contractEdges a b s)
                    && decide ((contractEdges a b s).length = n - 1 - 1))).length := by
  have key : sublists (contractEdges a b rest)
      = (sublists rest).map (fun s => contractEdges a b s) := by
    show sublists (rest.map (fun e : Edge => (relabelV a b e.1, relabelV a b e.2)))
       = (sublists rest).map
           (fun s => s.map (fun e : Edge => (relabelV a b e.1, relabelV a b e.2)))
    exact PenroseWeightedRepair.sublists_map
      (fun e : Edge => (relabelV a b e.1, relabelV a b e.2)) rest
  show ((sublists (contractEdges a b rest)).filter
          (fun A => spans (n - 1) A && decide (A.length = n - 1 - 1))).length = _
  rw [key]
  exact length_filter_map (fun s => contractEdges a b s)
      (fun A => spans (n - 1) A && decide (A.length = n - 1 - 1)) (sublists rest)

/-! ## 5. The correctly-guarded connectivity residual -/

/-- **`SpansContractLt` — the correctly-guarded weightless connectivity
contraction invariance (the sole combinatorial core, uninhabited here).**  For
`a < b` and `b < n`,
    `spans n ((a,b)::A) = spans (n-1) (contractEdges a b A)`.
The guard `a < b` is essential (not merely `a ≠ b`): `contractEdges a b` merges
`b` into `a` and shifts labels `> b` down, which collapses the vertex set to
`{0,…,n-2}` only when `a < b`; the companion `PenroseWeightedRepair.SpansContract`
(guards `a ≠ b, a < n, b < n`) is FALSE in-range for `a > b`
(e.g. `n=3,(a,b)=(1,0),A=[(0,1)]`), so this supersedes it.  Machine-verified TRUE
over all graphs on `≤ 5` vertices with `|A| ≤ 2`.  Left UNINHABITED — the pure
BFS-reachability fact the count identity reduces to. -/
def SpansContractLt : Prop :=
  ∀ (n a b : Nat) (A : List Edge), a < b → b < n →
    spans n ((a, b) :: A) = spans (n - 1) (contractEdges a b A)

/-! ## 6. THE DELIVERABLE: the guarded spanning-tree contraction identity -/

/-- **`treeCountContractGuarded` — the weightless spanning-tree
deletion–contraction count identity (PROVED from `SpansContractLt`).**

For `a < b`, `b < n`:

    treeCount n ((a,b)::rest)
      = treeCount n rest + treeCount (n-1) (contractEdges a b rest).

The delete half (`+ treeCount n rest`) is the `sublists` head split
(`treeCount_cons_split`).  The contract half (`+ treeCount (n-1) …`) is the
length-preserving bijection `s ↦ contractEdges a b s` between
`{spanning trees through (a,b)}` and `{spanning trees of the contraction}`:
`treeCount_contract_as_filter` re-expresses it as a `filter` over the SAME
`sublists rest`, and the two branch predicates coincide pointwise via the
connectivity invariance `SpansContractLt` (guard) and the length bookkeeping
`decLen` (`|(a,b)::s| = n-1 ⟺ |contractEdges a b s| = (n-1)-1` for `2 ≤ n`).
Weightless throughout, hence immune to the weight-relabelling defect that
refutes the non-loop `Csum` half in `PenroseDCContract`. -/
theorem treeCountContractGuarded (hSC : SpansContractLt)
    (n a b : Nat) (rest : List Edge) (hab : a < b) (hbn : b < n) :
    treeCount n ((a, b) :: rest)
      = treeCount n rest + treeCount (n - 1) (contractEdges a b rest) := by
  have h2n : 2 ≤ n := by omega
  have hL : treeCount n ((a, b) :: rest)
      = treeCount n rest
        + ((sublists rest).filter
            (fun s => spans n ((a, b) :: s)
                      && decide (((a, b) :: s).length = n - 1))).length :=
    treeCount_cons_split n (a, b) rest
  have hR : treeCount (n - 1) (contractEdges a b rest)
      = ((sublists rest).filter
          (fun s => spans (n - 1) (contractEdges a b s)
                    && decide ((contractEdges a b s).length = n - 1 - 1))).length :=
    treeCount_contract_as_filter n a b rest
  have hbranch :
      ((sublists rest).filter
        (fun s => spans n ((a, b) :: s)
                  && decide (((a, b) :: s).length = n - 1))).length
    = ((sublists rest).filter
        (fun s => spans (n - 1) (contractEdges a b s)
                  && decide ((contractEdges a b s).length = n - 1 - 1))).length := by
    have hpred :
        (fun s => spans n ((a, b) :: s)
                  && decide (((a, b) :: s).length = n - 1))
      = (fun s => spans (n - 1) (contractEdges a b s)
                  && decide ((contractEdges a b s).length = n - 1 - 1)) := by
      funext s
      have hspan : spans n ((a, b) :: s) = spans (n - 1) (contractEdges a b s) :=
        hSC n a b s hab hbn
      have e2 : (contractEdges a b s).length = s.length := by
        show (s.map (fun e : Edge => (relabelV a b e.1, relabelV a b e.2))).length
           = s.length
        rw [List.length_map]
      have hlen : decide (((a, b) :: s).length = n - 1)
                = decide ((contractEdges a b s).length = n - 1 - 1) := by
        show decide (s.length + 1 = n - 1)
           = decide ((contractEdges a b s).length = n - 1 - 1)
        rw [e2]
        exact decLen n s.length h2n
      rw [hspan, hlen]
    rw [hpred]
  rw [hL, hR, hbranch]

/-! ## 7. Refutation of the un-guarded residual (adversarial) -/

/-- **`treeCountContract_unguarded_false : ¬ TreeCountContract`.**  The residual
as stated in `PenroseDCContract` (guard only `a ≠ b`) is not inhabitable: at
`n = 0, (a,b) = (0,1), rest = []`, truncated `Nat` subtraction makes
`treeCount 0 [(0,1)] = 1` while
`treeCount 0 [] + treeCount 0 (contractEdges 0 1 []) = 1 + 1 = 2`, forcing
`1 = 2`.  (The genuine content is `treeCountContractGuarded`, guarded by
`a < b, b < n`.) -/
theorem treeCountContract_unguarded_false : ¬ PenroseDCContract.TreeCountContract := by
  intro h
  have hne : (0 : Nat) ≠ 1 := by decide
  have hcontra := h 0 0 1 [] hne
  revert hcontra
  decide

end YMGap.Continuum.TreeCountContractProof

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.TreeCountContractProof.length_filter_map
#print axioms YMGap.Continuum.TreeCountContractProof.decLen
#print axioms YMGap.Continuum.TreeCountContractProof.treeCount_cons_split
#print axioms YMGap.Continuum.TreeCountContractProof.treeCount_contract_as_filter
#print axioms YMGap.Continuum.TreeCountContractProof.treeCountContractGuarded
#print axioms YMGap.Continuum.TreeCountContractProof.treeCountContract_unguarded_false
