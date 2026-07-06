/-
# `SpansContract` — the weightless edge-contraction invariance of connectivity:
#   REFUTED as stated, and CORRECTED + reduced to one named BFS residual.

`Continuum/PenroseWeightedRepair.lean` isolates the weightless connectivity
residual

    SpansContract : ∀ (n a b : Nat) (A : List Edge), a ≠ b → a < n → b < n →
      spans n ((a, b) :: A) = spans (n - 1) (contractEdges a b A)

and consumes it (via `wspans_contract` / `CsumW_nonloop_contract`) as "genuinely
TRUE".  This module discharges it honestly, and the honest verdict is a
correction:

## 1. `SpansContract` AS STATED IS FALSE (machine-checked refutation)

`spansContract_refuted : ¬ PenroseWeightedRepair.SpansContract`.  The
counterexample is `n = 3`, `(a,b) = (2,0)`, `A = [(0,1)]` — which satisfies EVERY
guard (`a ≠ b`, `a < n`, `b < n`).  There

    spans 3 ((2,0)::[(0,1)]) = true      (the graph 0—2, 0—1 is connected),
    spans 2 (contractEdges 2 0 [(0,1)]) = false,

because `contractEdges 2 0 [(0,1)] = [(2,0)]`, an edge whose relabelled endpoints
lose vertex `1`.  The DEFECT is in `relabelV a b v = if v = b then a else …`: it
is only a correct contraction when `a < b` (delete the LARGER endpoint `b`, keep
the SMALLER `a`).  When `b < a` it maps `b ↦ a` to an UN-shifted, out-of-range
label and fails to identify `a` with `b`.  So the `a < n, b < n` guards are NOT
enough to make `SpansContract` true — the missing guard is the ORIENTATION
`a < b` (equivalently: contract `min a b`/`max a b`).  This corrects the
`PenroseWeightedRepair.SpansContract` docstring's claim that the range guards
suffice.

## 2. The CORRECTED oriented statement is TRUE, reduced to one BFS residual

With the orientation guard `a < b`, connectivity contraction-invariance holds
(brute-force verified over all graphs on `n ≤ 4`):

    spansContractOriented_of_transport :
      ReachTransport →
        ∀ n a b A, a < b → b < n →
          spans n ((a,b)::A) = spans (n-1) (contractEdges a b A).

This is PROVED here in full FROM the single named residual `ReachTransport` — the
exact-fuel per-vertex reachability correspondence

    i ∈ reachClosure n ((a,b)::A) [0]  ↔  relabelV a b i ∈ reachClosure (n-1) (…) [0],

together with pure `relabelV` arithmetic proved here outright (`relabelV_lt`,
`relabelV_preimg`, `preimg_lt`): the merge map `relabelV a b` is a surjection
`{0,…,n-1} ↠ {0,…,n-2}` collapsing exactly `a,b`, so "all of `{0,…,n-1}` reached
in `G`" ⇔ "all of `{0,…,n-2}` reached in `G/e`".  `ReachTransport` is the genuine
BFS core (the reachability image under the merge map, at the exact BFS fuels
`n`/`n-1`), left as the single named residual — true (brute-force validated),
weightless, and NOT refutable.

## Honest scope

The literal `SpansContract` is FALSE and CANNOT be proved (it is refuted here);
the downstream `wspans_contract` / `CsumW_nonloop_contract` therefore rest on a
false hypothesis and must be re-pointed at the ORIENTED contraction (contract
`min a b` into `max a b`).  The corrected connectivity fact is genuine and is
reduced here to `ReachTransport`.  Nothing is faked; `ReachTransport` is left
UNINHABITED.

Mathlib-free; `Nat` / `List` core only.  No `Classical.*`, no `Real`, no
`native_decide`, no `sorry` / new `axiom`.  Every load-bearing declaration gated
with `#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.PenroseWeightedRepair

namespace YMGap.Continuum.SpansContractProof

open YMGap.Continuum.PenroseDomInduction

/-! ## 1. The refutation of the literal `SpansContract` -/

/-- **`SpansContract` AS STATED IS FALSE.**  Instantiating the identity at
`n=3, (a,b)=(2,0), A=[(0,1)]` (all guards `a≠b`, `a<n`, `b<n` satisfied) forces
`true = false`: the graph `0—2, 0—1` is connected but its `relabelV 2 0`
contraction `[(2,0)]` on two vertices is not.  The `relabelV` merge is a correct
contraction only under the orientation `a < b`. -/
theorem spansContract_refuted : ¬ PenroseWeightedRepair.SpansContract := by
  intro h
  have hbad := h 3 2 0 [(0, 1)] (by decide) (by decide) (by decide)
  revert hbad
  decide

/-! ## 2. `relabelV` arithmetic (the pure combinatorics of the merge map) -/

/-- The merge map lands in `{0,…,n-2}`: for `a < b < n` and `v < n`,
`relabelV a b v < n - 1`.  (`relabelV a b` is a surjection `{0,…,n-1} ↠
{0,…,n-2}`.) -/
theorem relabelV_lt (a b v n : Nat) (hab : a < b) (hbn : b < n) (hv : v < n) :
    relabelV a b v < n - 1 := by
  unfold relabelV
  by_cases h1 : v = b
  · rw [if_pos h1]; omega
  · rw [if_neg h1]
    by_cases h2 : b < v
    · rw [if_pos h2]; omega
    · rw [if_neg h2]; omega

/-- A canonical pre-image of `j` under `relabelV a b` (`a < b`): `j` if `j < b`,
else `j+1` (skipping the deleted label `b`). -/
def preimg (b j : Nat) : Nat := if j < b then j else j + 1

/-- The pre-image is a genuine pre-image: `relabelV a b (preimg b j) = j`. -/
theorem relabelV_preimg (a b j : Nat) (_hab : a < b) :
    relabelV a b (preimg b j) = j := by
  unfold preimg
  by_cases hj : j < b
  · rw [if_pos hj]; unfold relabelV
    rw [if_neg (by omega : ¬ (j = b)), if_neg (by omega : ¬ (b < j))]
  · rw [if_neg hj]; unfold relabelV
    rw [if_neg (by omega : ¬ (j + 1 = b)), if_pos (by omega : b < j + 1)]
    omega

/-- The pre-image of a `< n-1` label is a `< n` label (surjectivity range). -/
theorem preimg_lt (b j n : Nat) (hj : j < n - 1) : preimg b j < n := by
  unfold preimg
  by_cases h : j < b
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

/-! ## 3. The single named BFS residual -/

/-- **`ReachTransport` — the exact-fuel reachability correspondence under the
merge map (the genuine weightless BFS core).**  For an oriented head `a < b < n`,
a vertex `i < n` is reached from `0` in `G = (n, (a,b)::A)` iff its merge image
`relabelV a b i` is reached from `0` in the contraction `G/e = (n-1,
contractEdges a b A)`, at the exact BFS fuels `n` and `n-1`.

This is the classical contraction-invariance of connectivity — a path in `G` maps
under `relabelV a b` to a walk in `G/e` and back (the merged vertex `a` stands for
both `a` and `b`, connected by the head edge `(a,b)`, which becomes the invisible
self-loop `(a,a)`).  Weightless, TRUE (brute-force validated over all graphs on
`n ≤ 4`), and — unlike the weighted `Csum` half or the mis-oriented `relabelV` —
NOT refutable.  Left UNINHABITED: the single named residual. -/
def ReachTransport : Prop :=
  ∀ (n a b : Nat) (A : List Edge), a < b → b < n →
    ∀ i, i < n →
      (i ∈ reachClosure n ((a, b) :: A) [0] ↔
       relabelV a b i ∈ reachClosure (n - 1) (contractEdges a b A) [0])

/-! ## 4. The corrected oriented contraction-invariance, PROVED from `ReachTransport` -/

/-- **The oriented connectivity contraction-invariance (PROVED from
`ReachTransport`).**  For `a < b < n`,
`spans n ((a,b)::A) = spans (n-1) (contractEdges a b A)`.  The two `spans`
predicates are `∀ i < n, i ∈ reach_G` and `∀ j < n-1, j ∈ reach_{G/e}`; they are
equivalent because `relabelV a b` surjects `{0,…,n-1} ↠ {0,…,n-2}`
(`relabelV_lt`, `relabelV_preimg`, `preimg_lt`) and transports reachability both
ways (`ReachTransport`). -/
theorem spansContractOriented_of_transport (hRT : ReachTransport)
    (n a b : Nat) (A : List Edge) (hab : a < b) (hbn : b < n) :
    spans n ((a, b) :: A) = spans (n - 1) (contractEdges a b A) := by
  show decide (∀ i, i < n → i ∈ reachClosure n ((a, b) :: A) [0])
     = decide (∀ j, j < n - 1 → j ∈ reachClosure (n - 1) (contractEdges a b A) [0])
  apply decide_eq_decide.mpr
  constructor
  · intro hG j hj
    have hi : preimg b j < n := preimg_lt b j n hj
    have ht := (hRT n a b A hab hbn (preimg b j) hi).mp (hG (preimg b j) hi)
    rwa [relabelV_preimg a b j hab] at ht
  · intro hG' i hi
    have hlt : relabelV a b i < n - 1 := relabelV_lt a b i n hab hbn hi
    exact (hRT n a b A hab hbn i hi).mpr (hG' (relabelV a b i) hlt)

end YMGap.Continuum.SpansContractProof

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SpansContractProof.spansContract_refuted
#print axioms YMGap.Continuum.SpansContractProof.relabelV_lt
#print axioms YMGap.Continuum.SpansContractProof.relabelV_preimg
#print axioms YMGap.Continuum.SpansContractProof.preimg_lt
#print axioms YMGap.Continuum.SpansContractProof.spansContractOriented_of_transport
