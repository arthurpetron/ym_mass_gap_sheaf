/-
# Leg (C), de-risked: the tree-graph atom needs only the LOOSE count bound `n^{n-1}`.

`Continuum/TreeGraphBoundProgress.lean` reduces the tree-graph atom `tree_graph`
(`|φ^T(Y)| ≤ eSurrogate^{|Y|}`) to the chain `(P)·(C)·(A)` whose leg (C) is the
Cayley bound `treeCount Y ≤ n^{n-2}` (`CayleyMaxBound.CayleyCountBound`, provable
only by the full **Prüfer bijection** — an injection PLUS a decoder proving
surjectivity onto `Fin(n-2) → Fin n`).

## What this module observes and delivers (all GREEN, axiom-clean)

The exponent `n-2` in leg (C) is **not load-bearing**: the downstream arithmetic
`legA` derives `n^{n-2} ≤ eSurrogate^n·n!` only via `n^{n-2} ≤ n^n ≤ 3^n·n!`
(`powSelf_le`), and the *same* `powSelf_le` already gives `n^{n-1} ≤ n^n ≤ 3^n·n!`.
So the WEAKER count bound

    treeCount Y  ≤  n^{n-1}                              -- (C′) loose Cayley

feeds the identical final inequality `phiT Y ≤ eSurrogate^{|Y|}`.  The loose bound
`n^{n-1}` needs only a **parent-map injection** (root the spanning tree at `0`,
send each non-root vertex to its neighbour towards the root — an injection into
`Fin(n-1) → Fin n`, no decoder / surjectivity), which is strictly less than the
Prüfer bijection.  This module therefore *de-risks* leg (C):

  * `eulerArithNat_loose` / `legA_loose` — **PROVED**: `n^{n-1} ≤ 3^n·n!` and its
    `Q'` form (reusing the already-proved `powSelf_le`).
  * `TreeGraphReductionLoose` + `toBoundLoose` — **PROVED**: a reduction datum
    carrying the WEAKER leg (C′) `treeCount Y ≤ n^{n-1}` (with the same (P) and
    (A)) still CONSTRUCTS a `TreeGraphBound` (discharges `tree_graph`).
  * `CayleyLooseBound` (NAMED-open, the de-risked leg (C′) residual) — the loose
    Cayley bound over the concrete `treeCount`, under the same `SimpleEdges`
    hypothesis.  Strictly weaker than `CayleyCountBound`:
    `cayleyCountBound_imp_loose` **PROVES** `CayleyCountBound → CayleyLooseBound`.
  * `pow_sub_two_le_sub_one` / `pow_sub_one_le_self` — **PROVED**: the exponent
    monotonicity `n^{n-2} ≤ n^{n-1} ≤ n^n` making the weakening explicit.
  * `CayleyPin.cayleyMaxLoose_field` — **PROVED**: from `CayleyLooseBound` + a
    `CayleyPin`, the exact loose leg-(C′) field for every polymer.

## Honest geography

This does NOT close leg (C).  It REDUCES the residual from the tight Cayley bound
`n^{n-2}` (Prüfer bijection) to the strictly weaker `n^{n-1}` (parent-map
injection only), and proves the entire downstream tolerates the weaker bound.
`CayleyLooseBound` is LEFT UNINHABITED for a physical lattice; nothing is faked.
`TreeGraphReductionLoose` is likewise left uninhabited (its (P) leg `penroseDom`
is the still-open Penrose/Ursell content of `PenroseDomInduction`).

Fixed spacing; not the spacing-uniform continuum modulus; Clay YM mass gap
remains OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1/6/8)

Mathlib-free; only `Q'` / `Nat` / `List` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `sorry` / new `axiom`.  All witnesses are `Type`-level data.
Every load-bearing declaration is gated with `#print axioms`.
-/

import YMGap.Continuum.CayleyMaxBound

namespace YMGap.Continuum.CayleyLooseReduction

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Ursell4DProgress
open YMGap.Continuum.TreeGraphBoundProgress
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.CayleyMaxBound

/-! ## 1. Exponent monotonicity: `n^{n-2} ≤ n^{n-1} ≤ n^n`

The explicit statement that leg (C′) `n^{n-1}` is weaker than the tight Cayley
bound `n^{n-2}` and still `≤ n^n` (so the same `powSelf_le` closes the
arithmetic). -/

/-- **PROVED.**  `n^{n-2} ≤ n^{n-1}` — leg (C′) is weaker than the tight bound. -/
theorem pow_sub_two_le_sub_one (n : Nat) : n ^ (n - 2) ≤ n ^ (n - 1) := by
  rcases Nat.eq_zero_or_pos n with h0 | hp
  · subst h0; decide
  · exact Nat.pow_le_pow_right hp (by omega)

/-- **PROVED.**  `n^{n-1} ≤ n^n` — leg (C′) is `≤ n^n`, so `powSelf_le` closes it. -/
theorem pow_sub_one_le_self (n : Nat) : n ^ (n - 1) ≤ n ^ n := by
  rcases Nat.eq_zero_or_pos n with h0 | hp
  · subst h0; decide
  · exact Nat.pow_le_pow_right hp (Nat.sub_le n 1)

/-! ## 2. Leg (A) for the loose exponent: `n^{n-1} ≤ 3^n·n!` (PROVED)

Reuses the already-proved `powSelf_le : n^n ≤ 3^n·n!`. -/

/-- **PROVED (leg (A) for the loose exponent, `Nat` form).**  `n^{n-1} ≤ 3^n·n!`,
from `powSelf_le` via `n^{n-1} ≤ n^n`. -/
theorem eulerArithNat_loose (h : CubicEulerBound) (n : Nat) :
    n ^ (n - 1) ≤ 3 ^ n * fact n :=
  Nat.le_trans (pow_sub_one_le_self n) (powSelf_le h n)

/-- **PROVED (leg (A) for the loose exponent, `Q'` form).**
`ofNat(n^{n-1}) ≤ eSurrogate^n · ofNat(n!)`.  Mirrors `legA`. -/
theorem legA_loose (h : CubicEulerBound) (n : Nat) :
    Q'.ofNat (n ^ (n - 1)) ≤ eSurrogate ^ n * Q'.ofNat (fact n) := by
  have h1 : Q'.ofNat (n ^ (n - 1)) ≤ Q'.ofNat (3 ^ n * fact n) :=
    ofNat_le_ofNat (eulerArithNat_loose h n)
  have h2 : (Q'.ofNat (3 ^ n * fact n)).eqv (Q'.ofNat (3 ^ n) * Q'.ofNat (fact n)) :=
    ofNat_mul_eqv (3 ^ n) (fact n)
  have h3 : Q'.ofNat (3 ^ n) ≤ eSurrogate ^ n := by
    show Q'.ofNat (3 ^ n) ≤ (Q'.ofNat 3) ^ n
    exact ofNat_pow_le 3 n
  have h4 : Q'.ofNat (3 ^ n) * Q'.ofNat (fact n)
      ≤ eSurrogate ^ n * Q'.ofNat (fact n) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ h3 (ofNat_nonneg (fact n))
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv h2) h4)

/-! ## 3. The de-risked reduction datum and master reduction

`TreeGraphReductionLoose` is `TreeGraphReduction` with the leg-(C) field weakened
to `n^{n-1}`.  `toBoundLoose` PROVES it still constructs a `TreeGraphBound`. -/

/-- **The de-risked reduction datum for the tree-graph atom.**  Identical to
`TreeGraphReduction` except leg (C) is the WEAKER `treeCount Y ≤ n^{n-1}`
(parent-map injection, not the full Prüfer bijection).  LEFT UNINHABITED for a
physical lattice; NOT faked (its `penroseDom` is the open Penrose/Ursell content). -/
structure TreeGraphReductionLoose (S : SepLattice) (w : Q') (r : Rep) where
  /-- The truncated Ursell weight `|φ^T(Y)|`. -/
  phiT : Polymer S.toLattice → Q'
  /-- `|φ^T(Y)| ≥ 0`. -/
  phiT_nonneg : ∀ Y, (0 : Q') ≤ phiT Y
  /-- The spanning-tree count of the connectivity graph of the cluster support. -/
  treeCount : Polymer S.toLattice → Nat
  /-- **Leg (P) — the Penrose / BKAR forest-root SIGN domination**:
  `n! · |φ^T(Y)| ≤ #spanningTrees(adjGraph Y)`. -/
  penroseDom : ∀ Y, Q'.ofNat (fact (Polymer.size Y)) * phiT Y
      ≤ Q'.ofNat (treeCount Y)
  /-- **Leg (C′) — the LOOSE Cayley bound**: `#spanningTrees ≤ n^{n-1}` (weaker
  than the tight `n^{n-2}`; only a parent-map injection is needed). -/
  cayleyMaxLoose : ∀ Y, treeCount Y ≤ (Polymer.size Y) ^ (Polymer.size Y - 1)

/-- **PROVED (the de-risked master reduction).**  From a `TreeGraphReductionLoose`
and the (proved) leg-(A) crux `CubicEulerBound`, the tree-graph inequality
`phiT Y ≤ eSurrogate^{|Y|}` holds.  Same chain as `tree_graph_of_reduction`, using
`legA_loose` at the (A) step. -/
theorem tree_graph_of_reduction_loose {S : SepLattice} {w : Q'} {r : Rep}
    (red : TreeGraphReductionLoose S w r) (hEuler : CubicEulerBound)
    (Y : Polymer S.toLattice) :
    red.phiT Y ≤ eSurrogate ^ (Polymer.size Y) := by
  have hP := red.penroseDom Y
  have hC : Q'.ofNat (red.treeCount Y)
      ≤ Q'.ofNat ((Polymer.size Y) ^ (Polymer.size Y - 1)) :=
    ofNat_le_ofNat (red.cayleyMaxLoose Y)
  have hA := legA_loose hEuler (Polymer.size Y)
  have hchain : Q'.ofNat (fact (Polymer.size Y)) * red.phiT Y
      ≤ eSurrogate ^ (Polymer.size Y) * Q'.ofNat (fact (Polymer.size Y)) :=
    Q'.le_trans' _ _ _ hP (Q'.le_trans' _ _ _ hC hA)
  have hcomm : (red.phiT Y * Q'.ofNat (fact (Polymer.size Y))).eqv
      (Q'.ofNat (fact (Polymer.size Y)) * red.phiT Y) :=
    Q'.mul_comm_eqv _ _
  have hchain2 : red.phiT Y * Q'.ofNat (fact (Polymer.size Y))
      ≤ eSurrogate ^ (Polymer.size Y) * Q'.ofNat (fact (Polymer.size Y)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hcomm) hchain
  have hpos : (0 : Q') < Q'.ofNat (fact (Polymer.size Y)) :=
    ofNat_pos (fact_pos (Polymer.size Y))
  exact le_of_mul_le_mul_right_pos hpos hchain2

/-- **PROVED (inhabitation given the loose legs).**  A `TreeGraphReductionLoose`
plus the (proved) leg-(A) crux CONSTRUCTS a `TreeGraphBound`.  This is the
de-risked reduction deliverable: `tree_graph` is a THEOREM of (P)∧(C′)∧(A), where
(C′) is the strictly weaker loose count bound. -/
def TreeGraphReductionLoose.toBoundLoose {S : SepLattice} {w : Q'} {r : Rep}
    (red : TreeGraphReductionLoose S w r) (hEuler : CubicEulerBound) :
    TreeGraphBound S w r where
  phiT := red.phiT
  phiT_nonneg := red.phiT_nonneg
  tree_graph := fun Y => tree_graph_of_reduction_loose red hEuler Y

/-! ## 4. Leg (C′) proper — the loose count residual, strictly weaker than Cayley

`CayleyLooseBound` is the loose Cayley bound over the concrete `treeCount`.  It is
implied by the tight `CayleyCountBound`, so it is genuinely WEAKER: whatever
proves the tight bound proves this, and only the loose bound is needed downstream.
The `SimpleEdges` hypothesis remains load-bearing (the multigraph counterexample
`treeCount 2 [(0,1),(0,1)] = 2` from `CayleyMaxBound` gives `2 = n^{n-1}` — the
loose bound is TIGHT for that multigraph, `n^{n-2} = 1` fails, so `n^{n-1}` is the
minimal exponent robust to the parent-map non-injectivity on repeated edges). -/

/-- **NAMED (leg (C′), the de-risked residual).**  The loose Cayley bound for the
concrete `treeCount`, under `SimpleEdges`.  Strictly weaker than `CayleyCountBound`
(`cayleyCountBound_imp_loose`).  Provable by the parent-map injection
`treeSubset ↪ (Fin (n-1) → Fin n)` (root at `0`; no decoder needed), strictly less
than the Prüfer bijection.  LEFT UNINHABITED — the single de-risked residual. -/
def CayleyLooseBound : Prop :=
  ∀ (n : Nat) (edges : List Edge),
    SimpleEdges n edges → treeCount n edges ≤ n ^ (n - 1)

/-- **PROVED.**  `CayleyCountBound → CayleyLooseBound`: the loose residual is
strictly weaker, so this reduction never *strengthens* the leg-(C) obligation. -/
theorem cayleyCountBound_imp_loose (h : CayleyCountBound) : CayleyLooseBound := by
  intro n edges hsimple
  exact Nat.le_trans (h n edges hsimple) (pow_sub_two_le_sub_one n)

/-! ## 5. The pin: reducing the loose leg-(C′) field to `CayleyLooseBound` -/

variable {L : Lattice}

/-- **`cayleyMaxLoose_field` — leg (C′), reduced (PROVED from the loose residual +
the pin).**  From `CayleyLooseBound` and a `CayleyPin`, the pinned tree count of
every polymer satisfies `treeCountF Y ≤ (Polymer.size Y)^(Polymer.size Y - 1)` —
exactly the `cayleyMaxLoose` field of `TreeGraphReductionLoose`.  Same proof shape
as `CayleyPin.cayleyMax_field`. -/
theorem CayleyPin.cayleyMaxLoose_field (P : CayleyPin L) (hCay : CayleyLooseBound)
    (Y : Polymer L) :
    P.treeCountF Y ≤ (Polymer.size Y) ^ (Polymer.size Y - 1) := by
  rw [P.countPin Y]
  have hc : treeCount (P.adjN Y) (P.adjE Y) ≤ (P.adjN Y) ^ (P.adjN Y - 1) :=
    hCay (P.adjN Y) (P.adjE Y) (P.adjSimple Y)
  rw [P.adjN_eq Y] at hc ⊢
  exact hc

end YMGap.Continuum.CayleyLooseReduction

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CayleyLooseReduction.pow_sub_two_le_sub_one
#print axioms YMGap.Continuum.CayleyLooseReduction.pow_sub_one_le_self
#print axioms YMGap.Continuum.CayleyLooseReduction.eulerArithNat_loose
#print axioms YMGap.Continuum.CayleyLooseReduction.legA_loose
#print axioms YMGap.Continuum.CayleyLooseReduction.tree_graph_of_reduction_loose
#print axioms YMGap.Continuum.CayleyLooseReduction.TreeGraphReductionLoose.toBoundLoose
#print axioms YMGap.Continuum.CayleyLooseReduction.cayleyCountBound_imp_loose
#print axioms YMGap.Continuum.CayleyLooseReduction.CayleyPin.cayleyMaxLoose_field
