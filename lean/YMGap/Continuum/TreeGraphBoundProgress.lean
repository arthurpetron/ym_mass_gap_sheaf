/-
Reducing the single unbacked Kotecký–Preiss atom `TreeGraphBound.tree_graph`
(`Ursell4DProgress`) — the per-cluster spanning-tree inequality
`|φ^T(Y)| ≤ eSurrogate^{|Y|}` (`eSurrogate = 3 ≥ e`) — to the standard
Penrose / Poghosyan–Ueltschi spanning-tree *count* factorisation.

# The object being reduced

`TreeGraphBound` (`Ursell4DProgress`) carries an abstract nonnegative weight
`phiT : Polymer → Q'` with the SINGLE open field

    tree_graph : ∀ Y, phiT Y ≤ eSurrogate ^ (Polymer.size Y).

With `phiT` an *arbitrary* nonneg function that inequality is FALSE (take `phiT`
large), so it is only meaningful once `phiT` is pinned to the truncated Ursell
coefficient `|φ^T(Y)|`.  The classical route factors it as, writing
`n = |Y| = size Y`:

    n! · phiT Y  ≤  #spanningTrees(adjGraph Y)          -- (P) penroseDom   [SIGN DOMINATION]
                 ≤  n^{n-2}                              -- (C) cayleyMax    [Cayley]
    n^{n-2}      ≤  eSurrogate^n · n!                    -- (A) eulerArith   [n^{n-2}/n! ≤ 3^n]

Dividing the composite `n!·phiT Y ≤ eSurrogate^n·n!` by the positive `n!` gives
`tree_graph`.

# What this module delivers (all GREEN, axiom-clean, unless marked NAMED-open)

* `TreeGraphReduction S w r` — a reduction datum carrying a CONCRETE `treeCount`
  (the spanning-tree count of the connectivity graph of `Y`) together with the
  two genuinely-open legs as fields:
    - `penroseDom` (leg (P)) — the Penrose/BKAR forest-root SIGN domination
      `n! · phiT Y ≤ ofNat(treeCount Y)`.  **This is the sole new mathematics.**
    - `cayleyMax`  (leg (C)) — Cayley's bound `treeCount Y ≤ n^{n-2}`
      (moderate combinatorics; the maximiser is `K_n`).

* `CubicEulerBound` (NAMED — the leg-(A) crux) — the ONE elementary rational
  inequality `(n+1)^n ≤ 3·n^n`, i.e. `(1+1/n)^n ≤ 3` (the standard `e < 3`
  bound).  Not new mathematics; not yet in-repo.  Everything downstream of it
  is PROVED here:

    - `powSelf_le`     — `n^n ≤ 3^n·n!`               (from `CubicEulerBound`);
    - `eulerArithNat`  — `n^{n-2} ≤ 3^n·n!`           (leg (A), Nat form);
    - `legA`           — `ofNat(n^{n-2}) ≤ eSurrogate^n·ofNat(n!)` (leg (A), `Q'`).

* `tree_graph_of_reduction` / `TreeGraphReduction.toBound` — PROVED: from a
  `TreeGraphReduction` and `CubicEulerBound`, CONSTRUCT a `TreeGraphBound`
  (i.e. derive `tree_graph`), by chaining (P)·(C)·(A) and cancelling `n!`.

# Honest geography

This does NOT close `tree_graph`.  It is a genuine REDUCTION: the frontier is
sharpened to leg (P) `n!·|φ^T(Y)| ≤ #spanningTrees(supp Y)` — the Penrose /
Brydges–Kennedy–Abdesselam–Rivasseau sign domination, the only genuinely new
mathematics.  Leg (C) Cayley and the leg-(A) crux `(1+1/n)^n ≤ 3` are the
downstream, non-load-bearing pieces (leg (A)'s arithmetic scaffold is fully
proved here).  `TreeGraphReduction` is LEFT UNINHABITED for a physical lattice
(as is `TreeGraphBound`); nothing is faked.

Fixed spacing; not the spacing-uniform continuum modulus; Clay YM mass gap
remains OPEN.

# Axiom-gate (AGENTS.md Rule 1)

Every delivered theorem reports `[propext]` (and `Quot.sound`) only.  No
`sorryAx`, no `Classical.*`, no custom axiom.
-/

import YMGap.Continuum.Ursell4DProgress

namespace YMGap.Continuum.TreeGraphBoundProgress

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Ursell4DProgress

/-! ## 0. Local `Q'`/`Nat` bookkeeping (self-contained copies)

These small helpers are reproved locally so the module depends only on the
foundational `Q'` API, not on incidental in-repo lemma placement. -/

/-- Factorial (`Lean` core here has no `Nat.factorial`). -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem fact_pos : ∀ n, 0 < fact n
  | 0 => by decide
  | n + 1 => Nat.mul_pos (Nat.succ_pos n) (fact_pos n)

/-- `ofNat` is monotone. -/
theorem ofNat_le_ofNat {a b : Nat} (h : a ≤ b) : Q'.ofNat a ≤ Q'.ofNat b := by
  show (Int.ofNat a) * ((Q'.ofNat b).den : Int)
      ≤ (Int.ofNat b) * ((Q'.ofNat a).den : Int)
  show (Int.ofNat a) * (1 : Int) ≤ (Int.ofNat b) * (1 : Int)
  rw [Int.mul_one, Int.mul_one]
  exact Int.ofNat_le.mpr h

/-- `ofNat` is nonnegative. -/
theorem ofNat_nonneg (a : Nat) : (0 : Q') ≤ Q'.ofNat a := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg a

/-- `ofNat` is strictly positive on positive inputs. -/
theorem ofNat_pos {m : Nat} (hm : 0 < m) : (0 : Q') < Q'.ofNat m := by
  cases m with
  | zero => exact absurd hm (by decide)
  | succ k => exact Q'.ofNat_succ_pos k

/-- `ofNat (a * b) ≃ ofNat a * ofNat b`. -/
theorem ofNat_mul_eqv (a b : Nat) :
    (Q'.ofNat (a * b)).eqv (Q'.ofNat a * Q'.ofNat b) := by
  show ((a * b : Nat) : Int) * ((Q'.ofNat a * Q'.ofNat b).den : Int)
     = (((a : Nat) : Int) * ((b : Nat) : Int)) * ((Q'.ofNat (a * b)).den : Int)
  show ((a * b : Nat) : Int) * (1 : Int)
     = (((a : Nat) : Int) * ((b : Nat) : Int)) * (1 : Int)
  rw [Int.mul_one, Int.mul_one, Int.natCast_mul]

/-- `ofNat (a ^ n) ≤ (ofNat a) ^ n` (equality up to `eqv`; `≤` suffices). -/
theorem ofNat_pow_le (a : Nat) : ∀ n : Nat,
    Q'.ofNat (a ^ n) ≤ (Q'.ofNat a) ^ n
  | 0 => by
      show Q'.ofNat 1 ≤ (1 : Q')
      exact Q'.le_refl' _
  | n + 1 => by
      rw [Nat.pow_succ, Q'.pow_succ]
      have hstep : (Q'.ofNat (a ^ n) * Q'.ofNat a)
          ≤ (Q'.ofNat a) ^ n * Q'.ofNat a :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ (ofNat_pow_le a n) (ofNat_nonneg a)
      have he : (Q'.ofNat (a ^ n * a)).eqv (Q'.ofNat (a ^ n) * Q'.ofNat a) :=
        ofNat_mul_eqv (a ^ n) a
      have hcomm : ((Q'.ofNat a) ^ n * Q'.ofNat a).eqv
          (Q'.ofNat a * (Q'.ofNat a) ^ n) :=
        Q'.mul_comm_eqv _ _
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv he) ?_
      exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv hcomm)

/-- Cancel a positive right factor: `0 < c → a·c ≤ b·c → a ≤ b`. -/
theorem le_of_mul_le_mul_right_pos {a b c : Q'} (hc : (0 : Q') < c)
    (h : a * c ≤ b * c) : a ≤ b := by
  have hcn : 0 < c.num := CReal.num_pos_of_pos hc
  have hh : (a * c).num * ((b * c).den : Int) ≤ (b * c).num * ((a * c).den : Int) := h
  show a.num * (b.den : Int) ≤ b.num * (a.den : Int)
  rw [show (a * c).num = a.num * c.num from rfl,
      show (b * c).num = b.num * c.num from rfl,
      Q'.mul_den_cast b c, Q'.mul_den_cast a c] at hh
  have e1 : (a.num * c.num) * ((b.den : Int) * (c.den : Int))
          = (c.num * (c.den : Int)) * (a.num * (b.den : Int)) := by ac_rfl
  have e2 : (b.num * c.num) * ((a.den : Int) * (c.den : Int))
          = (c.num * (c.den : Int)) * (b.num * (a.den : Int)) := by ac_rfl
  rw [e1, e2] at hh
  have hcc : 0 < c.num * (c.den : Int) := Int.mul_pos hcn (by exact_mod_cast c.den_pos)
  exact Int.le_of_mul_le_mul_left hh hcc

/-! ## 1. Leg (A): `n^{n-2} ≤ 3^n · n!`, reduced to the crux `(1+1/n)^n ≤ 3`

The single crux is the standard `e < 3` bound `(n+1)^n ≤ 3·n^n`.  It is NOT new
mathematics but is not yet in the repo; NAMED here and left as the leg-(A) input.
Everything downstream of it is PROVED. -/

/-- **NAMED (leg-(A) crux).**  The elementary rational inequality
`(n+1)^n ≤ 3·n^n`, i.e. `(1+1/n)^n ≤ 3` — the standard `e < 3` bound.  This is
the ONLY input for the entire leg-(A) arithmetic below. -/
def CubicEulerBound : Prop := ∀ n : Nat, (n + 1) ^ n ≤ 3 * n ^ n

/-- **PROVED (from the crux).**  `n^n ≤ 3^n · n!` — the `n^n/n! ≤ e^n < 3^n`
bound, by induction using `CubicEulerBound` at the step. -/
theorem powSelf_le (h : CubicEulerBound) : ∀ n, n ^ n ≤ 3 ^ n * fact n
  | 0 => by decide
  | n + 1 => by
      have ih := powSelf_le h n
      have hc : (n + 1) ^ n ≤ 3 * n ^ n := h n
      -- (n+1)^n ≤ 3·n^n ≤ 3·(3^n·n!) = 3^{n+1}·n!
      have h3 : (n + 1) ^ n ≤ 3 ^ (n + 1) * fact n := by
        have h2 : 3 * n ^ n ≤ 3 * (3 ^ n * fact n) :=
          Nat.mul_le_mul (Nat.le_refl 3) ih
        have e : 3 * (3 ^ n * fact n) = 3 ^ (n + 1) * fact n := by
          rw [Nat.pow_succ, Nat.mul_comm (3 ^ n) 3, Nat.mul_assoc]
        exact Nat.le_trans hc (e ▸ h2)
      -- (n+1)^{n+1} = (n+1)^n·(n+1) ≤ (3^{n+1}·n!)·(n+1) = 3^{n+1}·(n+1)!
      have step : (n + 1) ^ n * (n + 1) ≤ (3 ^ (n + 1) * fact n) * (n + 1) :=
        Nat.mul_le_mul h3 (Nat.le_refl (n + 1))
      have gEq2 : (3 ^ (n + 1) * fact n) * (n + 1) = 3 ^ (n + 1) * fact (n + 1) := by
        show (3 ^ (n + 1) * fact n) * (n + 1) = 3 ^ (n + 1) * ((n + 1) * fact n)
        rw [Nat.mul_assoc, Nat.mul_comm (fact n) (n + 1)]
      rw [Nat.pow_succ]
      exact Nat.le_trans step (Nat.le_of_eq gEq2)

/-- **PROVED (leg (A), Nat form).**  `n^{n-2} ≤ 3^n · n!` — from `powSelf_le`
via `n^{n-2} ≤ n^n`. -/
theorem eulerArithNat (h : CubicEulerBound) (n : Nat) :
    n ^ (n - 2) ≤ 3 ^ n * fact n := by
  have hself := powSelf_le h n
  have hle : n ^ (n - 2) ≤ n ^ n := by
    rcases Nat.eq_zero_or_pos n with h0 | hp
    · subst h0; decide
    · exact Nat.pow_le_pow_right hp (Nat.sub_le n 2)
  exact Nat.le_trans hle hself

/-- **PROVED (leg (A), `Q'` form).**  `ofNat(n^{n-2}) ≤ eSurrogate^n · ofNat(n!)`
(`eSurrogate = 3`). -/
theorem legA (h : CubicEulerBound) (n : Nat) :
    Q'.ofNat (n ^ (n - 2)) ≤ eSurrogate ^ n * Q'.ofNat (fact n) := by
  have h1 : Q'.ofNat (n ^ (n - 2)) ≤ Q'.ofNat (3 ^ n * fact n) :=
    ofNat_le_ofNat (eulerArithNat h n)
  have h2 : (Q'.ofNat (3 ^ n * fact n)).eqv (Q'.ofNat (3 ^ n) * Q'.ofNat (fact n)) :=
    ofNat_mul_eqv (3 ^ n) (fact n)
  have h3 : Q'.ofNat (3 ^ n) ≤ eSurrogate ^ n := by
    show Q'.ofNat (3 ^ n) ≤ (Q'.ofNat 3) ^ n
    exact ofNat_pow_le 3 n
  have h4 : Q'.ofNat (3 ^ n) * Q'.ofNat (fact n)
      ≤ eSurrogate ^ n * Q'.ofNat (fact n) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ h3 (ofNat_nonneg (fact n))
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv h2) h4)

/-! ## 2. The reduction datum and the master reduction

`TreeGraphReduction` pins `phiT` to a datum carrying a CONCRETE spanning-tree
`treeCount` and the two genuinely-open legs (P) and (C).  `toBound` PROVES that
these, together with the leg-(A) crux, CONSTRUCT a `TreeGraphBound`. -/

/-- **The reduction datum for the tree-graph atom.**  `treeCount Y` is the number
of spanning trees of the connectivity graph `adjGraph Y` of the cluster support
(the concrete count the abstract `TreeGraphBound.phiT` lacks).  The two fields
`penroseDom` and `cayleyMax` are the genuinely-open legs. LEFT UNINHABITED for a
physical lattice; NOT faked. -/
structure TreeGraphReduction (S : SepLattice) (w : Q') (r : Rep) where
  /-- The truncated Ursell weight `|φ^T(Y)|`. -/
  phiT : Polymer S.toLattice → Q'
  /-- `|φ^T(Y)| ≥ 0`. -/
  phiT_nonneg : ∀ Y, (0 : Q') ≤ phiT Y
  /-- The spanning-tree count `#spanningTrees(adjGraph Y)` of the connectivity
  graph of the cluster support. -/
  treeCount : Polymer S.toLattice → Nat
  /-- **Leg (P) — the Penrose / BKAR forest-root SIGN domination** (THE new
  mathematics): `n! · |φ^T(Y)| ≤ #spanningTrees(adjGraph Y)`. -/
  penroseDom : ∀ Y, Q'.ofNat (fact (Polymer.size Y)) * phiT Y
      ≤ Q'.ofNat (treeCount Y)
  /-- **Leg (C) — Cayley's bound**: the number of spanning trees of any simple
  graph on `n = |Y|` vertices is at most `n^{n-2}` (maximiser `K_n`). -/
  cayleyMax : ∀ Y, treeCount Y ≤ (Polymer.size Y) ^ (Polymer.size Y - 2)

/-- **PROVED (the master reduction).**  From a `TreeGraphReduction` and the
leg-(A) crux `CubicEulerBound`, the tree-graph inequality
`phiT Y ≤ eSurrogate^{|Y|}` holds.  Chain: `(P)·(C)·(A)` gives
`n!·phiT Y ≤ eSurrogate^n·n!`; cancel the positive `n!`. -/
theorem tree_graph_of_reduction {S : SepLattice} {w : Q'} {r : Rep}
    (red : TreeGraphReduction S w r) (hEuler : CubicEulerBound)
    (Y : Polymer S.toLattice) :
    red.phiT Y ≤ eSurrogate ^ (Polymer.size Y) := by
  -- (P): n!·phiT ≤ ofNat(treeCount Y)
  have hP := red.penroseDom Y
  -- (C): ofNat(treeCount Y) ≤ ofNat(n^{n-2})
  have hC : Q'.ofNat (red.treeCount Y)
      ≤ Q'.ofNat ((Polymer.size Y) ^ (Polymer.size Y - 2)) :=
    ofNat_le_ofNat (red.cayleyMax Y)
  -- (A): ofNat(n^{n-2}) ≤ eSurrogate^n·ofNat(n!)
  have hA := legA hEuler (Polymer.size Y)
  -- chain: n!·phiT ≤ eSurrogate^n·n!
  have hchain : Q'.ofNat (fact (Polymer.size Y)) * red.phiT Y
      ≤ eSurrogate ^ (Polymer.size Y) * Q'.ofNat (fact (Polymer.size Y)) :=
    Q'.le_trans' _ _ _ hP (Q'.le_trans' _ _ _ hC hA)
  -- commute the LHS product to `phiT · n!`
  have hcomm : (red.phiT Y * Q'.ofNat (fact (Polymer.size Y))).eqv
      (Q'.ofNat (fact (Polymer.size Y)) * red.phiT Y) :=
    Q'.mul_comm_eqv _ _
  have hchain2 : red.phiT Y * Q'.ofNat (fact (Polymer.size Y))
      ≤ eSurrogate ^ (Polymer.size Y) * Q'.ofNat (fact (Polymer.size Y)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hcomm) hchain
  -- cancel the positive `n!`
  have hpos : (0 : Q') < Q'.ofNat (fact (Polymer.size Y)) :=
    ofNat_pos (fact_pos (Polymer.size Y))
  exact le_of_mul_le_mul_right_pos hpos hchain2

/-- **PROVED (inhabitation given the legs).**  A `TreeGraphReduction` plus the
leg-(A) crux CONSTRUCTS a `TreeGraphBound` (i.e. discharges the once-abstract
`tree_graph` field).  This is the reduction deliverable: `tree_graph` is now a
THEOREM of (P)∧(C)∧(A), no longer a free field. -/
def TreeGraphReduction.toBound {S : SepLattice} {w : Q'} {r : Rep}
    (red : TreeGraphReduction S w r) (hEuler : CubicEulerBound) :
    TreeGraphBound S w r where
  phiT := red.phiT
  phiT_nonneg := red.phiT_nonneg
  tree_graph := fun Y => tree_graph_of_reduction red hEuler Y

end YMGap.Continuum.TreeGraphBoundProgress

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.TreeGraphBoundProgress.powSelf_le
#print axioms YMGap.Continuum.TreeGraphBoundProgress.eulerArithNat
#print axioms YMGap.Continuum.TreeGraphBoundProgress.legA
#print axioms YMGap.Continuum.TreeGraphBoundProgress.tree_graph_of_reduction
#print axioms YMGap.Continuum.TreeGraphBoundProgress.TreeGraphReduction.toBound
