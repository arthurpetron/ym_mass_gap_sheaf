/-
# The Penrose tree-graph domination `penroseDom`, reduced to the deletion–contraction
#   recursor + the Ursell coefficient identity, over a GENUINELY-PINNED object.

`Continuum/TreeGraphBoundProgress.lean` carries the Kotecký–Preiss atom
`penroseDom` as an ABSTRACT field of `TreeGraphReduction`:

    penroseDom : ∀ Y, ofNat (fact (size Y)) · phiT Y ≤ ofNat (treeCount Y)

with `phiT` an *arbitrary* nonnegative function and `treeCount` an *arbitrary*
`Nat`.  With `phiT` free the inequality is FALSE (take `phiT` huge), so the atom
carries content only once `phiT` is pinned to `|φ^T(Y)|` and `treeCount` to the
spanning-tree count of the connectivity graph.  This module supplies the pinning
and reduces `penroseDom` to two honest named residuals, of which one — the
Penrose spanning-tree inequality `|C(G)| ≤ τ(G)` — is here *proved by
deletion–contraction* modulo a single named recursor.

## The genuine objects (NOT abstract fields)

For a fixed **repulsive** weight `w : Nat → Nat → Q'` (`-1 ≤ w a b ≤ 0`,
the hard-core Mayer setting; at strong coupling `ρ₄ = 15/32` the pair factor
lies in `[-1,0]`), and a finite weighted graph `(n, edges)` with `edges :
List (Nat × Nat)` over the vertex set `{0,…,n-1}`, we DEFINE, over the
Mathlib-free `sublists` power-set enumeration:

  * `edgeProd w A`   — `∏_{e ∈ A} w e` (an edge-subset weight);
  * `spans n A`      — the genuine connectivity `Bool`: every vertex `< n` is
    reachable from `0` in the graph `(n, A)` (bounded BFS `reachClosure`);
  * `Csum w n edges` — the **signed connected-spanning-subgraph sum**
    `C(G) = Σ_{A ⊆ edges, spans n A} ∏_{e∈A} w e`;
  * `treeCount n edges` — the **spanning-tree count**
    `τ(G) = #{A ⊆ edges : spans n A ∧ |A| = n-1}`.

These are concrete computable objects; the bound `|C| ≤ τ` is genuinely false
for the wrong weights (it needs repulsivity), so the target is non-vacuous.

## What is PROVED here (all axiom-clean)

  * `abs_mul_le_of_factor` — the analytic heart: `-1 ≤ u ≤ 1`, `|C| ≤ M ⟹
    |u·C| ≤ M` (handles BOTH the non-loop factor `w e` and the loop factor
    `1 + w e`, the repulsivity that survives contraction-created loops).
  * `penrose_base` — the base case `|C(n,[])| ≤ τ(n,[])` (single vertex ⇒
    `C=τ=1`; ≥2 vertices with no edges ⇒ disconnected ⇒ `C=τ=0`).
  * `penroseIneq` — the **Penrose inequality** `|C(G)| ≤ τ(G)` for every graph,
    PROVED by well-founded (fuel) induction on `|edges|` from the base case, the
    analytic step, and the deletion–contraction recursor `DCHyp`.
  * `penroseDom_of_pin` — the atom `penroseDom` for the pinned `phiT`, reduced
    to `DCHyp` + the Ursell identity `UrsellPin`.

## Named residuals (NOT faked, genuine provable-in-principle statements)

  * `DCHyp w` — the deletion–contraction identities for the CONCRETE `Csum` /
    `treeCount`:  on a non-loop head `e = (a,b)`,
    `C(G) ≃ C(G−e) + w e · C(G/e)` and `τ(G) = τ(G−e) + τ(G/e)`; on a loop head
    `C(G) ≃ (1 + w e)·C(G−e)` and `τ(G) = τ(G−e)`.  The `G−e` (delete) half is a
    definitional `sublists`-split; the `G/e` (contract) half is the classical
    contraction-invariance of connectivity/spanning-trees.  Left as ONE named
    obligation (the load-bearing combinatorial core).
  * `UrsellPin w` — the Ursell↔connected-graph coefficient identity
    `n!·phiT Y = |C(adjGraph Y)|` (pins `phiT`) together with the tree-count
    pin `treeCount Y = τ(adjGraph Y)`.

## Honest scope

Fixed-spacing strong-coupling combinatorics (`ρ₄ = 15/32`).  This is NOT the
spacing-uniform continuum modulus and does not bear on the Clay continuum limit.
`DCHyp` / `UrsellPin` are LEFT UNINHABITED; nothing is faked.

# Constructive contract (`lean/AGENTS.md` Rules 1/6/8)

Mathlib-free; only `Q'` / `Nat` / `List` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `sorry` / new `axiom`.  All witnesses are `Type`-level data.
Every load-bearing declaration is gated with `#print axioms` (permitted:
`propext` / `Quot.sound`).
-/

import YMGap.Constructive.CRealAbs
import YMGap.Continuum.TreeGraphBoundProgress

namespace YMGap.Continuum.PenroseDomInduction

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.TreeGraphBoundProgress

/-! ## 0. A local `Q'`/`Nat` bookkeeping helper -/

/-- `ofNat (i+j) ≃ ofNat i + ofNat j` (local copy of the `CauchyConv` lemma so
this module depends only on the foundational `Q'` API). -/
theorem ofNat_add_eqv (i j : Nat) :
    (Q'.ofNat (i + j)).eqv (Q'.ofNat i + Q'.ofNat j) := by
  show (Q'.ofNat (i + j)).num * ((Q'.ofNat i + Q'.ofNat j).den : Int)
     = (Q'.ofNat i + Q'.ofNat j).num * ((Q'.ofNat (i + j)).den : Int)
  have hd : ((Q'.ofNat i + Q'.ofNat j).den : Int) = (1 : Int) := by
    show (((1 * 1 - 1) + 1 : Nat) : Int) = (1 : Int)
    decide
  rw [hd]
  show ((↑(i + j) : Int)) * (1 : Int)
     = (((↑i : Int)) * (1 : Int) + ((↑j : Int)) * (1 : Int)) * (1 : Int)
  push_cast
  omega

/-! ## 1. The finite weighted graph and its two invariants -/

/-- An edge is an unordered pair of vertex labels (carried as an ordered `Nat`
pair; the connectivity below is symmetrised). -/
abbrev Edge : Type := Nat × Nat

/-- The Mathlib-free power-set enumeration (mirrors `AbstractPolymerXi.sublists`). -/
def sublists : List α → List (List α)
  | [] => [[]]
  | a :: l => sublists l ++ (sublists l).map (fun s => a :: s)

@[simp] theorem sublists_nil : sublists ([] : List α) = [[]] := rfl

/-- The edge-subset weight `∏_{e ∈ A} w e`. -/
def edgeProd (w : Nat → Nat → Q') (A : List Edge) : Q' :=
  A.foldr (fun e acc => w e.1 e.2 * acc) 1

/-! ### Connectivity via bounded BFS

`relax` performs one undirected relaxation pass of an edge list over a current
reachable set; `reachClosure n` iterates it `n` times (enough to reach the
fixpoint on `n` vertices).  `spans n A` tests that every vertex `< n` is in the
reachable set of `0`. -/

/-- Add `x` to `R` unless already present. -/
def addV (x : Nat) (R : List Nat) : List Nat := if x ∈ R then R else x :: R

/-- One undirected relaxation across a single edge. -/
def relaxEdge (e : Edge) (R : List Nat) : List Nat :=
  if e.1 ∈ R then addV e.2 R else if e.2 ∈ R then addV e.1 R else R

/-- One relaxation pass across the whole edge list. -/
def relax (A : List Edge) (R : List Nat) : List Nat := A.foldr relaxEdge R

/-- `n`-fold relaxation (BFS closure with fuel). -/
def reachClosure : Nat → List Edge → List Nat → List Nat
  | 0, _, R => R
  | k + 1, A, R => reachClosure k A (relax A R)

/-- On the empty edge list every relaxation is the identity. -/
theorem reachClosure_nil (k : Nat) (R : List Nat) :
    reachClosure k ([] : List Edge) R = R := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    show reachClosure k ([] : List Edge) (relax [] R) = R
    have h : relax ([] : List Edge) R = R := rfl
    rw [h]; exact ih R

/-- The genuine connectivity `Bool`: every vertex `< n` is reachable from `0`. -/
def spans (n : Nat) (A : List Edge) : Bool :=
  decide (∀ i, i < n → i ∈ reachClosure n A [0])

/-- If a no-edge graph spans then it has at most one vertex (`{0}` is the only
component). -/
theorem spans_nil_le_one {n : Nat} (h : spans n [] = true) : n ≤ 1 := by
  have hs : ∀ i, i < n → i ∈ reachClosure n ([] : List Edge) [0] :=
    of_decide_eq_true h
  cases n with
  | zero => omega
  | succ m =>
    cases m with
    | zero => omega
    | succ k =>
      have hm : (1 : Nat) ∈ reachClosure (k + 1 + 1) ([] : List Edge) [0] :=
        hs 1 (by omega)
      rw [reachClosure_nil] at hm
      exact absurd (List.mem_singleton.mp hm) (by decide)

/-- The **signed connected-spanning-subgraph sum** `C(G)`. -/
def Csum (w : Nat → Nat → Q') (n : Nat) (edges : List Edge) : Q' :=
  (sublists edges).foldr
    (fun A acc => if spans n A = true then edgeProd w A + acc else acc) 0

/-- The **spanning-tree count** `τ(G)`: connected spanning subgraphs with exactly
`n-1` edges. -/
def treeCount (n : Nat) (edges : List Edge) : Nat :=
  ((sublists edges).filter
    (fun A => spans n A && decide (A.length = n - 1))).length

/-! ### Contraction of the head edge -/

/-- Vertex relabelling for contracting `b` into `a`: send `b ↦ a` and shift every
label above `b` down by one (so the range collapses to `{0,…,n-2}`). -/
def relabelV (a b v : Nat) : Nat :=
  if v = b then a else if b < v then v - 1 else v

/-- Contract the head edge `(a,b)` in the tail `rest`. -/
def contractEdges (a b : Nat) (rest : List Edge) : List Edge :=
  rest.map (fun e => (relabelV a b e.1, relabelV a b e.2))

/-! ## 2. The analytic heart: the repulsive factor bound -/

/-- **The factor bound.**  If `-1 ≤ u ≤ 1` and `|C| ≤ M` then `|u·C| ≤ M`.
This is the single analytic step of the Penrose induction; it is what lets both
the non-loop factor `w e ∈ [-1,0] ⊆ [-1,1]` and the loop factor
`1 + w e ∈ [0,1] ⊆ [-1,1]` (the repulsivity that survives contraction-created
loops) pass the triangle bound. -/
theorem abs_mul_le_of_factor {u C M : Q'}
    (hu1 : (-1 : Q') ≤ u) (hu2 : u ≤ 1) (hC : Q'.abs C ≤ M) :
    Q'.abs (u * C) ≤ M := by
  have hMnn : (0 : Q') ≤ M := Q'.le_trans' _ _ _ (Q'.abs_nonneg C) hC
  have hCM : C ≤ M := Q'.le_trans' _ _ _ (Q'.le_abs_self C) hC
  have hnegCM : -C ≤ M := Q'.le_trans' _ _ _ (Q'.neg_le_abs C) hC
  have hMC : -M ≤ C := by
    have h := Q'.neg_le_neg hnegCM
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.neg_neg_eqv C))
  have hmCM : -M ≤ -C := Q'.neg_le_neg hCM
  have h1M : (1 * M).eqv M :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv 1 M) (Q'.mul_one_eqv M)
  -- upper bound  u·C ≤ M
  have hup : u * C ≤ M := by
    have hb := Q'.mul_le_of_bounds (by decide : (0 : Q') ≤ (1 : Q')) hMnn hu1 hu2 hMC hCM
    exact Q'.le_trans' _ _ _ hb (Q'.le_of_eqv h1M)
  -- lower bound  -M ≤ u·C   via   u·(-C) ≤ M  and  u·(-C) ≃ -(u·C)
  have hlowb : u * (-C) ≤ M := by
    have hb := Q'.mul_le_of_bounds (by decide : (0 : Q') ≤ (1 : Q')) hMnn hu1 hu2 hmCM hnegCM
    exact Q'.le_trans' _ _ _ hb (Q'.le_of_eqv h1M)
  have hlow : -M ≤ u * C := by
    have he : (u * (-C)).eqv (-(u * C)) := Q'.mul_neg_eqv u C
    have h2 : -(u * C) ≤ M := Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) hlowb
    have h3 := Q'.neg_le_neg h2
    exact Q'.le_trans' _ _ _ h3 (Q'.le_of_eqv (Q'.neg_neg_eqv (u * C)))
  exact Q'.abs_le hlow hup

/-! ## 3. The base case -/

/-- **The base case** `|C(n,[])| ≤ τ(n,[])`.  A no-edge graph spans iff `n ≤ 1`;
then `C = τ = 1` (the empty subgraph is the unique spanning tree); otherwise it
is disconnected and `C = τ = 0`. -/
theorem penrose_base (w : Nat → Nat → Q') (n : Nat) :
    Q'.abs (Csum w n []) ≤ Q'.ofNat (treeCount n []) := by
  cases hs : spans n [] with
  | false =>
    have hC : Csum w n [] = 0 := by
      show (if spans n [] = true then edgeProd w [] + (0 : Q') else 0) = 0
      rw [if_neg (by rw [hs]; exact Bool.false_ne_true)]
    have hT : treeCount n [] = 0 := by
      show (([[]] : List (List Edge)).filter
        (fun A => spans n A && decide (A.length = n - 1))).length = 0
      rw [List.filter_cons]
      have hpf : (spans n ([] : List Edge) && decide (([] : List Edge).length = n - 1))
          = false := by rw [hs]; rfl
      rw [if_neg (by rw [hpf]; exact Bool.false_ne_true)]
      rfl
    rw [hC, hT]; decide
  | true =>
    have hn : n - 1 = 0 := by have := spans_nil_le_one hs; omega
    have hC : Csum w n [] = (1 : Q') + 0 := by
      show (if spans n [] = true then edgeProd w [] + (0 : Q') else 0)
          = (1 : Q') + 0
      rw [if_pos hs]; rfl
    have hT : treeCount n [] = 1 := by
      show (([[]] : List (List Edge)).filter
        (fun A => spans n A && decide (A.length = n - 1))).length = 1
      rw [List.filter_cons]
      have hpt : (spans n ([] : List Edge) && decide (([] : List Edge).length = n - 1))
          = true := by rw [hs, hn]; rfl
      rw [if_pos hpt]
      rfl
    rw [hC, hT]; decide

/-! ## 4. The deletion–contraction recursor (named residual) -/

/-- **`DCHyp w` — the deletion–contraction identities for the concrete
`Csum`/`treeCount` (the named combinatorial core).**  For a head edge `(a,b)`:

* non-loop (`a ≠ b`):
    `C(G) ≃ C(G−e) + w e · C(G/e)`  and  `τ(G) = τ(G−e) + τ(G/e)`;
* loop (`a = b`):
    `C(G) ≃ (1 + w e)·C(G−e)`  and  `τ(G) = τ(G−e)`,

where `G−e = (n, rest)` (delete) and `G/e = (n-1, contractEdges a b rest)`
(contract).  The delete half is the definitional `sublists`-split; the contract
half is the classical contraction-invariance of connectivity and spanning trees.
Left UNINHABITED — the single load-bearing residual. -/
def DCHyp (w : Nat → Nat → Q') : Prop :=
  ∀ (n a b : Nat) (rest : List Edge),
    (a ≠ b →
        (Csum w n ((a, b) :: rest)).eqv
          (Csum w n rest + w a b * Csum w (n - 1) (contractEdges a b rest))
      ∧ treeCount n ((a, b) :: rest)
          = treeCount n rest + treeCount (n - 1) (contractEdges a b rest))
  ∧ (a = b →
        (Csum w n ((a, b) :: rest)).eqv ((1 + w a a) * Csum w n rest)
      ∧ treeCount n ((a, b) :: rest) = treeCount n rest)

/-! ## 5. The Penrose inequality `|C(G)| ≤ τ(G)` -/

/-- Fuel-indexed Penrose induction: `|C| ≤ τ` for every graph with `|edges| ≤
fuel`, by induction on the fuel.  The step chains, on a non-loop head,
`|C(G)| ≤ |C(G−e)| + |w e|·|C(G/e)| ≤ τ(G−e) + τ(G/e) = τ(G)` (triangle +
repulsive factor bound + `DCHyp`), and on a loop head
`|C(G)| = |1 + w e|·|C(G−e)| ≤ τ(G−e) = τ(G)`. -/
theorem penroseIneq_fuel (w : Nat → Nat → Q')
    (hw : ∀ a b, (-1 : Q') ≤ w a b ∧ w a b ≤ (0 : Q'))
    (hDC : DCHyp w) :
    ∀ (fuel n : Nat) (edges : List Edge),
      edges.length ≤ fuel →
      Q'.abs (Csum w n edges) ≤ Q'.ofNat (treeCount n edges) := by
  intro fuel
  induction fuel with
  | zero =>
    intro n edges hlen
    cases edges with
    | nil => exact penrose_base w n
    | cons e rest => simp only [List.length_cons] at hlen; omega
  | succ k ih =>
    intro n edges hlen
    cases edges with
    | nil => exact penrose_base w n
    | cons e rest =>
      obtain ⟨a, b⟩ := e
      have hrest : rest.length ≤ k := by
        simp only [List.length_cons] at hlen; omega
      have IHdel : Q'.abs (Csum w n rest) ≤ Q'.ofNat (treeCount n rest) :=
        ih n rest hrest
      have hconlen : (contractEdges a b rest).length ≤ k := by
        show (rest.map (fun e => (relabelV a b e.1, relabelV a b e.2))).length ≤ k
        rw [List.length_map]; exact hrest
      have IHcon : Q'.abs (Csum w (n - 1) (contractEdges a b rest))
          ≤ Q'.ofNat (treeCount (n - 1) (contractEdges a b rest)) :=
        ih (n - 1) _ hconlen
      cases hab : decide (a = b) with
      | true =>
        have hab' : a = b := of_decide_eq_true hab
        obtain ⟨hCeqv, hTeq⟩ := (hDC n a b rest).2 hab'
        have hu2 : (1 + w a a) ≤ 1 :=
          Q'.le_trans' _ _ _
            (Q'.add_le_add_left 1 (w a a) 0 (hw a a).2) (by decide)
        have hu1 : (-1 : Q') ≤ 1 + w a a := by
          have hpos : (0 : Q') ≤ 1 + w a a :=
            Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ (1 : Q') + (-1))
              (Q'.add_le_add_left 1 (-1) (w a a) (hw a a).1)
          exact Q'.le_trans' _ _ _ (by decide : (-1 : Q') ≤ 0) hpos
        have hfac := abs_mul_le_of_factor hu1 hu2 IHdel
        have h1 := Q'.le_of_eqv (Q'.abs_eqv_congr hCeqv)
        have hgoal := Q'.le_trans' _ _ _ h1 hfac
        rw [hTeq]; exact hgoal
      | false =>
        have hab' : a ≠ b := of_decide_eq_false hab
        obtain ⟨hCeqv, hTeq⟩ := (hDC n a b rest).1 hab'
        have hu1 : (-1 : Q') ≤ w a b := (hw a b).1
        have hu2 : w a b ≤ 1 := Q'.le_trans' _ _ _ (hw a b).2 (by decide)
        have hfac := abs_mul_le_of_factor hu1 hu2 IHcon
        have h1 := Q'.le_of_eqv (Q'.abs_eqv_congr hCeqv)
        have h2 := Q'.abs_add_le' (Csum w n rest)
          (w a b * Csum w (n - 1) (contractEdges a b rest))
        have h4 :
            Q'.abs (Csum w n rest)
              + Q'.abs (w a b * Csum w (n - 1) (contractEdges a b rest))
            ≤ Q'.ofNat (treeCount n rest)
              + Q'.ofNat (treeCount (n - 1) (contractEdges a b rest)) :=
          Q'.le_trans' _ _ _
            (Q'.add_le_add_right _ _ _ IHdel)
            (Q'.add_le_add_left _ _ _ hfac)
        have h5 :
            Q'.ofNat (treeCount n rest)
              + Q'.ofNat (treeCount (n - 1) (contractEdges a b rest))
            ≤ Q'.ofNat (treeCount n rest + treeCount (n - 1) (contractEdges a b rest)) :=
          Q'.ge_of_eqv (ofNat_add_eqv _ _)
        have hgoal :=
          Q'.le_trans' _ _ _ h1
            (Q'.le_trans' _ _ _ h2 (Q'.le_trans' _ _ _ h4 h5))
        rw [hTeq]; exact hgoal

/-- **The Penrose inequality `|C(G)| ≤ τ(G)` (PROVED, modulo `DCHyp`).**  For a
repulsive weight, the modulus of the signed connected-spanning-subgraph sum is
dominated by the spanning-tree count. -/
theorem penroseIneq (w : Nat → Nat → Q')
    (hw : ∀ a b, (-1 : Q') ≤ w a b ∧ w a b ≤ (0 : Q'))
    (hDC : DCHyp w) (n : Nat) (edges : List Edge) :
    Q'.abs (Csum w n edges) ≤ Q'.ofNat (treeCount n edges) :=
  penroseIneq_fuel w hw hDC edges.length n edges (Nat.le_refl _)

/-! ## 6. The Ursell pin and the reduction of `penroseDom` -/

variable {L : Lattice}

/-- **`UrsellPin w` — the Ursell↔connected-graph coefficient identity (named
residual).**  Supplies the connectivity graph `adjGraph Y = (adjN Y, adjE Y)` of
each polymer, the pinned weight `phiT Y`, and the pinned tree count
`treeCountF Y`, with:

* `ursell`   — `n!·phiT Y = |C(adjGraph Y)|` (this PINS `phiT`; classically
  `φ^T(Y) = (1/n!)·Σ_{connected graphs} ∏ ζ`, and non-adjacent pairs carry
  `ζ = 0`, collapsing `K_n` onto `adjGraph Y`);
* `countPin` — `treeCount Y = τ(adjGraph Y)`.

Left UNINHABITED — the Ursell coefficient identity is the second residual. -/
structure UrsellPin (w : Nat → Nat → Q') where
  /-- Vertex count of the connectivity graph of `Y`. -/
  adjN : Polymer L → Nat
  /-- Edge list of the connectivity graph of `Y`. -/
  adjE : Polymer L → List Edge
  /-- The pinned truncated Ursell weight `|φ^T(Y)|`. -/
  phiT : Polymer L → Q'
  /-- The pinned spanning-tree count. -/
  treeCountF : Polymer L → Nat
  /-- **`ursell` — pins `phiT`**: `n!·phiT Y = |C(adjGraph Y)|`. -/
  ursell : ∀ Y, (Q'.ofNat (fact (Polymer.size Y)) * phiT Y).eqv
    (Q'.abs (Csum w (adjN Y) (adjE Y)))
  /-- **`countPin` — pins the tree count**: `treeCount Y = τ(adjGraph Y)`. -/
  countPin : ∀ Y, treeCountF Y = treeCount (adjN Y) (adjE Y)

/-- **`penroseDom_of_pin` — the atom `penroseDom`, reduced (PROVED from the two
named residuals + the proved Penrose induction).**  For the GENUINELY-PINNED
`phiT` (pinned by `ursell` to `|C(adjGraph Y)|/n!`),

    n! · phiT Y  ≤  ofNat (treeCountF Y),

by composing the Ursell identity (`ursell`), the Penrose inequality
(`penroseIneq`, from `DCHyp`), and the tree-count pin (`countPin`).  This is
exactly the `penroseDom` field of `TreeGraphReduction`, no longer resting on an
arbitrary `phiT` where the inequality is false. -/
theorem penroseDom_of_pin (w : Nat → Nat → Q')
    (hw : ∀ a b, (-1 : Q') ≤ w a b ∧ w a b ≤ (0 : Q'))
    (hDC : DCHyp w) (P : UrsellPin (L := L) w) (Y : Polymer L) :
    Q'.ofNat (fact (Polymer.size Y)) * P.phiT Y ≤ Q'.ofNat (P.treeCountF Y) := by
  have h1 : Q'.ofNat (fact (Polymer.size Y)) * P.phiT Y
      ≤ Q'.abs (Csum w (P.adjN Y) (P.adjE Y)) :=
    Q'.le_of_eqv (P.ursell Y)
  have h2 : Q'.abs (Csum w (P.adjN Y) (P.adjE Y))
      ≤ Q'.ofNat (treeCount (P.adjN Y) (P.adjE Y)) :=
    penroseIneq w hw hDC (P.adjN Y) (P.adjE Y)
  have h3 : Q'.abs (Csum w (P.adjN Y) (P.adjE Y))
      ≤ Q'.ofNat (P.treeCountF Y) := by
    rw [P.countPin Y]; exact h2
  exact Q'.le_trans' _ _ _ h1 h3

end YMGap.Continuum.PenroseDomInduction

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.PenroseDomInduction.abs_mul_le_of_factor
#print axioms YMGap.Continuum.PenroseDomInduction.penrose_base
#print axioms YMGap.Continuum.PenroseDomInduction.penroseIneq_fuel
#print axioms YMGap.Continuum.PenroseDomInduction.penroseIneq
#print axioms YMGap.Continuum.PenroseDomInduction.penroseDom_of_pin
