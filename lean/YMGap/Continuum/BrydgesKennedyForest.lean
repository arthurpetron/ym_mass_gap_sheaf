/-
# The Brydges–Kennedy / Abdesselam–Rivasseau FOREST-INTERPOLATION route to the
#   tree-graph bound, EVALUATED against the Penrose deletion–contraction route.

`Continuum/PenroseDomInduction.lean` proves the Penrose inequality
`|C(G)| ≤ τ(G)` (signed connected-spanning-subgraph sum ≤ spanning-tree count) by
**deletion–contraction sign domination**, modulo the single UNINHABITED recursor
`DCHyp` (the delete-half is definitional; the contract-half is the load-bearing
combinatorial core — vertex relabelling + contraction-invariance of connectivity
and spanning trees).

This module evaluates the proposed swap to the **Brydges–Kennedy / Abdesselam–
Rivasseau forest-interpolation formula**, whose promise is:
> replace the case-analytic *sign-domination* step by the *pointwise positivity*
> of the interpolated forest activities — Lean's best profile.

## What this module PROVES (all axiom-clean, `propext`/`Quot.sound` only)

  * The **positivity leg** in full generality: for `|w| ≤ 1` the tree
    forest-sum majorant `treeMajorant w = Σ_{T tree} ∏_{ℓ∈T} |w_ℓ|` is dominated
    by the spanning-tree COUNT, `treeMajorant w n edges ≤ ofNat (treeCount)`
    (`treeMajorant_le_treeCount`).  This is the *entire* "positivity/monotonicity"
    content of step (2) of the BK route, and it is genuinely trivial — one list
    induction, no case analysis.  Reuses the repulsive factor bound implicitly via
    `edgeAbsProd_le_one`.

  * `penroseIneq_via_forest` — GIVEN the forest-interpolation identity
    `ForestInterpolation` (the genuine BK tree-graph inequality `|C(G)| ≤
    treeMajorant`), the Penrose conclusion `|C(G)| ≤ ofNat (treeCount)` follows by
    composing with the positivity leg.  So the forest identity is a *drop-in* for
    `DCHyp`: it reaches the SAME `penroseIneq` conclusion.

  * `penroseDom_via_forest` — the KP consumer atom.  From `ForestInterpolation`
    plus the Ursell pin `UrsellPin`, the exact `penroseDom` field of
    `TreeGraphBoundProgress.TreeGraphReduction` (`n!·|φ^T(Y)| ≤ ofNat(treeCountF
    Y)`) is derived — i.e. the BK output feeds the identical Kotecký–Preiss layer
    that the Penrose route did, via the very same `UrsellPin`.

  * **The refutation of the premise** (`triangle_refutes_positivity`,
    machine-checked by `decide`): on the triangle `K₃` with the hard-core weight
    `ζ = -1`, the *positivity majorant* obtained by applying the triangle
    inequality directly to `C` — the count of connected spanning subgraphs
    `spanCount = 4` — STRICTLY EXCEEDS the tree count `treeCount = 3`, while the
    true SIGNED value `|C| = |signedCount| = 2 ≤ 3`.  Hence pure positivity applied
    to `C` itself CANNOT establish `|C| ≤ τ`: the required exponential collapse
    lives entirely in the SIGN CANCELLATION, which the forest-interpolation IDENTITY
    encodes (via the tree structure of the identity) — it is NOT eliminated by
    "replacing sign-domination with positivity".

## The named residual `ForestInterpolation` (NOT faked)

`ForestInterpolation w` carries exactly the BK tree-graph inequality
`|C(G)| ≤ treeMajorant w`.  It is left UNINHABITED.  It is the genuine
Brydges–Kennedy content: its honest cost is either the BK interpolation INTEGRAL
over the forest parameters `s ∈ [0,1]^{edges}` (a constructive multivariate
integral + fundamental-theorem-of-calculus, which the Mathlib-free `Q'`/`CReal`
core does NOT provide), or — equivalently — the Penrose partition-scheme /
deletion–contraction combinatorics `DCHyp`.  The two are the SAME difficulty
class; the forest identity is NOT independently cheaper in this core.

## HONEST VERDICT (see `bk_forest.md` for the full write-up)

The user's premise — "algebraic-identity-plus-positivity beats case-analytic
sign-domination" — is **correct in a Mathlib-rich setting** but does **NOT hold in
this Lean-core (`Q'`/`CReal`, no Mathlib) setting**, for a precise reason proved
here:

  1. The positivity leg (`treeMajorant_le_treeCount`) IS trivial — but it is not
     the wall; it was never the wall.
  2. The BK "single algebraic identity" `φ^T = Σ_F ∫ ds W(F,s) ∏(pair)` is an
     ANALYTIC (integral / FTC) identity, not a finite algebraic one.  Formalizing
     it constructively requires a multivariate integral over `[0,1]^{edges}` that
     the core lacks — strictly MORE infrastructure than the finite `DCHyp`.
  3. The sign cancellation the tree-graph bound depends on is real and essential
     (`triangle_refutes_positivity`); positivity does not remove it, it only
     repackages it inside the (integral) identity.

So BK does **not** collapse `(T′)`+`(D1)` into "one identity + positivity" in this
core, and the recommendation is: **do not swap** — keep the finite Penrose
`DCHyp` route (or supply `DCHyp` directly), which stays entirely inside
`Q'`/`Nat`/`List`.  This module nonetheless lands the genuinely-provable half of
the BK route (the positivity leg + the drop-in wiring to the KP consumer), so the
forest identity — if ever supplied — plugs straight in.

## Scope

Fixed-spacing strong-coupling combinatorics (`ρ₄ = 15/32`, hard-core `-1 ≤ w ≤ 0`).
NOT the spacing-uniform continuum modulus; does NOT bear on the Clay continuum
limit.  `ForestInterpolation` is LEFT UNINHABITED; nothing is faked.

# Constructive contract (`lean/AGENTS.md` Rules 1/6/8)

Mathlib-free; only `Q'` / `Nat` / `List` / `Int` core.  No `Classical.*`, no
`Real`, no `native_decide`, no `sorry` / `admit` / new `axiom` / `Prop := True`.
The one open item (`ForestInterpolation`) is a NAMED structure, uninhabited.
Every load-bearing declaration is gated with `#print axioms`
(permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.PenroseDomInduction

namespace YMGap.Continuum.BrydgesKennedyForest

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.TreeGraphBoundProgress
open YMGap.Continuum.PenroseDomInduction

/-! ## 0. The repulsive factor is `|·| ≤ 1` -/

/-- For a repulsive weight `-1 ≤ w ≤ 0`, each factor has `|w| ≤ 1`.
(`|w| = -w ≤ 1` since `-1 ≤ w`.) -/
theorem repulsive_abs_le_one {w : Nat → Nat → Q'}
    (hw : ∀ a b, (-1 : Q') ≤ w a b ∧ w a b ≤ (0 : Q')) :
    ∀ a b, Q'.abs (w a b) ≤ (1 : Q') := by
  intro a b
  have h2 : w a b ≤ (1 : Q') := Q'.le_trans' _ _ _ (hw a b).2 (by decide)
  exact Q'.abs_le (hw a b).1 h2

/-! ## 1. The tree forest-sum majorant `treeMajorant`

`edgeAbsProd w A = ∏_{e ∈ A} |w e|` is the absolute edge-subset weight; the tree
majorant sums it over the spanning trees (the length-`(n-1)` connected spanning
subgraphs), i.e. over the SAME filtered `sublists` list whose length IS
`treeCount`.  This is the RHS of the Brydges–Kennedy / tree-graph inequality
`|C(G)| ≤ Σ_{T tree} ∏_{ℓ∈T} |w_ℓ|`. -/

/-- The absolute edge-subset weight `∏_{e ∈ A} |w e|`. -/
def edgeAbsProd (w : Nat → Nat → Q') (A : List Edge) : Q' :=
  A.foldr (fun e acc => Q'.abs (w e.1 e.2) * acc) 1

/-- `∏|w| ≥ 0`. -/
theorem edgeAbsProd_nonneg (w : Nat → Nat → Q') :
    ∀ A : List Edge, (0 : Q') ≤ edgeAbsProd w A
  | [] => by show (0 : Q') ≤ (1 : Q'); decide
  | e :: A => by
      show (0 : Q') ≤ Q'.abs (w e.1 e.2) * edgeAbsProd w A
      exact Q'.mul_nonneg _ _ (Q'.abs_nonneg _) (edgeAbsProd_nonneg w A)

/-- For `|w| ≤ 1`, the absolute edge-subset weight is `≤ 1` (a product of factors
in `[0,1]`). -/
theorem edgeAbsProd_le_one {w : Nat → Nat → Q'}
    (hw1 : ∀ a b, Q'.abs (w a b) ≤ (1 : Q')) :
    ∀ A : List Edge, edgeAbsProd w A ≤ (1 : Q')
  | [] => by show (1 : Q') ≤ (1 : Q'); exact Q'.le_refl' 1
  | e :: A => by
      show Q'.abs (w e.1 e.2) * edgeAbsProd w A ≤ (1 : Q')
      -- |w e|·P ≤ 1·P = P ≤ 1
      have hP0 : (0 : Q') ≤ edgeAbsProd w A := edgeAbsProd_nonneg w A
      have hPle : edgeAbsProd w A ≤ (1 : Q') := edgeAbsProd_le_one hw1 A
      have h1 : Q'.abs (w e.1 e.2) * edgeAbsProd w A ≤ (1 : Q') * edgeAbsProd w A :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ (hw1 e.1 e.2) hP0
      refine Q'.le_trans' _ _ _ h1 ?_
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) hPle

/-- The spanning-tree list of the connectivity graph: the length-`(n-1)` connected
spanning subgraphs.  Its length IS `treeCount` (definitional). -/
def treeList (n : Nat) (edges : List Edge) : List (List Edge) :=
  (sublists edges).filter (fun A => spans n A && decide (A.length = n - 1))

/-- `treeList` has length `treeCount` (both are the same filtered `sublists`). -/
theorem treeList_length (n : Nat) (edges : List Edge) :
    (treeList n edges).length = treeCount n edges := rfl

/-- **The tree forest-sum majorant** `Σ_{T tree} ∏_{ℓ∈T} |w_ℓ|` — the RHS of the
Brydges–Kennedy tree-graph inequality. -/
def treeMajorant (w : Nat → Nat → Q') (n : Nat) (edges : List Edge) : Q' :=
  (treeList n edges).foldr (fun A acc => edgeAbsProd w A + acc) 0

/-! ## 2. THE POSITIVITY LEG (PROVED) — forest-sum majorant ≤ tree COUNT

`treeMajorant ≤ ofNat (treeCount)`: since each `∏|w_ℓ| ≤ 1` and there are exactly
`treeCount` summands, the forest-sum is bounded by the count.  This is the ENTIRE
positivity/monotonicity content of the BK route's step (2) — one list induction,
no case analysis.  It is genuinely trivial; it was never the wall. -/

/-- A finite sum of `edgeAbsProd`-terms, each `≤ 1`, is `≤ ofNat (length)`. -/
theorem listSum_le_len {w : Nat → Nat → Q'}
    (hw1 : ∀ a b, Q'.abs (w a b) ≤ (1 : Q')) :
    ∀ L : List (List Edge),
      L.foldr (fun A acc => edgeAbsProd w A + acc) 0 ≤ Q'.ofNat L.length
  | [] => by
      show (0 : Q') ≤ Q'.ofNat 0
      exact Q'.le_of_eqv (Q'.eqv_symm Q'.ofNat_zero_eqv)
  | A :: L => by
      show edgeAbsProd w A + L.foldr (fun A acc => edgeAbsProd w A + acc) 0
          ≤ Q'.ofNat (L.length + 1)
      have hAle : edgeAbsProd w A ≤ (1 : Q') := edgeAbsProd_le_one hw1 A
      have hIH : L.foldr (fun A acc => edgeAbsProd w A + acc) 0 ≤ Q'.ofNat L.length :=
        listSum_le_len hw1 L
      -- step1: ≤ 1 + ofNat L.length
      have hstep1 : edgeAbsProd w A + L.foldr (fun A acc => edgeAbsProd w A + acc) 0
          ≤ (1 : Q') + Q'.ofNat L.length := Q'.add_le_add hAle hIH
      -- step2: 1 + ofNat L.length ≤ ofNat (L.length + 1)
      have he1 : (Q'.ofNat 1).eqv (1 : Q') := by decide
      have h1 : (1 : Q') ≤ Q'.ofNat 1 := Q'.ge_of_eqv he1
      have h2 : (1 : Q') + Q'.ofNat L.length ≤ Q'.ofNat 1 + Q'.ofNat L.length :=
        Q'.add_le_add_right 1 (Q'.ofNat 1) (Q'.ofNat L.length) h1
      have he2 : (Q'.ofNat (1 + L.length)).eqv (Q'.ofNat 1 + Q'.ofNat L.length) :=
        ofNat_add_eqv 1 L.length
      have h3 : Q'.ofNat 1 + Q'.ofNat L.length ≤ Q'.ofNat (1 + L.length) :=
        Q'.ge_of_eqv he2
      have hcomm : (1 + L.length) = (L.length + 1) := Nat.add_comm 1 L.length
      rw [hcomm] at h3
      have hstep2 : (1 : Q') + Q'.ofNat L.length ≤ Q'.ofNat (L.length + 1) :=
        Q'.le_trans' _ _ _ h2 h3
      exact Q'.le_trans' _ _ _ hstep1 hstep2

/-- **`treeMajorant_le_treeCount` (PROVED — the positivity leg).**  For a weight
with `|w| ≤ 1`, the Brydges–Kennedy tree forest-sum majorant is bounded by the
spanning-tree COUNT:

    treeMajorant w n edges  =  Σ_{T tree} ∏_{ℓ∈T} |w_ℓ|  ≤  ofNat (treeCount n edges).

This is the whole "pointwise positivity/monotonicity" step of the forest route —
and it is trivial. -/
theorem treeMajorant_le_treeCount {w : Nat → Nat → Q'}
    (hw1 : ∀ a b, Q'.abs (w a b) ≤ (1 : Q')) (n : Nat) (edges : List Edge) :
    treeMajorant w n edges ≤ Q'.ofNat (treeCount n edges) := by
  have h := listSum_le_len hw1 (treeList n edges)
  rw [treeList_length] at h
  exact h

/-! ## 3. The forest-interpolation IDENTITY (named residual) and the drop-in

`ForestInterpolation w` carries exactly the Brydges–Kennedy tree-graph inequality
`|C(G)| ≤ treeMajorant w` — the content that the forest-interpolation formula
`φ^T = Σ_F ∫ ds W(F,s) ∏(pair)` (`W ≥ 0`, activities pointwise `≥ 0`) yields for
repulsive weights.  It is LEFT UNINHABITED: its honest cost is the BK interpolation
INTEGRAL over `[0,1]^{edges}` (a constructive multivariate integral + FTC, absent
from this core) or — equivalently — the Penrose deletion–contraction `DCHyp`.  Same
difficulty class; NOT independently cheaper here. -/

/-- **`ForestInterpolation` (NAMED — the Brydges–Kennedy tree-graph inequality).**
The single field is `|C(G)| ≤ treeMajorant w n edges` for every graph — the exact
tree-graph bound that the forest-interpolation identity delivers via pointwise
positivity of the interpolated forest activities.  LEFT UNINHABITED. -/
structure ForestInterpolation (w : Nat → Nat → Q') where
  /-- The Brydges–Kennedy tree-graph inequality: the signed connected-spanning
  sum is dominated by the tree forest-sum majorant. -/
  tree_graph_ineq : ∀ (n : Nat) (edges : List Edge),
    Q'.abs (Csum w n edges) ≤ treeMajorant w n edges

/-- **`penroseIneq_via_forest` (PROVED given the forest identity).**  From the
Brydges–Kennedy identity `ForestInterpolation` and the trivial positivity leg,
the Penrose conclusion `|C(G)| ≤ ofNat (treeCount)` follows.  This is the exact
conclusion of `PenroseDomInduction.penroseIneq` — the forest identity is a
drop-in for `DCHyp`. -/
theorem penroseIneq_via_forest {w : Nat → Nat → Q'}
    (hw1 : ∀ a b, Q'.abs (w a b) ≤ (1 : Q')) (F : ForestInterpolation w)
    (n : Nat) (edges : List Edge) :
    Q'.abs (Csum w n edges) ≤ Q'.ofNat (treeCount n edges) :=
  Q'.le_trans' _ _ _ (F.tree_graph_ineq n edges) (treeMajorant_le_treeCount hw1 n edges)

/-! ## 4. FEED THE KP CONSUMER — the `penroseDom` atom via the forest route

The forest output plugs into the SAME Kotecký–Preiss layer as Penrose: via the
same `UrsellPin` (pinning `phiT Y = |φ^T(Y)|`, `treeCountF Y = τ(adjGraph Y)`),
`ForestInterpolation` discharges the exact `penroseDom` field
(`n!·phiT Y ≤ ofNat(treeCountF Y)`) of `TreeGraphBoundProgress.TreeGraphReduction`.
Structurally identical to `PenroseDomInduction.penroseDom_of_pin`, with
`ForestInterpolation` replacing `DCHyp`. -/

variable {L : Lattice}

/-- **`penroseDom_via_forest` (PROVED given the forest identity + Ursell pin).**
The Kotecký–Preiss atom `penroseDom` for the pinned `phiT`, derived from the
Brydges–Kennedy `ForestInterpolation`:

    n! · phiT Y  ≤  ofNat (treeCountF Y),

by composing the Ursell identity (`P.ursell`), the forest tree-graph bound
(`penroseIneq_via_forest`), and the tree-count pin (`P.countPin`).  This is
exactly the `penroseDom` field of `TreeGraphReduction`, fed by BK instead of
deletion–contraction. -/
theorem penroseDom_via_forest {w : Nat → Nat → Q'}
    (hw : ∀ a b, (-1 : Q') ≤ w a b ∧ w a b ≤ (0 : Q'))
    (F : ForestInterpolation w) (P : UrsellPin (L := L) w) (Y : Polymer L) :
    Q'.ofNat (fact (Polymer.size Y)) * P.phiT Y ≤ Q'.ofNat (P.treeCountF Y) := by
  have hw1 : ∀ a b, Q'.abs (w a b) ≤ (1 : Q') := repulsive_abs_le_one hw
  have h1 : Q'.ofNat (fact (Polymer.size Y)) * P.phiT Y
      ≤ Q'.abs (Csum w (P.adjN Y) (P.adjE Y)) :=
    Q'.le_of_eqv (P.ursell Y)
  have h2 : Q'.abs (Csum w (P.adjN Y) (P.adjE Y))
      ≤ Q'.ofNat (treeCount (P.adjN Y) (P.adjE Y)) :=
    penroseIneq_via_forest hw1 F (P.adjN Y) (P.adjE Y)
  have h3 : Q'.abs (Csum w (P.adjN Y) (P.adjE Y)) ≤ Q'.ofNat (P.treeCountF Y) := by
    rw [P.countPin Y]; exact h2
  exact Q'.le_trans' _ _ _ h1 h3

/-! ## 5. THE REFUTATION — positivity applied to `C` CANNOT replace sign-domination

The Brydges–Kennedy promise is "replace *sign-domination* by *positivity*".  This
section machine-refutes the naive reading of that promise: applying the triangle
inequality (positivity) to `C(G)` DIRECTLY gives `|C(G)| ≤ Σ_{A spanning} ∏|w_ℓ|`,
and for the hard-core weight `ζ = -1` that RHS is the COUNT of connected spanning
subgraphs `spanCount`.  On the triangle `K₃` this count is `4`, STRICTLY larger
than the tree count `treeCount = 3` — so this positivity bound is USELESS for
`|C| ≤ τ`.  Yet the true SIGNED value is `|C| = |signedCount| = 2 ≤ 3`.  The gap
`4 vs 2` is exactly the sign cancellation, which the forest-interpolation IDENTITY
must still encode (via its tree structure).  Positivity does not remove it. -/

/-- The triangle `K₃` (`3` vertices, `3` edges). -/
def triEdges : List Edge := [(0, 1), (1, 2), (0, 2)]

/-- The number of connected spanning subgraphs — i.e. `Σ_{A spanning} ∏|ζ|` at the
hard-core weight `|ζ| = 1`.  This is the RHS of the triangle inequality applied to
`C` directly (the "positivity" bound one gets WITHOUT the forest identity). -/
def spanCount (n : Nat) (edges : List Edge) : Nat :=
  ((sublists edges).filter (fun A => spans n A)).length

/-- The signed connected-spanning-subgraph count `Σ_{A spanning} (-1)^{|A|}` — the
value of `C(G)` at the hard-core weight `ζ = -1` (an `Int`). -/
def signedCount (n : Nat) (edges : List Edge) : Int :=
  (sublists edges).foldr
    (fun A acc => if spans n A = true then acc + (-1) ^ A.length else acc) 0

/-- **`triangle_refutes_positivity` (PROVED by `decide` — the refutation).**  On
the triangle `K₃` with the hard-core weight `ζ = -1`:

  * the POSITIVITY majorant (triangle inequality on `C`) is
    `spanCount = 4`, which **strictly exceeds** the tree count `treeCount = 3` —
    so positivity applied to `C` cannot yield `|C| ≤ τ`;
  * the TRUE signed value satisfies `|C| = |signedCount| = 2 ≤ 3 = treeCount` —
    the bound holds only via the SIGN CANCELLATION.

Hence "replace sign-domination by positivity" fails for the naive positivity of
`C`: the cancellation is essential and must live in the forest IDENTITY. -/
theorem triangle_refutes_positivity :
    treeCount 3 triEdges < spanCount 3 triEdges
      ∧ (signedCount 3 triEdges).natAbs ≤ treeCount 3 triEdges := by
  decide

/-- Sharp companion: the exact values `treeCount = 3`, `spanCount = 4`,
`signedCount = 2` on `K₃` (the numbers behind the refutation). -/
theorem triangle_values :
    treeCount 3 triEdges = 3
      ∧ spanCount 3 triEdges = 4
      ∧ signedCount 3 triEdges = 2 := by
  decide

end YMGap.Continuum.BrydgesKennedyForest

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.BrydgesKennedyForest.repulsive_abs_le_one
#print axioms YMGap.Continuum.BrydgesKennedyForest.edgeAbsProd_le_one
#print axioms YMGap.Continuum.BrydgesKennedyForest.treeMajorant_le_treeCount
#print axioms YMGap.Continuum.BrydgesKennedyForest.penroseIneq_via_forest
#print axioms YMGap.Continuum.BrydgesKennedyForest.penroseDom_via_forest
#print axioms YMGap.Continuum.BrydgesKennedyForest.triangle_refutes_positivity
#print axioms YMGap.Continuum.BrydgesKennedyForest.triangle_values
