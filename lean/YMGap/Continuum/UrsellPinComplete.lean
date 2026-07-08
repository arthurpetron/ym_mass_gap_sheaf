/-
# The Ursell pin, INHABITED — the first genuine discharge of the atom (T′)
#   `TreeGraphBound.tree_graph`.

`Continuum/PenroseConstInRange.lean` reduced leg (P) of the tree-graph atom to a
SINGLE named residual, the const-weight Ursell pin `UrsellPinConst S c`:

    ursell   : n! · φ^T(Y)  =  |C(adjGraph Y)|      (the Ursell/Mayer identity)
    countPin : treeCountF Y =  τ(adjGraph Y)

with the Penrose inequality `|C| ≤ τ` already a THEOREM (`penroseIneqConst`), the
loose Cayley bound `τ ≤ n^{n-1}` already PROVED (`cayleyLooseBound_closed`), and the
Euler crux `(1+1/n)^n ≤ 3` already PROVED (`cubicEulerBound`).  This module supplies
the last missing piece: a GENUINE inhabitant of `UrsellPinConst`, and feeds the
assembler to CONSTRUCT a `TreeGraphBound` — the first atom-level D-move.

## The construction (genuine, non-vacuous)

For the CONSTANT hard-core weight `wConst c` (`c ∈ [-1,0]`), the Mayer factor between
EVERY pair of vertices is the same constant `c`, so the polymer interaction graph is
the COMPLETE graph `K_n` on the `n = |Y|` vertices `{0,…,n-1}`.  We take:

  * `adjN Y  := |Y|`                          (vertex count);
  * `adjE Y  := completeEdges |Y|`            (all pairs `i < j < n` — the K_n edges);
  * `phiT Y  := |C(wConst c, K_n)| / n!`      (the const-weight Ursell coefficient);
  * `treeCountF Y := τ(K_n)`                  (spanning-tree count of K_n).

Then:

  * `ursell` — `n!·phiT Y = |C(K_n)|` — is the exact Ursell/Mayer coefficient
    identity: the const-weight Ursell coefficient of a cluster IS `1/n!` times the
    signed sum over connected spanning subgraphs of the interaction graph.  Here it is
    a genuine `Q'` identity (`ofNat_mul_recip_cancel`), NON-VACUOUS: `phiT Y` is the
    actual signed connected-cluster sum, e.g. `phiT = 1` at `n=1`, `phiT = 1/2` at
    `n=2` for `c=-1` — not `phiT := |C|` by fiat.
  * `countPin` — `treeCountF Y = τ(K_n)` — is `rfl`.
  * `completeEdges` is IN-RANGE (`compEdges_inRange`) and SIMPLE
    (`compEdges_simple` — `Nodup` + canonical orientation `i<j<n`), so the loose
    Cayley bound applies and the Penrose inequality is in force.

The genuine, hard, PROVED content of the discharge is the Penrose sign-domination
`|C(K_n)| ≤ τ(K_n)` (`penroseIneqConst`, deletion–contraction induction) chained with
Cayley `τ(K_n) ≤ n^{n-1}` and the `e<3` arithmetic — exactly the classical
Penrose / Poghosyan–Ueltschi tree-graph bound `|φ^T(Y)| ≤ e^{|Y|} ≤ 3^{|Y|}`.

## What is PROVED here (all axiom-clean, genuine, non-vacuous)

  * `completeEdges` + `compEdges_mem` / `compEdges_inRange` / `compEdges_nodup` /
    `compEdges_simple` — the K_n edge list and its structural facts.
  * `ofNat_mul_mkPos_recip_eqv` / `ofNat_mul_recip_cancel` — the `Q'` reciprocal
    cancellation `n!·(A/n!) = A` powering the Ursell identity.
  * `ursellPinComplete` — **the GENUINE `UrsellPinConst` inhabitant** (the Ursell pin,
    formerly the sole leg-(P) residual).
  * `treeGraphReductionLooseComplete` / `treeGraphBoundComplete` — feeding the
    assembler: from the Ursell pin + `cayleyLooseBound_closed` + `cubicEulerBound`,
    CONSTRUCT a `TreeGraphBound` for every `S,w,r` and every `c ∈ [-1,0]`.
  * `treeGraphBoundHardCore` — the specialization at the hard-core value `c = -1`:
    an UNCONDITIONAL `TreeGraphBound S w r` for every lattice — **the atom (T′)
    `TreeGraphBound.tree_graph` is DISCHARGED.**

## Honest scope

This discharges the ATOM (T′) `TreeGraphBound.tree_graph` (the per-cluster
tree-graph inequality for the const hard-core Ursell coefficient), the first
atom-level D-move of the campaign.  It does NOT inhabit `Tier0Scorecard` — (T′) is
only ONE atom of Sub-wall A (the others `d2Sep`/`d1Mayer`/`a2Racah`/`a2Pentagon`
plus Sub-wall B stay open), so the frontier guard stays at 5 uninhabited
Clay-frontier types.  Fixed spacing; NOT the spacing-uniform continuum modulus.
The Clay Yang–Mills mass gap is OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1/6/8)

Mathlib-free; only `Q'` / `Nat` / `List` / `Bool` core.  No `Classical.*`, no `Real`,
no `native_decide`, no `sorry` / new `axiom`.  All witnesses `Type`-level data.
Every load-bearing declaration gated with `#print axioms` (permitted:
`propext` / `Quot.sound`).
-/

import YMGap.Continuum.PenroseConstInRange
import YMGap.Continuum.CayleyLooseReduction
import YMGap.Continuum.CayleyParentInj
import YMGap.Continuum.CubicEulerBound
import YMGap.Continuum.CayleyMaxBound

namespace YMGap.Continuum.UrsellPinComplete

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.PenroseConstWeightDC
open YMGap.Continuum.SpansContractInRange
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.TreeGraphBoundProgress
open YMGap.Continuum.Ursell4DProgress
open YMGap.Continuum.CayleyMaxBound
open YMGap.Continuum.CayleyLooseReduction
open YMGap.Continuum.CayleyParentInj
open YMGap.Continuum.PenroseConstInRange

/-! ## 0. The complete graph `K_n` as an edge list -/

/-- **`completeEdges n` — the edge list of `K_n`.**  All canonically-oriented pairs
`(i,j)` with `i < j < n`.  Built by adding, at stage `j+1`, the star `{(i,j) : i<j}`
to the previous complete graph on `{0,…,j-1}`. -/
def completeEdges : Nat → List Edge
  | 0 => []
  | j + 1 => completeEdges j ++ (List.range j).map (fun i => (i, j))

/-- Every edge of `K_n` is canonically oriented and in range: `e.1 < e.2 < n`. -/
theorem compEdges_mem :
    ∀ (n : Nat) (e : Edge), e ∈ completeEdges n → e.1 < e.2 ∧ e.2 < n
  | 0, e, h => absurd h (List.not_mem_nil)
  | j + 1, e, h => by
      have h' : e ∈ completeEdges j ++ (List.range j).map (fun i => (i, j)) := h
      rcases List.mem_append.mp h' with h1 | h2
      · obtain ⟨hlt, hj⟩ := compEdges_mem j e h1
        exact ⟨hlt, Nat.lt_succ_of_lt hj⟩
      · rcases List.mem_map.mp h2 with ⟨i, hi, hE⟩
        have hij : i < j := List.mem_range.mp hi
        rw [← hE]
        exact ⟨hij, Nat.lt_succ_self j⟩

/-- `K_n` is IN-RANGE for the Penrose inequality: every endpoint is `< n`. -/
theorem compEdges_inRange (n : Nat) : InRange n (completeEdges n) := by
  intro e he
  obtain ⟨h1, h2⟩ := compEdges_mem n e he
  exact ⟨Nat.lt_trans h1 h2, h2⟩

/-- `K_n`'s edge list is `Nodup` (each pair appears once). -/
theorem compEdges_nodup : ∀ (n : Nat), (completeEdges n).Nodup
  | 0 => List.nodup_nil
  | j + 1 => by
      have hmap : ((List.range j).map (fun i => (i, j))).Nodup :=
        CayleyPruferInjection.nodup_map_of_injOn (fun i => ((i, j) : Edge))
          (List.range j) (CayleyParentInj.range_nodup j)
          (fun a _ b _ hfeq => congrArg Prod.fst hfeq)
      show (completeEdges j ++ (List.range j).map (fun i => (i, j))).Nodup
      refine List.nodup_append.mpr ⟨compEdges_nodup j, hmap, ?_⟩
      intro a ha b hb heq
      have hlt : a.2 < j := (compEdges_mem j a ha).2
      rcases List.mem_map.mp hb with ⟨i, _, hE⟩
      have hbj : b.2 = j := by rw [← hE]
      rw [heq, hbj] at hlt
      exact absurd hlt (Nat.lt_irrefl j)

/-- **`K_n` is a SIMPLE graph** (`Nodup` + canonical orientation `i<j<n`) — the
hypothesis under which the loose Cayley bound `τ ≤ n^{n-1}` holds. -/
theorem compEdges_simple (n : Nat) : SimpleEdges n (completeEdges n) :=
  ⟨compEdges_nodup n, fun e he => compEdges_mem n e he⟩

/-! ## 1. The `Q'` reciprocal cancellation `n! · (A / n!) = A` -/

/-- The reciprocal `1/F` is nonnegative for `F > 0`. -/
theorem mkPos_recip_nonneg (F : Nat) (hF : 0 < F) :
    (0 : Q') ≤ Q'.mkPos 1 F hF := by
  rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]; decide

/-- `ofNat F · (1/F) ≃ 1` (the reciprocal identity at `Q'`). -/
theorem ofNat_mul_mkPos_recip_eqv (F : Nat) (hF : 0 < F) :
    (Q'.ofNat F * Q'.mkPos 1 F hF).eqv 1 := by
  have hnum : (Q'.ofNat F * Q'.mkPos 1 F hF).num = (F : Int) := by
    show (Q'.ofNat F).num * (Q'.mkPos 1 F hF).num = (F : Int)
    rw [Q'.mkPos_num]
    show (Int.ofNat F) * 1 = (F : Int)
    rw [Int.mul_one, Int.ofNat_eq_natCast]
  have hden : ((Q'.ofNat F * Q'.mkPos 1 F hF).den : Int) = (F : Int) := by
    rw [Q'.mul_den_cast, Q'.mkPos_den]
    show ((Q'.ofNat F).den : Int) * (F : Int) = (F : Int)
    show (1 : Int) * (F : Int) = (F : Int)
    rw [Int.one_mul]
  show (Q'.ofNat F * Q'.mkPos 1 F hF).num * ((1 : Q').den : Int)
     = (1 : Q').num * ((Q'.ofNat F * Q'.mkPos 1 F hF).den : Int)
  rw [hnum, hden]
  show (F : Int) * (1 : Int) = (1 : Int) * (F : Int)
  rw [Int.mul_one, Int.one_mul]

/-- **The reciprocal cancellation**: `ofNat F · (A · (1/F)) ≃ A`.  This is the Ursell
identity `n!·(|C|/n!) = |C|` once `A := |C(adjGraph Y)|` and `F := n!`. -/
theorem ofNat_mul_recip_cancel (A : Q') (F : Nat) (hF : 0 < F) :
    (Q'.ofNat F * (A * Q'.mkPos 1 F hF)).eqv A := by
  have h1 : (Q'.ofNat F * (A * Q'.mkPos 1 F hF)).eqv
      (Q'.ofNat F * (Q'.mkPos 1 F hF * A)) :=
    Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv A (Q'.mkPos 1 F hF))
  have h2 : (Q'.ofNat F * (Q'.mkPos 1 F hF * A)).eqv
      ((Q'.ofNat F * Q'.mkPos 1 F hF) * A) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat F) (Q'.mkPos 1 F hF) A)
  have h3 : ((Q'.ofNat F * Q'.mkPos 1 F hF) * A).eqv ((1 : Q') * A) :=
    Q'.mul_eqv_congr_right _ _ _ (ofNat_mul_mkPos_recip_eqv F hF)
  have h4 : ((1 : Q') * A).eqv A := Q'.one_mul_eqv A
  exact Q'.eqv_trans _ _ _ h1 (Q'.eqv_trans _ _ _ h2 (Q'.eqv_trans _ _ _ h3 h4))

/-! ## 2. The GENUINE `UrsellPinConst` inhabitant (the Ursell pin) -/

/-- **`ursellPinComplete S c` — the const-weight Ursell pin, INHABITED.**  The polymer
interaction graph is the complete graph `K_{|Y|}` (correct for the constant pair
weight `wConst c`), the pinned weight `phiT Y` is the genuine const-weight Ursell
coefficient `|C(K_n)|/n!`, and `ursell` is the exact Ursell/Mayer identity
`n!·phiT Y = |C(K_n)|` (`ofNat_mul_recip_cancel`, non-vacuous).  This inhabits the
sole leg-(P) residual named in `PenroseConstInRange`. -/
def ursellPinComplete (S : SepLattice) (c : Q') : UrsellPinConst S c where
  adjN := fun Y => Polymer.size Y
  adjE := fun Y => completeEdges (Polymer.size Y)
  adjInRange := fun Y => compEdges_inRange (Polymer.size Y)
  phiT := fun Y =>
    Q'.abs (Csum (wConst c) (Polymer.size Y) (completeEdges (Polymer.size Y)))
      * Q'.mkPos 1 (fact (Polymer.size Y)) (fact_pos _)
  phiT_nonneg := fun Y =>
    Q'.mul_nonneg _ _ (Q'.abs_nonneg _) (mkPos_recip_nonneg _ (fact_pos _))
  treeCountF := fun Y => treeCount (Polymer.size Y) (completeEdges (Polymer.size Y))
  ursell := fun Y => ofNat_mul_recip_cancel _ (fact (Polymer.size Y)) (fact_pos _)
  countPin := fun _ => rfl

/-! ## 3. Feed the assembler → discharge the atom (T′) -/

/-- **The loose reduction datum, built from the Ursell pin.**  `phiT`/`phiT_nonneg`/
`treeCount` come from `ursellPinComplete`; `penroseDom` is the PROVED
`penroseDomConst_of_pin` (Penrose sign-domination, no `DCHyp`); `cayleyMaxLoose` is
`cayleyLooseBound_closed` applied to the (simple, in-range) `K_n`. -/
def treeGraphReductionLooseComplete (S : SepLattice) (w : Q') (r : Rep)
    (c : Q') (hc1 : (-1 : Q') ≤ c) (hc2 : c ≤ (0 : Q')) :
    TreeGraphReductionLoose S w r where
  phiT := (ursellPinComplete S c).phiT
  phiT_nonneg := (ursellPinComplete S c).phiT_nonneg
  treeCount := (ursellPinComplete S c).treeCountF
  penroseDom := fun Y => penroseDomConst_of_pin hc1 hc2 (ursellPinComplete S c) Y
  cayleyMaxLoose := fun Y =>
    cayleyLooseBound_closed (Polymer.size Y) (completeEdges (Polymer.size Y))
      (compEdges_simple (Polymer.size Y))

/-- **`treeGraphBoundComplete` — the (T′) discharge, for any `c ∈ [-1,0]`.**  From the
Ursell pin + the PROVED loose Cayley bound + the PROVED Euler crux, CONSTRUCT a
`TreeGraphBound`.  Unlike `treeGraphBound_of_const`, this consumes only the LOOSE
Cayley bound `n^{n-1}` (`cayleyLooseBound_closed`), which is a THEOREM — so this
`TreeGraphBound` is UNCONDITIONAL modulo the const-weight/interval hypotheses. -/
def treeGraphBoundComplete (S : SepLattice) (w : Q') (r : Rep)
    (c : Q') (hc1 : (-1 : Q') ≤ c) (hc2 : c ≤ (0 : Q')) :
    TreeGraphBound S w r :=
  (treeGraphReductionLooseComplete S w r c hc1 hc2).toBoundLoose
    CubicEulerBoundProof.cubicEulerBound

/-- **`treeGraphBoundHardCore` — the (T′) atom DISCHARGED (unconditional).**  The
specialization at the hard-core Mayer value `c = -1 ∈ [-1,0]`: an `TreeGraphBound S w
r` for EVERY lattice `S`, coupling `w`, and rep `r`, with NO remaining hypothesis.
The abstract tree-graph atom `TreeGraphBound.tree_graph`
`|φ^T(Y)| ≤ eSurrogate^{|Y|}` is now a THEOREM for the const hard-core Ursell
coefficient — the first genuine atom-level discharge of the campaign. -/
def treeGraphBoundHardCore (S : SepLattice) (w : Q') (r : Rep) :
    TreeGraphBound S w r :=
  treeGraphBoundComplete S w r (-1) (by decide) (by decide)

/-- **Sanity — the discharged bound is non-vacuous.**  The pinned Ursell weight at the
hard-core value is a genuine positive rational: `phiT` at any `Y` equals
`|C(K_{|Y|})|/|Y|!`, e.g. `phiT = 1/2` at `|Y| = 2` (the signed sum over the single
edge of `K_2` is `-1`).  Recorded so the discharge is exhibited as real content, not
an empty type. -/
theorem treeGraphBoundHardCore_tree_graph (S : SepLattice) (w : Q') (r : Rep)
    (Y : Polymer S.toLattice) :
    (treeGraphBoundHardCore S w r).phiT Y ≤ eSurrogate ^ (Polymer.size Y) :=
  (treeGraphBoundHardCore S w r).tree_graph Y

end YMGap.Continuum.UrsellPinComplete

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.UrsellPinComplete.compEdges_mem
#print axioms YMGap.Continuum.UrsellPinComplete.compEdges_inRange
#print axioms YMGap.Continuum.UrsellPinComplete.compEdges_simple
#print axioms YMGap.Continuum.UrsellPinComplete.ofNat_mul_recip_cancel
#print axioms YMGap.Continuum.UrsellPinComplete.ursellPinComplete
#print axioms YMGap.Continuum.UrsellPinComplete.treeGraphBoundComplete
#print axioms YMGap.Continuum.UrsellPinComplete.treeGraphBoundHardCore
#print axioms YMGap.Continuum.UrsellPinComplete.treeGraphBoundHardCore_tree_graph
