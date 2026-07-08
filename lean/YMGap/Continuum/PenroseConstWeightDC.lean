/-
# The Penrose deletion–contraction recursor, CLOSED on its loop branch and
#   CORRECTED + reduced on its non-loop branch — for the physically-correct
#   constant (hard-core) weight.

`Continuum/PenroseDomInduction.lean` proves the Penrose inequality
`|C(G)| ≤ τ(G)` by fuel induction *modulo* the residual `DCHyp w` — the
deletion–contraction identities for the concrete signed sum `Csum` and the
spanning-tree count `treeCount`.  Two honest facts about `DCHyp w`, both
established elsewhere in-tree, frame this module:

* the **non-loop `Csum` half is machine-REFUTED for general `w`**
  (`PenroseDCContract.dc_nonloop_Csum_refuted`): `contractEdges` relabels
  vertices and `edgeProd` re-reads `w` at the NEW labels, so the identity fails
  unless `w` is relabel-invariant;
* the connectivity/`treeCount` contract half needs the ORIENTATION guard
  `a < b` (not merely `a ≠ b`): `SpansContractProof.spansContract_refuted` shows
  the unoriented form is false.

This module discharges what is GENUINELY TRUE, over the *original* `Csum` /
`treeCount` objects (not the edge-carried-weight `WEdge` mirror of
`PenroseWeightedRepair`):

## 1. The loop branch — CLOSED unconditionally (no residual)

  * `treeCount_loop_closed` — `treeCount n ((a,a)::rest) = treeCount n rest`,
    PROVED from the already-PROVED `SpansMinEdgesProof.spansMinEdges`
    ("spanning ⟹ ≥ n-1 edges") + `spans_self_loop` + `treeCount_cons_split`: a
    head self-loop `(a,a)` needs `|s| = n-2` edges to span with `|(a,a)::s|=n-1`,
    which `spansMinEdges` forbids, so the head-containing branch is empty.
  * `dcLoopBranch_closed` — the FULL loop branch of the recursor, for EVERY `w`:
    `Csum` half is `PenroseDCContract.dc_loop_Csum` (already general), `treeCount`
    half is `treeCount_loop_closed`.  No residual, no orientation, no weight
    restriction — the loop branch of `DCHyp` is now a theorem.

## 2. The non-loop `Csum` branch — CORRECTED + reduced to one BFS residual

The refutation is a defect of *non-constant* weights only.  For the constant
(hard-core) weight `wConst c ≡ c` (`-1 ≤ c ≤ 0` is the strong-coupling pair
factor), `edgeProd (wConst c) A = c^{|A|}` is relabel-invariant, so the value
side is immune to the defect and the identity is TRUE:

  * `Csum_nonloop_const_reduced` — for `a < b`, `b < n`:
        `C(n,(a,b)::rest) ≃ C(n,rest) + c · C(n-1, contractEdges a b rest)`,
    PROVED from the SINGLE correctly-guarded connectivity residual
    `TreeCountContractProof.SpansContractLt` (`a < b → b < n →
    spans n ((a,b)::A) = spans (n-1)(contractEdges a b A)`), the same residual
    the weightless `treeCount` half (`treeCountContractGuarded`) reduces to.

So, for the constant hard-core weight, **every** half of the deletion–contraction
recursor is either closed outright (both loop halves; the delete split) or
reduced to the ONE weightless BFS fact `SpansContractLt` (both non-loop halves) —
which in turn reduces to `SpansContractProof.ReachTransport`.  The general-`w`
refutation is thereby localized precisely to the non-constant weights, and the
physically-relevant hard-core case is honestly assembled.

## Honest scope (AGENTS.md Rule 6)

This does NOT inhabit `penroseIneq`/`DCHyp` as stated (those quantify over a
general `w` and arbitrary head orientation, where the recursor is FALSE).  It
closes the loop branch unconditionally and reduces the constant-weight non-loop
branch to the single open BFS residual `SpansContractLt`
(⟸ `ReachTransport`), which is left UNINHABITED (genuinely TRUE, unbuilt).
Nothing is faked.  Fixed-spacing strong-coupling combinatorics; NOT the
spacing-uniform continuum modulus, NOT the Clay Yang–Mills mass gap (OPEN).

# Constructive contract (`lean/AGENTS.md` Rules 1/6/8)

Mathlib-free; only `Q'` / `Nat` / `List` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `sorry` / new `axiom`.  `by_cases`/`decide`/`cases` on
decidable `Nat`/`Bool`/`List` props only.  Every load-bearing declaration gated
with `#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.SpansMinEdgesProof
import YMGap.Continuum.TreeCountContractProof

namespace YMGap.Continuum.PenroseConstWeightDC

open YMGap.Constructive
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.PenroseDCContract
open YMGap.Continuum.TreeCountContractProof
open YMGap.Continuum.SpansMinEdgesProof

/-! ## 0. A `filter`-length helper: all-false ⟹ length 0 -/

/-- If every member of `l` fails the guard `p`, the `p`-filter is empty. -/
theorem filter_len_zero {α : Type _} (p : α → Bool) :
    ∀ l : List α, (∀ x, x ∈ l → p x = false) → (l.filter p).length = 0
  | [], _ => rfl
  | a :: t, h => by
      rw [List.filter_cons]
      have ha : p a = false := h a List.mem_cons_self
      rw [if_neg (by rw [ha]; exact Bool.false_ne_true)]
      exact filter_len_zero p t (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-! ## 1. The loop branch — CLOSED unconditionally -/

/-- **`treeCount_loop_closed` (PROVED — the loop `treeCount` identity).**  A head
self-loop `(a,a)` is invisible to the spanning-tree count:

    treeCount n ((a,a)::rest) = treeCount n rest.

The `sublists` head split (`treeCount_cons_split`) leaves a head-containing branch
counting `s ⊆ rest` with `spans n ((a,a)::s)` and `|(a,a)::s| = n-1`.  Since a
self-loop is invisible to connectivity (`spans_self_loop`), such an `s` would
span with only `|s| = n-2` edges — forbidden by the PROVED `spansMinEdges`
("spanning ⟹ `n ≤ |s|+1`").  So the branch is empty. -/
theorem treeCount_loop_closed (n a : Nat) (rest : List Edge) :
    treeCount n ((a, a) :: rest) = treeCount n rest := by
  have hsplit := treeCount_cons_split n (a, a) rest
  have hz : ((sublists rest).filter
      (fun s => spans n ((a, a) :: s) && decide (((a, a) :: s).length = n - 1))).length
        = 0 := by
    apply filter_len_zero
    intro s _
    by_cases hlen : ((a, a) :: s).length = n - 1
    · have hd : decide (((a, a) :: s).length = n - 1) = true := by
        rw [decide_eq_true_eq]; exact hlen
      rw [hd, Bool.and_true, spans_self_loop n a s]
      cases hsp : spans n s with
      | false => rfl
      | true =>
          exfalso
          have hmin := spansMinEdges n s hsp
          have hlen' : s.length + 1 = n - 1 := hlen
          omega
    · have hd : decide (((a, a) :: s).length = n - 1) = false :=
        decide_eq_false_iff_not.mpr hlen
      rw [hd, Bool.and_false]
  rw [hsplit, hz, Nat.add_zero]

/-- **`dcLoopBranch_closed` (PROVED — the whole loop branch of the recursor,
general `w`).**  For a head self-loop `(a,a)` and ANY weight `w`, both
deletion–contraction identities of `DCHyp`'s loop branch hold:

    Csum w n ((a,a)::rest) ≃ (1 + w a a) · Csum w n rest     (`dc_loop_Csum`)
    treeCount n ((a,a)::rest) = treeCount n rest             (`treeCount_loop_closed`).

No residual, no orientation guard, no weight restriction. -/
theorem dcLoopBranch_closed (w : Nat → Nat → Q') (n a : Nat) (rest : List Edge) :
    (Csum w n ((a, a) :: rest)).eqv ((1 + w a a) * Csum w n rest)
    ∧ treeCount n ((a, a) :: rest) = treeCount n rest :=
  ⟨dc_loop_Csum w n a rest, treeCount_loop_closed n a rest⟩

/-! ## 2. The constant (hard-core) weight and its `edgeProd` -/

/-- The constant (hard-core) weight `wConst c a b = c`.  At strong coupling the
pair factor `c ∈ [-1,0]`; being relabel-invariant it is immune to the
contraction defect that refutes the non-loop `Csum` identity for general `w`. -/
def wConst (c : Q') : Nat → Nat → Q' := fun _ _ => c

/-- `wConst c` is repulsive for `-1 ≤ c ≤ 0` (admissible for `penroseIneq`). -/
theorem wConst_repulsive {c : Q'} (h1 : (-1 : Q') ≤ c) (h2 : c ≤ (0 : Q')) :
    ∀ a b, (-1 : Q') ≤ wConst c a b ∧ wConst c a b ≤ (0 : Q') :=
  fun _ _ => ⟨h1, h2⟩

/-- **`edgeProd_const_map`.**  Since `edgeProd (wConst c)` folds `fun _ acc => c*acc`
(ignoring the edge), it depends only on list length; hence it is invariant under
ANY per-edge relabelling `φ`: `edgeProd (wConst c) (s.map φ) = edgeProd (wConst c) s`.
This is exactly the relabel-invariance the general-`w` `edgeProd` lacks. -/
theorem edgeProd_const_map (c : Q') (φ : Edge → Edge) :
    ∀ s : List Edge, edgeProd (wConst c) (s.map φ) = edgeProd (wConst c) s
  | [] => rfl
  | e :: t => by
      show wConst c (φ e).1 (φ e).2 * edgeProd (wConst c) (t.map φ)
         = wConst c e.1 e.2 * edgeProd (wConst c) t
      show c * edgeProd (wConst c) (t.map φ) = c * edgeProd (wConst c) t
      rw [edgeProd_const_map c φ t]

/-! ## 3. A general `map`-collapse for `gsum` -/

/-- The `gsum` over a `map`ped power-set collapses to a `gsum` over the
un-mapped list with `f`/`P` precomposed with `g` (general `g`, mirrors
`PenroseDCContract.gsum_map_cons`). -/
theorem gsum_map (f : List Edge → Q') (P : List Edge → Bool) (g : List Edge → List Edge) :
    ∀ L : List (List Edge),
      gsum f P (L.map g) = gsum (fun A => f (g A)) (fun A => P (g A)) L
  | [] => rfl
  | a :: t => by
      show gsum f P (g a :: t.map g) = gsum (fun A => f (g A)) (fun A => P (g A)) (a :: t)
      cases hP : P (g a) with
      | true =>
          rw [gsum_cons_pos f P (g a) _ hP, gsum_map f P g t,
              gsum_cons_pos (fun A => f (g A)) (fun A => P (g A)) a t hP]
      | false =>
          rw [gsum_cons_neg f P (g a) _ hP, gsum_map f P g t,
              gsum_cons_neg (fun A => f (g A)) (fun A => P (g A)) a t hP]

/-! ## 4. The non-loop `Csum` identity for the constant weight, reduced to
`SpansContractLt` -/

/-- **`Csum_nonloop_const_reduced` (PROVED from `SpansContractLt`).**  For the
constant weight `wConst c` and an ORIENTED in-range head `a < b < n`,

    C(n, (a,b)::rest)  ≃  C(n, rest)  +  c · C(n-1, contractEdges a b rest),

the non-loop deletion–contraction identity that is FALSE for general `w`
(`dc_nonloop_Csum_refuted`) but TRUE here because `edgeProd (wConst c)` is
relabel-invariant (`edgeProd_const_map`).  The single input is the
correctly-guarded connectivity contraction-invariance `SpansContractLt` — the
same residual the weightless `treeCount` half (`treeCountContractGuarded`)
consumes.  Assembly: the delete split (`Csum_delete_split`) leaves a
head-containing branch sum, which `gsum_map` + `edgeProd_const_map` (value) +
`SpansContractLt` (guard) identify with `C(n-1, contract)`, and
`gsum_const_mul` pulls out the head factor `c`. -/
theorem Csum_nonloop_const_reduced (hSC : SpansContractLt) (c : Q')
    (n a b : Nat) (rest : List Edge) (hab : a < b) (hbn : b < n) :
    (Csum (wConst c) n ((a, b) :: rest)).eqv
      (Csum (wConst c) n rest
        + c * Csum (wConst c) (n - 1) (contractEdges a b rest)) := by
  -- (i) delete split at the general head (a,b)
  have hsplit := Csum_delete_split (wConst c) n a b rest
  -- (ii) rewrite C(n-1, contract) as a gsum over `sublists rest` with the
  --      head-guard `spans n ((a,b)::·)` and value `edgeProd (wConst c)`.
  have hCeq : Csum (wConst c) (n - 1) (contractEdges a b rest)
      = gsum (edgeProd (wConst c)) (fun s => spans n ((a, b) :: s)) (sublists rest) := by
    show gsum (edgeProd (wConst c)) (spans (n - 1)) (sublists (contractEdges a b rest)) = _
    have hsub : sublists (contractEdges a b rest)
        = (sublists rest).map (fun s => contractEdges a b s) := by
      show sublists (rest.map (fun e : Edge => (relabelV a b e.1, relabelV a b e.2)))
         = (sublists rest).map
             (fun s => s.map (fun e : Edge => (relabelV a b e.1, relabelV a b e.2)))
      exact PenroseWeightedRepair.sublists_map
        (fun e : Edge => (relabelV a b e.1, relabelV a b e.2)) rest
    rw [hsub, gsum_map]
    have hval : (fun A => edgeProd (wConst c) (contractEdges a b A))
        = edgeProd (wConst c) := by
      funext s
      exact edgeProd_const_map c (fun e : Edge => (relabelV a b e.1, relabelV a b e.2)) s
    have hguard : (fun A => spans (n - 1) (contractEdges a b A))
        = (fun s => spans n ((a, b) :: s)) := by
      funext s; exact (hSC n a b s hab hbn).symm
    rw [hval, hguard]
  -- (iii) the head-containing branch equals `c · C(n-1, contract)`
  have hbranch :
      (gsum (fun A => edgeProd (wConst c) ((a, b) :: A))
            (fun A => spans n ((a, b) :: A)) (sublists rest)).eqv
        (c * Csum (wConst c) (n - 1) (contractEdges a b rest)) := by
    rw [hCeq]
    have hval2 : (fun A => edgeProd (wConst c) ((a, b) :: A))
        = (fun A => c * edgeProd (wConst c) A) := by funext A; rfl
    rw [hval2]
    exact gsum_const_mul c (edgeProd (wConst c))
      (fun s => spans n ((a, b) :: s)) (sublists rest)
  -- (iv) assemble
  exact Q'.eqv_trans _ _ _ hsplit (Q'.add_eqv_congr_left _ _ _ hbranch)

/-! ## 5. Documentation: PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED here (genuine, axiom-clean):

  * `treeCount_loop_closed`, `dcLoopBranch_closed` — the loop branch of the
    deletion–contraction recursor, CLOSED unconditionally (general `w`), via the
    already-PROVED `spansMinEdges`;
  * `edgeProd_const_map`, `gsum_map` — the relabel-invariance of the constant
    `edgeProd` and the general `gsum` map-collapse;
  * `Csum_nonloop_const_reduced` — the non-loop `Csum` identity for the constant
    (hard-core) weight, REDUCED to the single correctly-guarded BFS residual
    `SpansContractLt` (the identity is FALSE for general `w` — refuted — but TRUE
    for the relabel-invariant constant weight).

NAMED-open (NOT faked, left UNINHABITED):

  * `TreeCountContractProof.SpansContractLt` — the oriented connectivity
    contraction-invariance (⟸ `SpansContractProof.ReachTransport`), the SOLE
    residual both non-loop halves reduce to.

Together with `treeCountContractGuarded` (weightless `treeCount` non-loop, from
`SpansContractLt`) and `dc_loop_Csum` (loop `Csum`, general), the ENTIRE
deletion–contraction recursor for the constant hard-core weight is thus either
closed or reduced to `SpansContractLt` alone.  This is fixed-spacing
strong-coupling combinatorics, NOT the Clay Yang–Mills mass gap. -/

end YMGap.Continuum.PenroseConstWeightDC

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.PenroseConstWeightDC.treeCount_loop_closed
#print axioms YMGap.Continuum.PenroseConstWeightDC.dcLoopBranch_closed
#print axioms YMGap.Continuum.PenroseConstWeightDC.edgeProd_const_map
#print axioms YMGap.Continuum.PenroseConstWeightDC.gsum_map
#print axioms YMGap.Continuum.PenroseConstWeightDC.Csum_nonloop_const_reduced
