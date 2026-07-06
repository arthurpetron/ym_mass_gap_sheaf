/-
# The deletion–contraction contract for `Csum`: honest fragments + one refutation.

`Continuum/PenroseDomInduction.lean` proves the Penrose inequality
`|C(G)| ≤ τ(G)` by well-founded induction, *modulo* the named residual `DCHyp w`
— the deletion–contraction identities for the concrete signed sum `Csum` and the
spanning-tree count `treeCount`.  This module discharges the parts of `DCHyp`
that are genuinely true and — adversarially — **refutes** the part that the prior
audit mislabeled as "provable in principle".

## What is proved here (all axiom-clean)

  * `gsum_append`, `gsum_map_cons`, `gsum_const_mul` — the additive/`map`/scalar
    algebra of the guarded power-set sum `gsum` that underlies `Csum`.
  * `Csum_delete_split` — the **delete half** of `DCHyp`, for a GENERAL head
    `(a,b)`:  `C(n, (a,b)::rest) ≃ C(n, rest) + B⋆(a,b)`, where `B⋆(a,b)` is the
    `(a,b)`-containing branch sum (the object the contract half must identify).
    This is the honest content of the "definitional `sublists`-split".
  * `spans_self_loop` — a self-loop is invisible to connectivity:
    `spans n ((a,a)::A) = spans n A` (via `relaxEdge (a,a) = id`).
  * `dc_loop_Csum` — the **loop-branch `Csum` identity** of `DCHyp`, PROVED in
    FULL GENERALITY:  `C(n, (a,a)::rest) ≃ (1 + w a a)·C(n, rest)`.  No
    contraction, no relabelling — the self-loop factors cleanly.

## What is REFUTED here (the adversarial correction)

  * `dc_nonloop_Csum_refuted` — for a concrete repulsive weight `wc` (values in
    `{-1,0} ⊆ [-1,0]`), `DCHyp wc` is FALSE.  The non-loop `Csum` identity
    `C(n,(a,b)::rest) ≃ C(n,rest) + w a b · C(n-1, contractEdges a b rest)`
    demands, at `n=3, (a,b)=(0,1), rest=[(1,2)]`,
        `w 0 1 · w 1 2  ≃  w 0 1 · w 0 1`,
    because `contractEdges 0 1 [(1,2)] = [(0,1)]` and `edgeProd` re-evaluates `w`
    at the RELABELLED endpoints `(0,1)`, silently discarding the original weight
    `w 1 2` of the contracted edge `(1,2)`.  With `w 0 1 = -1`, `w 1 2 = 0` this
    is `0 ≃ 1`.  Hence `DCHyp w` is **not inhabitable for general repulsive `w`**:
    the concrete `Csum w (n-1) (contractEdges …)` carries the WRONG edge weights.
    (It *is* true for relabel-invariant — e.g. constant/hard-core — weights.)

## Honest verdict on the `DCHyp` "contract half"

  * loop `Csum` half      — PROVED (`dc_loop_Csum`), general `w`.
  * delete half (both)    — PROVED (`Csum_delete_split`), general `w`.
  * non-loop `Csum` half  — REFUTED for general `w` (`dc_nonloop_Csum_refuted`);
    true only for relabel-invariant weights.  This is a genuine defect in the
    `DCHyp`/`Csum` object as stated, not a missing lemma.
  * treeCount halves      — weightless and TRUE, reduced to two named
    combinatorial residuals (`SpansMinEdges`, `TreeCountContract`); the loop
    treeCount identity follows from `SpansMinEdges` (a spanning subgraph on `n`
    vertices has `≥ n-1` edges), stated precisely below.

Nothing is faked; `DCHyp` remains UNINHABITED (correctly — it is false for
general `w`).  Mathlib-free; `Q'`/`Nat`/`List` core only.
-/

import YMGap.Continuum.PenroseDomInduction

namespace YMGap.Continuum.PenroseDCContract

open YMGap.Constructive
open YMGap.Continuum.PenroseDomInduction

/-! ## 1. The guarded power-set sum `gsum` (the shape of `Csum`) -/

/-- The guarded additive fold over an explicit power-set list: sum of `f A` over
`A` in `L` for which the boolean guard `P A` holds.  `Csum w n edges` is exactly
`gsum (edgeProd w) (spans n) (sublists edges)` (definitionally). -/
def gsum (f : List Edge → Q') (P : List Edge → Bool) : List (List Edge) → Q' :=
  fun L => L.foldr (fun A acc => if P A = true then f A + acc else acc) 0

theorem gsum_nil (f : List Edge → Q') (P : List Edge → Bool) : gsum f P [] = 0 := rfl

theorem gsum_cons_pos (f : List Edge → Q') (P : List Edge → Bool)
    (a : List Edge) (L : List (List Edge)) (h : P a = true) :
    gsum f P (a :: L) = f a + gsum f P L := by
  show (if P a = true then f a + gsum f P L else gsum f P L) = f a + gsum f P L
  rw [if_pos h]

theorem gsum_cons_neg (f : List Edge → Q') (P : List Edge → Bool)
    (a : List Edge) (L : List (List Edge)) (h : P a = false) :
    gsum f P (a :: L) = gsum f P L := by
  show (if P a = true then f a + gsum f P L else gsum f P L) = gsum f P L
  rw [if_neg (by rw [h]; exact Bool.false_ne_true)]

/-- The `gsum` of an append splits additively (up to `Q'.eqv`). -/
theorem gsum_append (f : List Edge → Q') (P : List Edge → Bool)
    (L1 L2 : List (List Edge)) :
    (gsum f P (L1 ++ L2)).eqv (gsum f P L1 + gsum f P L2) := by
  induction L1 with
  | nil =>
    show (gsum f P L2).eqv ((0 : Q') + gsum f P L2)
    rw [Q'.zero_add']
    exact Q'.eqv_refl _
  | cons a t ih =>
    cases hP : P a with
    | true =>
      show (gsum f P (a :: (t ++ L2))).eqv (gsum f P (a :: t) + gsum f P L2)
      rw [gsum_cons_pos f P a (t ++ L2) hP, gsum_cons_pos f P a t hP]
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (f a) _ _ ih) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv (f a) (gsum f P t) (gsum f P L2))
    | false =>
      show (gsum f P (a :: (t ++ L2))).eqv (gsum f P (a :: t) + gsum f P L2)
      rw [gsum_cons_neg f P a (t ++ L2) hP, gsum_cons_neg f P a t hP]
      exact ih

/-- The `gsum` over a `(e :: ·)`-prepended power-set collapses to a `gsum` over
the un-prepended list with `f`/`P` precomposed with `e :: ·`. -/
theorem gsum_map_cons (f : List Edge → Q') (P : List Edge → Bool)
    (e : Edge) (L : List (List Edge)) :
    gsum f P (L.map (fun s => e :: s))
      = gsum (fun A => f (e :: A)) (fun A => P (e :: A)) L := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    show gsum f P ((e :: a) :: t.map (fun s => e :: s))
       = gsum (fun A => f (e :: A)) (fun A => P (e :: A)) (a :: t)
    cases hP : P (e :: a) with
    | true =>
      rw [gsum_cons_pos f P (e :: a) _ hP, ih,
          gsum_cons_pos (fun A => f (e :: A)) (fun A => P (e :: A)) a t hP]
    | false =>
      rw [gsum_cons_neg f P (e :: a) _ hP, ih,
          gsum_cons_neg (fun A => f (e :: A)) (fun A => P (e :: A)) a t hP]

/-- A constant factor pulls out of a `gsum` (up to `Q'.eqv`). -/
theorem gsum_const_mul (c : Q') (f : List Edge → Q') (P : List Edge → Bool)
    (L : List (List Edge)) :
    (gsum (fun A => c * f A) P L).eqv (c * gsum f P L) := by
  induction L with
  | nil =>
    show (0 : Q').eqv (c * 0)
    exact Q'.eqv_symm (Q'.mul_zero_eqv c)
  | cons a t ih =>
    cases hP : P a with
    | true =>
      rw [gsum_cons_pos (fun A => c * f A) P a t hP, gsum_cons_pos f P a t hP]
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (c * f a) _ _ ih) ?_
      exact Q'.eqv_symm (Q'.mul_add_eqv c (f a) (gsum f P t))
    | false =>
      rw [gsum_cons_neg (fun A => c * f A) P a t hP, gsum_cons_neg f P a t hP]
      exact ih

/-! ## 2. `Csum` is a `gsum`; the delete-half split -/

/-- `Csum` is definitionally the guarded power-set sum. -/
theorem Csum_eq_gsum (w : Nat → Nat → Q') (n : Nat) (edges : List Edge) :
    Csum w n edges = gsum (edgeProd w) (spans n) (sublists edges) := rfl

/-- **The delete half of `DCHyp` (GENERAL head `(a,b)`, PROVED).**
`C(n, (a,b)::rest) ≃ C(n, rest) + B⋆`, where the branch sum
`B⋆ = gsum (edgeProd w ∘ ((a,b)::·)) (spans n ∘ ((a,b)::·)) (sublists rest)` is
the sum over the subsets that CONTAIN the head edge.  The contract half of
`DCHyp` is exactly the claim `B⋆ ≃ w a b · C(n-1, contractEdges a b rest)` —
which `dc_nonloop_Csum_refuted` shows is false for general `w`. -/
theorem Csum_delete_split (w : Nat → Nat → Q') (n a b : Nat) (rest : List Edge) :
    (Csum w n ((a, b) :: rest)).eqv
      (Csum w n rest
        + gsum (fun A => edgeProd w ((a, b) :: A))
               (fun A => spans n ((a, b) :: A)) (sublists rest)) := by
  show (gsum (edgeProd w) (spans n)
          (sublists rest ++ (sublists rest).map (fun s => (a, b) :: s))).eqv _
  refine Q'.eqv_trans _ _ _ (gsum_append _ _ _ _) ?_
  rw [gsum_map_cons]
  exact Q'.eqv_refl _

/-! ## 3. A self-loop is invisible to connectivity -/

/-- Relaxing across a self-loop `(a,a)` never changes the reachable set. -/
theorem relaxEdge_selfloop (a : Nat) (R : List Nat) : relaxEdge (a, a) R = R := by
  show (if a ∈ R then addV a R else if a ∈ R then addV a R else R) = R
  cases hd : decide (a ∈ R) with
  | true =>
    have hm : a ∈ R := of_decide_eq_true hd
    rw [if_pos hm]
    show (if a ∈ R then R else a :: R) = R
    rw [if_pos hm]
  | false =>
    have hm : a ∉ R := of_decide_eq_false hd
    rw [if_neg hm, if_neg hm]

/-- One relaxation pass ignores a leading self-loop. -/
theorem relax_selfloop (a : Nat) (A : List Edge) (R : List Nat) :
    relax ((a, a) :: A) R = relax A R := by
  show relaxEdge (a, a) (A.foldr relaxEdge R) = A.foldr relaxEdge R
  exact relaxEdge_selfloop a _

/-- The full BFS closure ignores a leading self-loop. -/
theorem reachClosure_selfloop (a : Nat) (A : List Edge) :
    ∀ (k : Nat) (R : List Nat),
      reachClosure k ((a, a) :: A) R = reachClosure k A R := by
  intro k
  induction k with
  | zero => intro R; rfl
  | succ k ih =>
    intro R
    show reachClosure k ((a, a) :: A) (relax ((a, a) :: A) R)
       = reachClosure k A (relax A R)
    rw [relax_selfloop]; exact ih (relax A R)

/-- **A self-loop is invisible to spanning connectivity.** -/
theorem spans_self_loop (n a : Nat) (A : List Edge) :
    spans n ((a, a) :: A) = spans n A := by
  show decide (∀ i, i < n → i ∈ reachClosure n ((a, a) :: A) [0])
     = decide (∀ i, i < n → i ∈ reachClosure n A [0])
  rw [reachClosure_selfloop]

/-! ## 4. The loop-branch `Csum` identity of `DCHyp` (PROVED, general `w`) -/

/-- **The loop-branch `Csum` identity of `DCHyp`, PROVED in full generality.**
For any repulsive-or-not weight `w`,
    `C(n, (a,a)::rest) ≃ (1 + w a a) · C(n, rest)`.
The self-loop factors out cleanly (no contraction, no vertex relabelling), so —
unlike the non-loop branch — this half of `DCHyp` is honestly true for every
`w`. -/
theorem dc_loop_Csum (w : Nat → Nat → Q') (n a : Nat) (rest : List Edge) :
    (Csum w n ((a, a) :: rest)).eqv ((1 + w a a) * Csum w n rest) := by
  -- delete-split at head (a,a)
  have hsplit := Csum_delete_split w n a a rest
  -- identify the branch sum with `w a a · C(n, rest)`
  have hbranch :
      (gsum (fun A => edgeProd w ((a, a) :: A))
            (fun A => spans n ((a, a) :: A)) (sublists rest)).eqv
        (w a a * Csum w n rest) := by
    -- rewrite the guard (self-loop invisible) and the value (factor `w a a`)
    have hP : (fun A => spans n ((a, a) :: A)) = spans n :=
      funext (fun A => spans_self_loop n a A)
    have hf : (fun A => edgeProd w ((a, a) :: A))
        = (fun A => w a a * edgeProd w A) := funext (fun _ => rfl)
    rw [hP, hf]
    exact gsum_const_mul (w a a) (edgeProd w) (spans n) (sublists rest)
  -- assemble: C((a,a)::rest) ≃ C(rest) + w a a · C(rest) ≃ (1 + w a a)·C(rest)
  refine Q'.eqv_trans _ _ _ hsplit ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hbranch) ?_
  -- (C + w·C) ≃ (1 + w)·C
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (1 + w a a) (Csum w n rest)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (Csum w n rest) 1 (w a a)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (Q'.mul_one_eqv (Csum w n rest))) ?_
  exact Q'.add_eqv_congr_left _ _ _ (Q'.mul_comm_eqv (Csum w n rest) (w a a))

/-! ## 5. Refutation of the non-loop `Csum` contract half (adversarial) -/

/-- A concrete repulsive weight: `-1` on the ordered pair `(0,1)`, `0` elsewhere.
Values lie in `{-1, 0} ⊆ [-1, 0]`, so `wc` is admissible for `penroseIneq`. -/
def wc (a b : Nat) : Q' := if a = 0 ∧ b = 1 then (-1 : Q') else 0

theorem wc_repulsive : ∀ a b, (-1 : Q') ≤ wc a b ∧ wc a b ≤ (0 : Q') := by
  intro a b
  show (-1 : Q') ≤ (if a = 0 ∧ b = 1 then (-1 : Q') else 0)
     ∧ (if a = 0 ∧ b = 1 then (-1 : Q') else 0) ≤ (0 : Q')
  split <;> exact ⟨by decide, by decide⟩

/-- **The non-loop `Csum` contract half of `DCHyp` is FALSE for general `w`.**
`DCHyp wc` is not inhabited: instantiating the non-loop identity at
`n=3, (a,b)=(0,1), rest=[(1,2)]` forces `Csum wc 3 [(0,1),(1,2)] ≃ 0 + 1`, i.e.
`0 ≃ 1`.  The defect: `contractEdges 0 1 [(1,2)] = [(0,1)]`, and
`Csum wc 2 [(0,1)]` evaluates `wc` at the RELABELLED endpoints, using `wc 0 1`
in place of the original edge weight `wc 1 2`.  Contraction relabels vertices and
`edgeProd` re-reads `w` at the new labels, so the identity can only hold for
relabel-invariant (e.g. constant/hard-core) weights. -/
theorem dc_nonloop_Csum_refuted : ¬ DCHyp wc := by
  intro h
  have hne : (0 : Nat) ≠ 1 := by decide
  have hCeqv := ((h 3 0 1 [(1, 2)]).1 hne).1
  revert hCeqv
  decide

/-! ## 6. The weightless treeCount halves — precise named residuals

The `Csum` halves above settle the analytic content of `DCHyp`.  The `treeCount`
halves are WEIGHTLESS (pure counting) and TRUE; they reduce to two standard
finite-combinatorial facts, stated here as named residuals (mirroring the
`DCHyp` residual style — genuine, provable-in-principle, left uninhabited). -/

/-- **`SpansMinEdges` — "spanning ⟹ ≥ n-1 edges".**  A connected spanning
subgraph on `n` vertices has at least `n-1` edges.  Over the concrete BFS: if
every vertex `< n` is reachable from `0` in `(n, A)` then `n ≤ |A| + 1` (each
edge introduces at most one new vertex to the reachable set, giving an injection
from the `n` reachable vertices minus the seed into `A`).  This DISCHARGES the
loop-branch treeCount identity `treeCount n ((a,a)::rest) = treeCount n rest`:
the head-containing subsets `(a,a)::s` that span with `|(a,a)::s| = n-1` require
`spans n s` with `|s| = n-2 < n-1`, which `SpansMinEdges` forbids. -/
def SpansMinEdges : Prop :=
  ∀ (n : Nat) (A : List Edge), spans n A = true → n ≤ A.length + 1

/-- **`TreeCountContract` — the non-loop treeCount contraction bijection.**
For a non-loop head `(a,b)`, `treeCount n ((a,b)::rest) = treeCount n rest +
treeCount (n-1) (contractEdges a b rest)`.  The `+treeCount n rest` is the
delete half (subsets omitting the head; a `sublists`-split); the
`+treeCount (n-1) (contractEdges a b rest)` is the genuine contraction bijection
`s ↦ contractEdges a b s` between {spanning trees of `G` through `(a,b)`} and
{spanning trees of `G/e`}, using contraction-invariance of connectivity
(`spans n ((a,b)::s) = spans (n-1) (contractEdges a b s)`) and the length
bookkeeping `|(a,b)::s| = |contractEdges a b s| + 1`.  Weightless, hence immune
to the `Csum` weight-relabelling defect that refutes the non-loop `Csum` half. -/
def TreeCountContract : Prop :=
  ∀ (n a b : Nat) (rest : List Edge), a ≠ b →
    treeCount n ((a, b) :: rest)
      = treeCount n rest + treeCount (n - 1) (contractEdges a b rest)

end YMGap.Continuum.PenroseDCContract

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.PenroseDCContract.gsum_append
#print axioms YMGap.Continuum.PenroseDCContract.gsum_map_cons
#print axioms YMGap.Continuum.PenroseDCContract.gsum_const_mul
#print axioms YMGap.Continuum.PenroseDCContract.Csum_delete_split
#print axioms YMGap.Continuum.PenroseDCContract.spans_self_loop
#print axioms YMGap.Continuum.PenroseDCContract.dc_loop_Csum
#print axioms YMGap.Continuum.PenroseDCContract.dc_nonloop_Csum_refuted
