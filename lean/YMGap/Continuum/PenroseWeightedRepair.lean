/-
# The WEIGHTED-EDGE repair of the refuted non-loop deletion–contraction `Csum` identity.

`Continuum/PenroseDCContract.lean` **refutes** the non-loop `Csum` contract half of
`DCHyp` for a concrete repulsive weight (`dc_nonloop_Csum_refuted`).  The exposed
BUG is *not* combinatorial: it is that `Csum w (n-1) (contractEdges a b rest)`
re-reads the weight function `w` at the RELABELLED vertex endpoints, silently
discarding the original weight of the contracted edge.  At
`n=3, (a,b)=(0,1), rest=[(1,2)]` contraction turns `(1,2)` into `(0,1)` and
`edgeProd` re-evaluates `w 0 1` in place of the true `w 1 2`, forcing `0 ≃ 1`.

This module performs the **weighted-edge repair**: carry each edge's weight as
DATA *on* the edge, so contraction relabels the two vertex components but PRESERVES
the weight component.  With the weight attached to the edge, the value side of the
identity no longer re-reads any weight function — the sole remaining ingredient is
the (weightless, genuinely true) connectivity contraction-invariance.

## The weighted objects (all concrete, computable)

  * `WEdge := Nat × Nat × Q'`   — endpoints + carried weight.
  * `wedgeProd A`               — `∏_{e∈A} e.2.2` (reads the CARRIED weight only).
  * `endpoints e`, `wspans n A` — connectivity reading ONLY the endpoints
    (projects `WEdge` to `Edge`, then reuses `spans`).
  * `CsumW n edges`             — the guarded signed sum over `sublists edges`,
    the exact weighted mirror of `Csum`.
  * `relabelW a b`, `wcontractEdges a b rest` — contraction relabelling ONLY the
    first two components (`relabelV a b`) while PRESERVING `e.2.2`.

## What is PROVED here (all axiom-clean)

  * `CsumW_delete_split` — the delete half, general head `(a,b,c)` (weighted mirror
    of `Csum_delete_split`).
  * `CsumW_loop` — the loop-branch weighted `Csum` identity, general `c`
    (weighted mirror of `dc_loop_Csum`):  `C(n,(a,a,c)::rest) ≃ (1+c)·C(n,rest)`.
  * **`CsumW_nonloop_contract`** — THE LOAD-BEARING DELIVERABLE.  For `a ≠ b`,
    `a < n`, `b < n`:
        `C(n,(a,b,c)::rest) ≃ C(n,rest) + c·C(n-1, wcontractEdges a b rest)`,
    for EVERY carried weight `c`.  This is the exact analog of the refuted
    identity, now TRUE: `wcontractEdges` preserves each edge's carried weight, so
    the value side carries the *original* weight `c` of the head edge (not a
    re-read of any weight function), and the weight-relabelling defect that
    refuted the weightless version is gone.  The only input consumed is the
    weightless connectivity residual `SpansContract`.

## The single named residual consumed (genuinely TRUE, uninhabited here)

  * `SpansContract` — edge-contraction invariance of connectivity, WEIGHTLESS:
        `a ≠ b → a < n → b < n →
           spans n ((a,b)::A) = spans (n-1) (contractEdges a b A)`.
    Guarded by `a < n`, `b < n` (the intended regime) so that it is TRUE — dropping
    the guards makes it false at out-of-range instances (e.g. `n=2,(a,b)=(0,5)`),
    exactly as the unguarded `DCHyp` is uninhabited.  This is the pure connectivity
    fact underlying `TreeCountContract`, now isolated as its own named residual and
    NOT refutable (unlike the weight half it is weightless).  Left UNINHABITED —
    nothing here is faked; the weighted `Csum` identity is proved *from* it.

## Honest scope

The repair shows leg P (`penroseDom`) is fixable once weights are edge-attached:
the refuted non-loop `Csum` identity becomes a genuine theorem.  The full weighted
`penroseIneq` additionally needs the weightless `treeCount` halves
(`SpansMinEdges`, `TreeCountContract` in `PenroseDCContract`), left as named
residuals there; those are not attempted here.

Mathlib-free; `Q'` / `Nat` / `List` core only.  No `Classical.*`, no `Real`, no
`native_decide`, no `sorry` / new `axiom`.  Every load-bearing declaration gated
with `#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.PenroseDCContract

namespace YMGap.Continuum.PenroseWeightedRepair

open YMGap.Constructive
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.PenroseDCContract

/-! ## 1. Weighted edges and their invariants -/

/-- A weighted edge: two vertex labels together with a carried `Q'` weight. -/
abbrev WEdge : Type := Nat × Nat × Q'

/-- The edge-subset weight `∏_{e∈A} e.2.2`, reading the CARRIED weight component
(never a weight function). -/
def wedgeProd (A : List WEdge) : Q' := A.foldr (fun e acc => e.2.2 * acc) 1

/-- Forget the carried weight, keeping only the endpoints. -/
def endpoints (e : WEdge) : Edge := (e.1, e.2.1)

/-- Weighted connectivity: reads ONLY the endpoints, reusing the weightless
`spans`. -/
def wspans (n : Nat) (A : List WEdge) : Bool := spans n (A.map endpoints)

/-- The **weighted signed connected-spanning-subgraph sum** `C(G)` (mirror of
`Csum`; guard reads endpoints, value reads carried weights). -/
def CsumW (n : Nat) (edges : List WEdge) : Q' :=
  (sublists edges).foldr
    (fun A acc => if wspans n A = true then wedgeProd A + acc else acc) 0

/-- Contraction relabelling on a weighted edge: relabel the two vertex components
(`relabelV a b`) and PRESERVE the carried weight `e.2.2`. -/
def relabelW (a b : Nat) (e : WEdge) : WEdge :=
  (relabelV a b e.1, relabelV a b e.2.1, e.2.2)

/-- Contract the head edge `(a,b)` in a weighted tail, preserving every weight. -/
def wcontractEdges (a b : Nat) (rest : List WEdge) : List WEdge :=
  rest.map (relabelW a b)

/-! ## 2. The guarded power-set sum `wgsum` (the shape of `CsumW`) -/

/-- The guarded additive fold over an explicit power-set list (weighted mirror of
`gsum`). -/
def wgsum (f : List WEdge → Q') (P : List WEdge → Bool) :
    List (List WEdge) → Q' :=
  fun L => L.foldr (fun A acc => if P A = true then f A + acc else acc) 0

theorem wgsum_cons_pos (f : List WEdge → Q') (P : List WEdge → Bool)
    (a : List WEdge) (L : List (List WEdge)) (h : P a = true) :
    wgsum f P (a :: L) = f a + wgsum f P L := by
  show (if P a = true then f a + wgsum f P L else wgsum f P L) = f a + wgsum f P L
  rw [if_pos h]

theorem wgsum_cons_neg (f : List WEdge → Q') (P : List WEdge → Bool)
    (a : List WEdge) (L : List (List WEdge)) (h : P a = false) :
    wgsum f P (a :: L) = wgsum f P L := by
  show (if P a = true then f a + wgsum f P L else wgsum f P L) = wgsum f P L
  rw [if_neg (by rw [h]; exact Bool.false_ne_true)]

/-- `CsumW` is definitionally the guarded power-set sum. -/
theorem CsumW_eq_wgsum (n : Nat) (edges : List WEdge) :
    CsumW n edges = wgsum wedgeProd (wspans n) (sublists edges) := rfl

/-- The `wgsum` of an append splits additively (up to `Q'.eqv`). -/
theorem wgsum_append (f : List WEdge → Q') (P : List WEdge → Bool)
    (L1 L2 : List (List WEdge)) :
    (wgsum f P (L1 ++ L2)).eqv (wgsum f P L1 + wgsum f P L2) := by
  induction L1 with
  | nil =>
    show (wgsum f P L2).eqv ((0 : Q') + wgsum f P L2)
    rw [Q'.zero_add']
    exact Q'.eqv_refl _
  | cons a t ih =>
    cases hP : P a with
    | true =>
      show (wgsum f P (a :: (t ++ L2))).eqv (wgsum f P (a :: t) + wgsum f P L2)
      rw [wgsum_cons_pos f P a (t ++ L2) hP, wgsum_cons_pos f P a t hP]
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (f a) _ _ ih) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv (f a) (wgsum f P t) (wgsum f P L2))
    | false =>
      show (wgsum f P (a :: (t ++ L2))).eqv (wgsum f P (a :: t) + wgsum f P L2)
      rw [wgsum_cons_neg f P a (t ++ L2) hP, wgsum_cons_neg f P a t hP]
      exact ih

/-- The `wgsum` over a `φ`-image of a power-set collapses to a `wgsum` over the
pre-image with `f`/`P` precomposed with `φ` (general mirror of `gsum_map_cons`). -/
theorem wgsum_map (f : List WEdge → Q') (P : List WEdge → Bool)
    (φ : List WEdge → List WEdge) (L : List (List WEdge)) :
    wgsum f P (L.map φ)
      = wgsum (fun A => f (φ A)) (fun A => P (φ A)) L := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    show wgsum f P (φ a :: t.map φ)
       = wgsum (fun A => f (φ A)) (fun A => P (φ A)) (a :: t)
    cases hP : P (φ a) with
    | true =>
      rw [wgsum_cons_pos f P (φ a) _ hP, ih,
          wgsum_cons_pos (fun A => f (φ A)) (fun A => P (φ A)) a t hP]
    | false =>
      rw [wgsum_cons_neg f P (φ a) _ hP, ih,
          wgsum_cons_neg (fun A => f (φ A)) (fun A => P (φ A)) a t hP]

/-- A constant factor pulls out of a `wgsum` (up to `Q'.eqv`). -/
theorem wgsum_const_mul (c : Q') (f : List WEdge → Q') (P : List WEdge → Bool)
    (L : List (List WEdge)) :
    (wgsum (fun A => c * f A) P L).eqv (c * wgsum f P L) := by
  induction L with
  | nil =>
    show (0 : Q').eqv (c * 0)
    exact Q'.eqv_symm (Q'.mul_zero_eqv c)
  | cons a t ih =>
    cases hP : P a with
    | true =>
      rw [wgsum_cons_pos (fun A => c * f A) P a t hP, wgsum_cons_pos f P a t hP]
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (c * f a) _ _ ih) ?_
      exact Q'.eqv_symm (Q'.mul_add_eqv c (f a) (wgsum f P t))
    | false =>
      rw [wgsum_cons_neg (fun A => c * f A) P a t hP, wgsum_cons_neg f P a t hP]
      exact ih

/-- Pointwise-equal value/guard give equal `wgsum` (plain `Eq`, no `eqv`). -/
theorem wgsum_congr (f1 f2 : List WEdge → Q') (P1 P2 : List WEdge → Bool)
    (hf : ∀ A, f1 A = f2 A) (hP : ∀ A, P1 A = P2 A) (L : List (List WEdge)) :
    wgsum f1 P1 L = wgsum f2 P2 L := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    show (if P1 a = true then f1 a + wgsum f1 P1 t else wgsum f1 P1 t)
       = (if P2 a = true then f2 a + wgsum f2 P2 t else wgsum f2 P2 t)
    rw [hf a, hP a, ih]

/-! ## 3. Weight preservation and connectivity bookkeeping under contraction -/

/-- Contraction preserves every carried weight, hence the subset weight. -/
theorem wedgeProd_map_relabelW (a b : Nat) (s : List WEdge) :
    wedgeProd (s.map (relabelW a b)) = wedgeProd s := by
  induction s with
  | nil => rfl
  | cons e t ih =>
    show e.2.2 * wedgeProd (t.map (relabelW a b)) = e.2.2 * wedgeProd t
    rw [ih]

/-- Projecting the contracted weighted edges onto endpoints agrees with contracting
the projected endpoints (`endpoints ∘ relabelW = contract ∘ endpoints`). -/
theorem endpoints_map_relabelW (a b : Nat) (s : List WEdge) :
    (s.map (relabelW a b)).map endpoints = contractEdges a b (s.map endpoints) := by
  induction s with
  | nil => rfl
  | cons e t ih =>
    show (relabelV a b e.1, relabelV a b e.2.1) :: (t.map (relabelW a b)).map endpoints
       = (relabelV a b e.1, relabelV a b e.2.1) :: contractEdges a b (t.map endpoints)
    rw [ih]

/-- `sublists` commutes with a componentwise `map` (a clean structural identity). -/
theorem cons_map_comm {α β : Type} (g : α → β) (x : α) (K : List (List α)) :
    (K.map (fun s => s.map g)).map (fun s => g x :: s)
      = (K.map (fun s => x :: s)).map (fun s => s.map g) := by
  induction K with
  | nil => rfl
  | cons k rest ih =>
    show (g x :: k.map g) :: (rest.map (fun s => s.map g)).map (fun s => g x :: s)
       = (g x :: k.map g) :: (rest.map (fun s => x :: s)).map (fun s => s.map g)
    rw [ih]

theorem sublists_map {α β : Type} (g : α → β) (l : List α) :
    sublists (l.map g) = (sublists l).map (fun s => s.map g) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    show sublists (t.map g) ++ (sublists (t.map g)).map (fun s => g a :: s)
       = (sublists t ++ (sublists t).map (fun s => a :: s)).map (fun s => s.map g)
    rw [ih, List.map_append, cons_map_comm g a (sublists t)]

/-! ## 4. The weightless connectivity residual -/

/-- **`SpansContract` — the weightless edge-contraction invariance of
connectivity.**  For a non-loop head `(a,b)` with both endpoints in range,
    `spans n ((a,b)::A) = spans (n-1) (contractEdges a b A)`.
The `a < n`, `b < n` guards pin the intended regime — without them the identity is
false at out-of-range instances (`n=2, (a,b)=(0,5)`: LHS `false`, RHS `true`), just
as the unguarded `DCHyp` is uninhabited.  This is the pure connectivity content of
`TreeCountContract`, weightless (hence NOT subject to the weight-relabelling
refutation) and TRUE.  Left UNINHABITED — the single named residual consumed by the
weighted `Csum` identity below. -/
def SpansContract : Prop :=
  ∀ (n a b : Nat) (A : List Edge), a ≠ b → a < n → b < n →
    spans n ((a, b) :: A) = spans (n - 1) (contractEdges a b A)

/-- A leading self-loop is invisible to weighted connectivity (reuses the
weightless `spans_self_loop`). -/
theorem wspans_self_loop (n a : Nat) (c : Q') (A : List WEdge) :
    wspans n ((a, a, c) :: A) = wspans n A := by
  show spans n ((a, a) :: A.map endpoints) = spans n (A.map endpoints)
  exact PenroseDCContract.spans_self_loop n a (A.map endpoints)

/-- The guard-matching lemma: the head-containing guard equals the contracted
guard, via `SpansContract` (endpoints only; the carried weight `c` is irrelevant). -/
theorem wspans_contract (hSC : SpansContract) (n a b : Nat) (c : Q')
    (hab : a ≠ b) (han : a < n) (hbn : b < n) (s : List WEdge) :
    wspans n ((a, b, c) :: s) = wspans (n - 1) (s.map (relabelW a b)) := by
  show spans n ((a, b) :: s.map endpoints)
     = spans (n - 1) ((s.map (relabelW a b)).map endpoints)
  rw [endpoints_map_relabelW]
  exact hSC n a b (s.map endpoints) hab han hbn

/-! ## 5. The weighted delete half -/

/-- **The delete half, general head `(a,b,c)` (weighted mirror of
`Csum_delete_split`).**  `C(n,(a,b,c)::rest) ≃ C(n,rest) + B⋆`, where the branch
sum `B⋆` runs over the subsets that CONTAIN the head edge. -/
theorem CsumW_delete_split (n a b : Nat) (c : Q') (rest : List WEdge) :
    (CsumW n ((a, b, c) :: rest)).eqv
      (CsumW n rest
        + wgsum (fun A => wedgeProd ((a, b, c) :: A))
                (fun A => wspans n ((a, b, c) :: A)) (sublists rest)) := by
  show (wgsum wedgeProd (wspans n)
          (sublists rest ++ (sublists rest).map (fun s => (a, b, c) :: s))).eqv _
  refine Q'.eqv_trans _ _ _ (wgsum_append _ _ _ _) ?_
  rw [wgsum_map wedgeProd (wspans n) (fun s => (a, b, c) :: s) (sublists rest)]
  exact Q'.eqv_refl _

/-! ## 6. The loop-branch weighted `Csum` identity (PROVED, general `c`) -/

/-- **The loop-branch weighted `Csum` identity (weighted mirror of
`dc_loop_Csum`).**  `C(n,(a,a,c)::rest) ≃ (1 + c)·C(n,rest)`, for every carried
weight `c`.  The self-loop factors cleanly; the carried weight `c` is the loop
factor. -/
theorem CsumW_loop (n a : Nat) (c : Q') (rest : List WEdge) :
    (CsumW n ((a, a, c) :: rest)).eqv ((1 + c) * CsumW n rest) := by
  have hsplit := CsumW_delete_split n a a c rest
  have hbranch :
      (wgsum (fun A => wedgeProd ((a, a, c) :: A))
             (fun A => wspans n ((a, a, c) :: A)) (sublists rest)).eqv
        (c * CsumW n rest) := by
    have hP : (fun A => wspans n ((a, a, c) :: A)) = wspans n :=
      funext (fun A => wspans_self_loop n a c A)
    have hf : (fun A => wedgeProd ((a, a, c) :: A))
        = (fun A : List WEdge => c * wedgeProd A) := funext (fun _ => rfl)
    rw [hP, hf]
    exact wgsum_const_mul c wedgeProd (wspans n) (sublists rest)
  refine Q'.eqv_trans _ _ _ hsplit ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hbranch) ?_
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (1 + c) (CsumW n rest)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (CsumW n rest) 1 c) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (Q'.mul_one_eqv (CsumW n rest))) ?_
  exact Q'.add_eqv_congr_left _ _ _ (Q'.mul_comm_eqv (CsumW n rest) c)

/-! ## 7. THE WEIGHTED NON-LOOP CONTRACTION IDENTITY (the repair) -/

/-- **`CsumW_nonloop_contract` — the weighted non-loop deletion–contraction `Csum`
identity, TRUE (the repair of the refuted weightless identity).**

For `a ≠ b`, `a < n`, `b < n`, and EVERY carried weight `c`:

    C(n, (a,b,c)::rest) ≃ C(n, rest) + c · C(n-1, wcontractEdges a b rest).

Contrast with `dc_nonloop_Csum_refuted`: there the contracted sum re-read the
weight function at the relabelled endpoints, forcing `0 ≃ 1`.  Here the head
weight `c` is carried explicitly, and `wcontractEdges` preserves each edge's weight
(`wedgeProd_map_relabelW`), so the value side carries the *original* weight `c` —
the defect is gone.  The only input consumed is the weightless connectivity
residual `SpansContract`. -/
theorem CsumW_nonloop_contract (hSC : SpansContract)
    (n a b : Nat) (c : Q') (rest : List WEdge)
    (hab : a ≠ b) (han : a < n) (hbn : b < n) :
    (CsumW n ((a, b, c) :: rest)).eqv
      (CsumW n rest + c * CsumW (n - 1) (wcontractEdges a b rest)) := by
  have hsplit := CsumW_delete_split n a b c rest
  -- B⋆ ≃ c · S,  with S the head-guarded value sum.
  have hbranch :
      (wgsum (fun A => wedgeProd ((a, b, c) :: A))
             (fun A => wspans n ((a, b, c) :: A)) (sublists rest)).eqv
        (c * wgsum wedgeProd (fun A => wspans n ((a, b, c) :: A)) (sublists rest)) := by
    have hf : (fun A => wedgeProd ((a, b, c) :: A))
        = (fun A : List WEdge => c * wedgeProd A) := funext (fun _ => rfl)
    rw [hf]
    exact wgsum_const_mul c wedgeProd (fun A => wspans n ((a, b, c) :: A)) (sublists rest)
  -- S = C(n-1, wcontractEdges a b rest): weights preserved (value) + SpansContract (guard).
  have hS : wgsum wedgeProd (fun A => wspans n ((a, b, c) :: A)) (sublists rest)
      = CsumW (n - 1) (wcontractEdges a b rest) := by
    have e1 : CsumW (n - 1) (wcontractEdges a b rest)
        = wgsum (fun A => wedgeProd (A.map (relabelW a b)))
                (fun A => wspans (n - 1) (A.map (relabelW a b))) (sublists rest) := by
      show wgsum wedgeProd (wspans (n - 1)) (sublists (rest.map (relabelW a b))) = _
      rw [sublists_map]
      exact wgsum_map wedgeProd (wspans (n - 1)) (fun s => s.map (relabelW a b))
        (sublists rest)
    rw [e1]
    exact wgsum_congr wedgeProd (fun A => wedgeProd (A.map (relabelW a b)))
      (fun A => wspans n ((a, b, c) :: A))
      (fun A => wspans (n - 1) (A.map (relabelW a b)))
      (fun A => (wedgeProd_map_relabelW a b A).symm)
      (fun A => wspans_contract hSC n a b c hab han hbn A)
      (sublists rest)
  refine Q'.eqv_trans _ _ _ hsplit ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hbranch) ?_
  rw [hS]
  exact Q'.eqv_refl _

/-! ## 8. The weightless `treeCount` halves for a full weighted `penroseIneq`

The weighted `Csum` identity above settles the analytic (weight) content.  A full
weighted `penroseIneq` additionally needs the weightless `treeCount` halves, left
as named residuals in `PenroseDCContract`:

  * `PenroseDCContract.SpansMinEdges`  — "spanning ⟹ ≥ n-1 edges".
  * `PenroseDCContract.TreeCountContract` — the non-loop `treeCount` contraction
    bijection.

Both are weightless (pure counting), hence immune to the weight-relabelling defect,
and TRUE; they are not attempted here.  Note `wspans`/`treeCount` agree with
`spans`/`treeCount` on projected endpoints, so those residuals port unchanged to the
weighted setting via `endpoints`. -/

end YMGap.Continuum.PenroseWeightedRepair

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.PenroseWeightedRepair.wgsum_append
#print axioms YMGap.Continuum.PenroseWeightedRepair.wgsum_map
#print axioms YMGap.Continuum.PenroseWeightedRepair.wgsum_const_mul
#print axioms YMGap.Continuum.PenroseWeightedRepair.wgsum_congr
#print axioms YMGap.Continuum.PenroseWeightedRepair.wedgeProd_map_relabelW
#print axioms YMGap.Continuum.PenroseWeightedRepair.endpoints_map_relabelW
#print axioms YMGap.Continuum.PenroseWeightedRepair.sublists_map
#print axioms YMGap.Continuum.PenroseWeightedRepair.wspans_contract
#print axioms YMGap.Continuum.PenroseWeightedRepair.CsumW_delete_split
#print axioms YMGap.Continuum.PenroseWeightedRepair.CsumW_loop
#print axioms YMGap.Continuum.PenroseWeightedRepair.CsumW_nonloop_contract
