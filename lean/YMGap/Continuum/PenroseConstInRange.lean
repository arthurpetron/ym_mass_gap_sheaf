/-
# The Penrose inequality `|C(G)| ≤ τ(G)` for the constant hard-core weight,
#   IN-RANGE — the mechanical finish of leg (P), with the refuted `DCHyp`
#   residual DISCHARGED (no longer a hypothesis).

`Continuum/PenroseDomInduction.lean` proves the Penrose inequality
`|C(G)| ≤ τ(G)` by fuel induction *modulo* the residual `DCHyp w` — the
deletion–contraction identities for `Csum`/`treeCount`.  Two facts about that
residual are already established in-tree:

* the general-`w` non-loop `Csum` identity is machine-REFUTED
  (`PenroseDCContract.dc_nonloop_Csum_refuted`): `edgeProd` re-reads `w` at the
  RELABELLED endpoints, so it fails unless `w` is relabel-invariant;
* the unguarded connectivity contraction `SpansContractLt` / `ReachTransport` is
  ALSO false (`SpansContractInRange.*_unguarded_false`): the fixed-fuel BFS only
  saturates when every label is `< n` (`InRange`).

Both defects are cured for the physically-relevant CONSTANT (hard-core) weight
`wConst c` (`-1 ≤ c ≤ 0`) over IN-RANGE graphs.  This module threads `InRange`
through the whole deletion–contraction recursor and closes the Penrose
inequality for `wConst c` **without any `DCHyp` hypothesis** — the load-bearing
combinatorial residual of leg (P) is thereby DISCHARGED, not merely reduced.

## What is PROVED here (all axiom-clean, genuine, non-vacuous)

  * `gsum_guard_congr` — a `gsum` congruence under pointwise agreement of the
    guard on the actual power-set members (the tool that lets the guarded, in-range
    connectivity identity replace the false global funext).
  * `Csum_nonloop_const_inRange` — the **const-`Csum` non-loop guarded half**: for
    `a < b < n` and `InRange n rest`,
        `C(n,(a,b)::rest) ≃ C(n,rest) + c·C(n-1, contractEdges a b rest)`,
    now consuming the PROVED `spansContractLt_inRange` (per member) instead of the
    unsatisfiable unguarded `SpansContractLt`.  This is the const-weight mirror of
    the already-closed weightless `treeCountContract_inRange` half.
  * `relaxEdge_swap` / `spans_head_swap` / `Csum_headswap_const` /
    `treeCount_head_swap` — the **undirected head re-orientation**: the head edge
    of the recursor is orientation-blind (`relaxEdge (a,b) = relaxEdge (b,a)`), so
    `spans`, and hence `Csum (wConst c)` and `treeCount`, are invariant under
    swapping the head endpoints.  This closes the `a > b` branch by reducing it to
    the oriented `b < a` non-loop identity.
  * `penroseIneqConst_fuel` / `penroseIneqConst` — the **Penrose inequality for the
    constant hard-core weight, IN-RANGE**, PROVED by fuel induction with NO
    `DCHyp`: loop head (`a=b`, `dc_loop_Csum` + `treeCount_loop_closed`), oriented
    non-loop head (`a<b`, the guarded halves) and re-oriented head (`a>b`, via the
    head-swap), all in-range at every recursion step (edges stay `< n` under
    deletion and contraction).
  * `penroseDomConst_of_pin` — leg (P) `penroseDom` for the const weight, reduced
    to the single `UrsellPinConst` residual (the Ursell coefficient identity),
    with the Penrose inequality now a THEOREM.
  * `treeGraphReductionOfConst` / `treeGraphBound_of_const` — assembling the
    reduction: from `UrsellPinConst` + Cayley leg (C) + `CubicEulerBound` leg (A),
    CONSTRUCT a `TreeGraphBound` (discharging the atom (T′)
    `TreeGraphBound.tree_graph`).  Leg (P)'s Penrose inequality is no longer a
    residual.

## Named residuals remaining for (T′) (NOT faked, left UNINHABITED)

  * `UrsellPinConst` — the Ursell↔connected-graph coefficient identity
    `n!·|φ^T(Y)| = |C(adjGraph Y)|` with the const weight, over an IN-RANGE polymer
    connectivity graph (vertices `{0,…,n-1}`).  The Ursell pin.
  * Cayley leg (C) `treeCount Y ≤ n^{n-2}` (`hCayley`).
  * `TreeGraphBoundProgress.CubicEulerBound` leg (A) `(1+1/n)^n ≤ 3`.

## Honest scope

Fixed-spacing strong-coupling combinatorics (`ρ₄ = 15/32`; hard-core pair factor
`c ∈ [-1,0]`).  This DISCHARGES the leg-(P) Penrose inequality (the sole new
mathematics of the tree-graph reduction) for the const weight in-range, removing
the refuted `DCHyp` from the critical path.  It does NOT close (T′) — the Ursell
pin, Cayley, and `CubicEulerBound` are the residuals that remain — and it is NOT
the spacing-uniform continuum modulus.  The Clay Yang–Mills mass gap is OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1/6/8)

Mathlib-free; only `Q'` / `Nat` / `List` / `Bool` core.  No `Classical.*`, no
`Real`, no `native_decide`, no `sorry` / new `axiom`.  All witnesses `Type`-level
data.  Every load-bearing declaration gated with `#print axioms` (permitted:
`propext` / `Quot.sound`).
-/

import YMGap.Continuum.PenroseConstWeightDC
import YMGap.Continuum.SpansContractInRange
import YMGap.Continuum.PenroseDCContract
import YMGap.Continuum.TreeGraphBoundProgress

namespace YMGap.Continuum.PenroseConstInRange

open YMGap.Constructive
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.PenroseDCContract
open YMGap.Continuum.PenroseConstWeightDC
open YMGap.Continuum.TreeCountContractProof
open YMGap.Continuum.SpansContractInRange
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.Ursell4DProgress
open YMGap.Continuum.TreeGraphBoundProgress

/-! ## 0. A `gsum` congruence under pointwise guard agreement on members -/

/-- **`gsum_guard_congr`.**  If two guards `P`, `P'` agree on every actual member
of the power-set list `L`, the guarded sums coincide.  This is what lets the
IN-RANGE connectivity identity `spansContractLt_inRange` (which only holds on
in-range sublists) replace the FALSE global funext of the guard. -/
theorem gsum_guard_congr (f : List Edge → Q') (P P' : List Edge → Bool) :
    ∀ (L : List (List Edge)), (∀ A, A ∈ L → P A = P' A) → gsum f P L = gsum f P' L
  | [], _ => rfl
  | a :: t, h => by
      have ha : P a = P' a := h a List.mem_cons_self
      have ht : gsum f P t = gsum f P' t :=
        gsum_guard_congr f P P' t (fun A hA => h A (List.mem_cons_of_mem _ hA))
      cases hp : P a with
      | true =>
          have hp' : P' a = true := by rw [← ha]; exact hp
          rw [gsum_cons_pos f P a t hp, gsum_cons_pos f P' a t hp', ht]
      | false =>
          have hp' : P' a = false := by rw [← ha]; exact hp
          rw [gsum_cons_neg f P a t hp, gsum_cons_neg f P' a t hp', ht]

/-! ## 1. The const-`Csum` non-loop guarded half (IN-RANGE) -/

/-- **`Csum_nonloop_const_inRange` (PROVED from `spansContractLt_inRange`).**  The
non-loop deletion–contraction identity for the constant weight `wConst c` on an
ORIENTED in-range head `a < b < n`, `InRange n rest`:

    C(n,(a,b)::rest) ≃ C(n,rest) + c·C(n-1, contractEdges a b rest).

The general-`w` form is FALSE (`dc_nonloop_Csum_refuted`), and the unguarded
`SpansContractLt` it used is also FALSE; this version is TRUE because
`edgeProd (wConst c)` is relabel-invariant (`edgeProd_const_map`) and the guard
`spans` agreement holds per in-range member (`spansContractLt_inRange` via
`inRange_of_mem_sublists`, threaded through `gsum_guard_congr`). -/
theorem Csum_nonloop_const_inRange (c : Q') (n a b : Nat) (rest : List Edge)
    (hab : a < b) (hbn : b < n) (hIR : InRange n rest) :
    (Csum (wConst c) n ((a, b) :: rest)).eqv
      (Csum (wConst c) n rest
        + c * Csum (wConst c) (n - 1) (contractEdges a b rest)) := by
  have hsplit := Csum_delete_split (wConst c) n a b rest
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
    rw [hval]
    exact gsum_guard_congr (edgeProd (wConst c))
      (fun A => spans (n - 1) (contractEdges a b A))
      (fun s => spans n ((a, b) :: s)) (sublists rest)
      (fun s hs => (spansContractLt_inRange n a b s hab hbn
        (inRange_of_mem_sublists hIR s hs)).symm)
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
  exact Q'.eqv_trans _ _ _ hsplit (Q'.add_eqv_congr_left _ _ _ hbranch)

/-! ## 2. The undirected head re-orientation (`a > b` ⟶ `b < a`) -/

/-- Relaxing across an edge is orientation-blind: `relaxEdge (a,b) = relaxEdge (b,a)`. -/
theorem relaxEdge_swap (a b : Nat) (R : List Nat) :
    relaxEdge (a, b) R = relaxEdge (b, a) R := by
  show (if a ∈ R then addV b R else if b ∈ R then addV a R else R)
     = (if b ∈ R then addV a R else if a ∈ R then addV b R else R)
  by_cases ha : a ∈ R <;> by_cases hb : b ∈ R
  · rw [if_pos ha, if_pos hb]
    show addV b R = addV a R
    unfold addV; rw [if_pos hb, if_pos ha]
  · rw [if_pos ha, if_neg hb, if_pos ha]
  · rw [if_neg ha, if_pos hb, if_pos hb]
  · rw [if_neg ha, if_neg hb, if_neg hb, if_neg ha]

/-- One relaxation pass is head-orientation-blind. -/
theorem relax_swap (a b : Nat) (A : List Edge) (R : List Nat) :
    relax ((a, b) :: A) R = relax ((b, a) :: A) R := by
  show relaxEdge (a, b) (relax A R) = relaxEdge (b, a) (relax A R)
  exact relaxEdge_swap a b (relax A R)

/-- The full BFS closure is head-orientation-blind. -/
theorem reachClosure_swap (a b : Nat) (A : List Edge) :
    ∀ (k : Nat) (R : List Nat),
      reachClosure k ((a, b) :: A) R = reachClosure k ((b, a) :: A) R := by
  intro k
  induction k with
  | zero => intro R; rfl
  | succ k ih =>
      intro R
      show reachClosure k ((a, b) :: A) (relax ((a, b) :: A) R)
         = reachClosure k ((b, a) :: A) (relax ((b, a) :: A) R)
      rw [relax_swap]; exact ih (relax ((b, a) :: A) R)

/-- **`spans_head_swap`.**  Spanning connectivity is blind to head-edge
orientation: `spans n ((a,b)::A) = spans n ((b,a)::A)`. -/
theorem spans_head_swap (n a b : Nat) (A : List Edge) :
    spans n ((a, b) :: A) = spans n ((b, a) :: A) := by
  show decide (∀ i, i < n → i ∈ reachClosure n ((a, b) :: A) [0])
     = decide (∀ i, i < n → i ∈ reachClosure n ((b, a) :: A) [0])
  rw [reachClosure_swap]

/-- **`Csum_headswap_const`.**  The constant-weight signed sum is blind to
head-edge orientation (the value `c` is symmetric and `spans` is head-swap
invariant): `C(n,(a,b)::rest) ≃ C(n,(b,a)::rest)`. -/
theorem Csum_headswap_const (c : Q') (n a b : Nat) (rest : List Edge) :
    (Csum (wConst c) n ((a, b) :: rest)).eqv (Csum (wConst c) n ((b, a) :: rest)) := by
  have hab := Csum_delete_split (wConst c) n a b rest
  have hba := Csum_delete_split (wConst c) n b a rest
  have hbranch :
      gsum (fun A => edgeProd (wConst c) ((a, b) :: A))
           (fun A => spans n ((a, b) :: A)) (sublists rest)
    = gsum (fun A => edgeProd (wConst c) ((b, a) :: A))
           (fun A => spans n ((b, a) :: A)) (sublists rest) := by
    have hf : (fun A => edgeProd (wConst c) ((a, b) :: A))
        = (fun A => edgeProd (wConst c) ((b, a) :: A)) := by
      funext A
      show wConst c a b * edgeProd (wConst c) A = wConst c b a * edgeProd (wConst c) A
      rfl
    have hP : (fun A => spans n ((a, b) :: A))
        = (fun A => spans n ((b, a) :: A)) := by
      funext A; exact spans_head_swap n a b A
    rw [hf, hP]
  refine Q'.eqv_trans _ _ _ hab ?_
  rw [hbranch]
  exact Q'.eqv_symm hba

/-- **`treeCount_head_swap`.**  The spanning-tree count is blind to head-edge
orientation: `treeCount n ((a,b)::rest) = treeCount n ((b,a)::rest)`. -/
theorem treeCount_head_swap (n a b : Nat) (rest : List Edge) :
    treeCount n ((a, b) :: rest) = treeCount n ((b, a) :: rest) := by
  rw [treeCount_cons_split n (a, b) rest, treeCount_cons_split n (b, a) rest]
  have hpred :
      (fun s => spans n ((a, b) :: s) && decide (((a, b) :: s).length = n - 1))
    = (fun s => spans n ((b, a) :: s) && decide (((b, a) :: s).length = n - 1)) := by
    funext s
    show (spans n ((a, b) :: s) && decide (s.length + 1 = n - 1))
       = (spans n ((b, a) :: s) && decide (s.length + 1 = n - 1))
    rw [spans_head_swap n a b s]
  rw [hpred]

/-! ## 3. The Penrose inequality for the constant hard-core weight (IN-RANGE) -/

/-- The non-loop analytic assembly (shared by the `a<b` and `a>b` branches): from
the two induction hypotheses, the const-`Csum` non-loop identity, and the
`treeCount` non-loop identity, conclude `|C((a,b)::rest)| ≤ τ((a,b)::rest)`.  The
factor is `c ∈ [-1,0] ⊆ [-1,1]`. -/
theorem nonloop_assemble (c : Q') (hc1 : (-1 : Q') ≤ c) (hc2 : c ≤ (0 : Q'))
    (n a b : Nat) (rest G : List Edge)
    (IHdel : Q'.abs (Csum (wConst c) n rest) ≤ Q'.ofNat (treeCount n rest))
    (IHcon : Q'.abs (Csum (wConst c) (n - 1) G) ≤ Q'.ofNat (treeCount (n - 1) G))
    (hCeqv : (Csum (wConst c) n ((a, b) :: rest)).eqv
        (Csum (wConst c) n rest + c * Csum (wConst c) (n - 1) G))
    (hTeq : treeCount n ((a, b) :: rest) = treeCount n rest + treeCount (n - 1) G) :
    Q'.abs (Csum (wConst c) n ((a, b) :: rest))
      ≤ Q'.ofNat (treeCount n ((a, b) :: rest)) := by
  have hu1 : (-1 : Q') ≤ c := hc1
  have hu2 : c ≤ 1 := Q'.le_trans' _ _ _ hc2 (by decide)
  have hfac := abs_mul_le_of_factor hu1 hu2 IHcon
  have h1 := Q'.le_of_eqv (Q'.abs_eqv_congr hCeqv)
  have h2 := Q'.abs_add_le' (Csum (wConst c) n rest) (c * Csum (wConst c) (n - 1) G)
  have h4 :
      Q'.abs (Csum (wConst c) n rest) + Q'.abs (c * Csum (wConst c) (n - 1) G)
        ≤ Q'.ofNat (treeCount n rest) + Q'.ofNat (treeCount (n - 1) G) :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ _ IHdel)
      (Q'.add_le_add_left _ _ _ hfac)
  have h5 :
      Q'.ofNat (treeCount n rest) + Q'.ofNat (treeCount (n - 1) G)
        ≤ Q'.ofNat (treeCount n rest + treeCount (n - 1) G) :=
    Q'.ge_of_eqv (ofNat_add_eqv _ _)
  have hgoal :=
    Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 (Q'.le_trans' _ _ _ h4 h5))
  rw [hTeq]; exact hgoal

/-- **`penroseIneqConst_fuel` (PROVED — the IN-RANGE Penrose induction, NO
`DCHyp`).**  For the constant hard-core weight `wConst c` (`-1 ≤ c ≤ 0`) and any
IN-RANGE graph, `|C(G)| ≤ τ(G)`.  The deletion–contraction step is discharged in
each of the three head cases by the genuinely-proved in-range identities (loop,
oriented non-loop, re-oriented non-loop); `InRange` is preserved under deletion
(sublist) and contraction (`relabelV_lt`), so the recursion stays in range. -/
theorem penroseIneqConst_fuel (c : Q') (hc1 : (-1 : Q') ≤ c) (hc2 : c ≤ (0 : Q')) :
    ∀ (fuel n : Nat) (edges : List Edge),
      edges.length ≤ fuel → InRange n edges →
      Q'.abs (Csum (wConst c) n edges) ≤ Q'.ofNat (treeCount n edges) := by
  have hw : ∀ x y, (-1 : Q') ≤ wConst c x y ∧ wConst c x y ≤ (0 : Q') :=
    fun _ _ => ⟨hc1, hc2⟩
  intro fuel
  induction fuel with
  | zero =>
    intro n edges hlen _
    cases edges with
    | nil => exact penrose_base (wConst c) n
    | cons e rest => simp only [List.length_cons] at hlen; omega
  | succ k ih =>
    intro n edges hlen hIR
    cases edges with
    | nil => exact penrose_base (wConst c) n
    | cons e rest =>
      obtain ⟨a, b⟩ := e
      have hrest : rest.length ≤ k := by simp only [List.length_cons] at hlen; omega
      have hIRrest : InRange n rest := fun e he => hIR e (List.mem_cons_of_mem _ he)
      have hIRhead : a < n ∧ b < n := hIR (a, b) List.mem_cons_self
      have IHdel : Q'.abs (Csum (wConst c) n rest) ≤ Q'.ofNat (treeCount n rest) :=
        ih n rest hrest hIRrest
      rcases Nat.lt_trichotomy a b with hlt | heq | hgt
      · -- a < b : oriented non-loop
        have hbn : b < n := hIRhead.2
        have hIRcon : InRange (n - 1) (contractEdges a b rest) := by
          intro e he
          rcases List.mem_map.mp he with ⟨p, hpA, hpe⟩
          rw [← hpe]
          have hp := hIRrest p hpA
          exact ⟨SpansContractProof.relabelV_lt a b p.1 n hlt hbn hp.1,
                 SpansContractProof.relabelV_lt a b p.2 n hlt hbn hp.2⟩
        have hconlen : (contractEdges a b rest).length ≤ k := by
          show (rest.map (fun e => (relabelV a b e.1, relabelV a b e.2))).length ≤ k
          rw [List.length_map]; exact hrest
        have IHcon : Q'.abs (Csum (wConst c) (n - 1) (contractEdges a b rest))
            ≤ Q'.ofNat (treeCount (n - 1) (contractEdges a b rest)) :=
          ih (n - 1) _ hconlen hIRcon
        have hCeqv := Csum_nonloop_const_inRange c n a b rest hlt hbn hIRrest
        have hTeq := treeCountContract_inRange hIRrest hlt hbn
        exact nonloop_assemble c hc1 hc2 n a b rest (contractEdges a b rest)
          IHdel IHcon hCeqv hTeq
      · -- a = b : loop
        subst heq
        have hCeqv := dc_loop_Csum (wConst c) n a rest
        have hTeq := treeCount_loop_closed n a rest
        have hu2 : (1 + wConst c a a) ≤ 1 :=
          Q'.le_trans' _ _ _
            (Q'.add_le_add_left 1 (wConst c a a) 0 (hw a a).2) (by decide)
        have hu1 : (-1 : Q') ≤ 1 + wConst c a a := by
          have hpos : (0 : Q') ≤ 1 + wConst c a a :=
            Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ (1 : Q') + (-1))
              (Q'.add_le_add_left 1 (-1) (wConst c a a) (hw a a).1)
          exact Q'.le_trans' _ _ _ (by decide : (-1 : Q') ≤ 0) hpos
        have hfac := abs_mul_le_of_factor hu1 hu2 IHdel
        have h1 := Q'.le_of_eqv (Q'.abs_eqv_congr hCeqv)
        have hgoal := Q'.le_trans' _ _ _ h1 hfac
        rw [hTeq]; exact hgoal
      · -- a > b : re-oriented non-loop (head-swap to b < a)
        have han : a < n := hIRhead.1
        have hIRcon : InRange (n - 1) (contractEdges b a rest) := by
          intro e he
          rcases List.mem_map.mp he with ⟨p, hpA, hpe⟩
          rw [← hpe]
          have hp := hIRrest p hpA
          exact ⟨SpansContractProof.relabelV_lt b a p.1 n hgt han hp.1,
                 SpansContractProof.relabelV_lt b a p.2 n hgt han hp.2⟩
        have hconlen : (contractEdges b a rest).length ≤ k := by
          show (rest.map (fun e => (relabelV b a e.1, relabelV b a e.2))).length ≤ k
          rw [List.length_map]; exact hrest
        have IHcon : Q'.abs (Csum (wConst c) (n - 1) (contractEdges b a rest))
            ≤ Q'.ofNat (treeCount (n - 1) (contractEdges b a rest)) :=
          ih (n - 1) _ hconlen hIRcon
        have hCeqv0 := Csum_nonloop_const_inRange c n b a rest hgt han hIRrest
        have hswapC := Csum_headswap_const c n a b rest
        have hCeqv : (Csum (wConst c) n ((a, b) :: rest)).eqv
            (Csum (wConst c) n rest
              + c * Csum (wConst c) (n - 1) (contractEdges b a rest)) :=
          Q'.eqv_trans _ _ _ hswapC hCeqv0
        have hTeq0 := treeCountContract_inRange hIRrest hgt han
        have hswapT := treeCount_head_swap n a b rest
        have hTeq : treeCount n ((a, b) :: rest)
            = treeCount n rest + treeCount (n - 1) (contractEdges b a rest) := by
          rw [hswapT]; exact hTeq0
        exact nonloop_assemble c hc1 hc2 n a b rest (contractEdges b a rest)
          IHdel IHcon hCeqv hTeq

/-- **`penroseIneqConst` (PROVED — the Penrose inequality for the constant
hard-core weight, IN-RANGE).**  For `-1 ≤ c ≤ 0` and any in-range graph
`(n, edges)`, `|C(G)| ≤ τ(G)`.  NO `DCHyp` hypothesis — the deletion–contraction
recursor is fully discharged for this weight. -/
theorem penroseIneqConst (c : Q') (hc1 : (-1 : Q') ≤ c) (hc2 : c ≤ (0 : Q'))
    (n : Nat) (edges : List Edge) (hIR : InRange n edges) :
    Q'.abs (Csum (wConst c) n edges) ≤ Q'.ofNat (treeCount n edges) :=
  penroseIneqConst_fuel c hc1 hc2 edges.length n edges (Nat.le_refl _) hIR

/-! ## 4. Leg (P) `penroseDom` for the const weight, and the (T′) reduction -/

/-- **`UrsellPinConst S c` — the const-weight, IN-RANGE Ursell pin (named
residual).**  Supplies the polymer connectivity graph `(adjN Y, adjE Y)` with
vertices `{0,…,adjN Y - 1}` (hence `adjInRange`), the pinned weight `phiT Y`, and
the pinned tree count, with the Ursell coefficient identity `ursell` pinning
`phiT` to `|C(adjGraph Y)|/n!`.  Left UNINHABITED — the Ursell coefficient
identity is the sole remaining leg-(P) residual (the Penrose inequality itself is
now the theorem `penroseIneqConst`). -/
structure UrsellPinConst (S : SepLattice) (c : Q') where
  /-- Vertex count of the connectivity graph of `Y`. -/
  adjN : Polymer S.toLattice → Nat
  /-- Edge list of the connectivity graph of `Y`. -/
  adjE : Polymer S.toLattice → List Edge
  /-- The connectivity graph lives on the vertex set `{0,…,adjN Y - 1}`. -/
  adjInRange : ∀ Y, InRange (adjN Y) (adjE Y)
  /-- The pinned truncated Ursell weight `|φ^T(Y)|`. -/
  phiT : Polymer S.toLattice → Q'
  /-- `|φ^T(Y)| ≥ 0`. -/
  phiT_nonneg : ∀ Y, (0 : Q') ≤ phiT Y
  /-- The pinned spanning-tree count. -/
  treeCountF : Polymer S.toLattice → Nat
  /-- **`ursell` — pins `phiT`**: `n!·phiT Y = |C(adjGraph Y)|` (const weight). -/
  ursell : ∀ Y, (Q'.ofNat (fact (Polymer.size Y)) * phiT Y).eqv
    (Q'.abs (Csum (wConst c) (adjN Y) (adjE Y)))
  /-- **`countPin` — pins the tree count**: `treeCount Y = τ(adjGraph Y)`. -/
  countPin : ∀ Y, treeCountF Y = treeCount (adjN Y) (adjE Y)

/-- **`penroseDomConst_of_pin` — leg (P) `penroseDom`, PROVED for the const weight
modulo only the Ursell pin.**  For the genuinely-pinned `phiT`,
`n!·phiT Y ≤ ofNat(treeCountF Y)`, by composing the Ursell identity with the now-
PROVED in-range Penrose inequality `penroseIneqConst` and the tree-count pin.  NO
`DCHyp`: the deletion–contraction residual is discharged. -/
theorem penroseDomConst_of_pin {S : SepLattice} {c : Q'}
    (hc1 : (-1 : Q') ≤ c) (hc2 : c ≤ (0 : Q'))
    (P : UrsellPinConst S c) (Y : Polymer S.toLattice) :
    Q'.ofNat (fact (Polymer.size Y)) * P.phiT Y ≤ Q'.ofNat (P.treeCountF Y) := by
  have h1 : Q'.ofNat (fact (Polymer.size Y)) * P.phiT Y
      ≤ Q'.abs (Csum (wConst c) (P.adjN Y) (P.adjE Y)) :=
    Q'.le_of_eqv (P.ursell Y)
  have h2 : Q'.abs (Csum (wConst c) (P.adjN Y) (P.adjE Y))
      ≤ Q'.ofNat (treeCount (P.adjN Y) (P.adjE Y)) :=
    penroseIneqConst c hc1 hc2 (P.adjN Y) (P.adjE Y) (P.adjInRange Y)
  have h3 : Q'.abs (Csum (wConst c) (P.adjN Y) (P.adjE Y))
      ≤ Q'.ofNat (P.treeCountF Y) := by
    rw [P.countPin Y]; exact h2
  exact Q'.le_trans' _ _ _ h1 h3

/-- **`treeGraphReductionOfConst` — the `TreeGraphReduction` datum, with leg (P)
DISCHARGED.**  From the const-weight Ursell pin and the Cayley leg (C), assemble a
`TreeGraphReduction`: the `penroseDom` field is the PROVED `penroseDomConst_of_pin`
(no `DCHyp`), the `cayleyMax` field is the Cayley input.  Leg (P) is no longer a
free field. -/
def treeGraphReductionOfConst {S : SepLattice} {w : Q'} {r : Rep} {c : Q'}
    (hc1 : (-1 : Q') ≤ c) (hc2 : c ≤ (0 : Q'))
    (P : UrsellPinConst S c)
    (hCayley : ∀ Y, P.treeCountF Y ≤ (Polymer.size Y) ^ (Polymer.size Y - 2)) :
    TreeGraphReduction S w r where
  phiT := P.phiT
  phiT_nonneg := P.phiT_nonneg
  treeCount := P.treeCountF
  penroseDom := fun Y => penroseDomConst_of_pin hc1 hc2 P Y
  cayleyMax := hCayley

/-- **`treeGraphBound_of_const` — the (T′) discharge, modulo the three residuals.**
From the const-weight Ursell pin, the Cayley leg (C), and the `CubicEulerBound`
leg (A), CONSTRUCT a `TreeGraphBound` — i.e. discharge the once-abstract
tree-graph atom `TreeGraphBound.tree_graph` (T′).  The leg-(P) Penrose inequality
is a THEOREM here (`penroseIneqConst`); the remaining inputs are the Ursell pin,
Cayley, and `CubicEulerBound`.  Conditional (three hypotheses) — NOT an
unconditional closure. -/
def treeGraphBound_of_const {S : SepLattice} {w : Q'} {r : Rep} {c : Q'}
    (hc1 : (-1 : Q') ≤ c) (hc2 : c ≤ (0 : Q'))
    (P : UrsellPinConst S c)
    (hCayley : ∀ Y, P.treeCountF Y ≤ (Polymer.size Y) ^ (Polymer.size Y - 2))
    (hEuler : CubicEulerBound) :
    TreeGraphBound S w r :=
  (treeGraphReductionOfConst hc1 hc2 P hCayley).toBound hEuler

end YMGap.Continuum.PenroseConstInRange

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.PenroseConstInRange.gsum_guard_congr
#print axioms YMGap.Continuum.PenroseConstInRange.Csum_nonloop_const_inRange
#print axioms YMGap.Continuum.PenroseConstInRange.relaxEdge_swap
#print axioms YMGap.Continuum.PenroseConstInRange.spans_head_swap
#print axioms YMGap.Continuum.PenroseConstInRange.Csum_headswap_const
#print axioms YMGap.Continuum.PenroseConstInRange.treeCount_head_swap
#print axioms YMGap.Continuum.PenroseConstInRange.penroseIneqConst_fuel
#print axioms YMGap.Continuum.PenroseConstInRange.penroseIneqConst
#print axioms YMGap.Continuum.PenroseConstInRange.penroseDomConst_of_pin
#print axioms YMGap.Continuum.PenroseConstInRange.treeGraphReductionOfConst
#print axioms YMGap.Continuum.PenroseConstInRange.treeGraphBound_of_const
