/-
# `ReachTransport` / `SpansContractLt`: the unguarded forms REFUTED, the
#   in-range forms PROVED — the BFS walk-transport core of leg (P), closed.

`Continuum/SpansContractProof.lean` names the weightless BFS residual
`ReachTransport` (the per-vertex reachability correspondence under the merge map
`relabelV a b`) and claims it "genuinely TRUE (brute-force validated over all
graphs on `n ≤ 4`) … NOT refutable"; `Continuum/TreeCountContractProof.lean`
names the spans-level `SpansContractLt` on the same claim.  Both consumers
(`Csum_nonloop_const_reduced`, `treeCountContractGuarded`,
`spansContractOriented_of_transport`) thread these as *hypotheses*.

Working this out adversarially (exhaustive machine search over the concrete
`reachClosure` BFS) reveals an HONEST CORRECTION: **both statements as written
are FALSE.**  They quantify over an ARBITRARY edge list `A : List Edge`, but the
fixed-fuel BFS `reachClosure n` (resp. `n-1`) only saturates when every vertex
label of `A` is `< n` (resp. the contraction is `< n-1`).  With an out-of-range
label a long detour needs more than `n` passes, and the merge-created shortcut
breaks the biconditional:

    n = 3, (a,b) = (0,1), A = [(0,3),(3,4),(2,4)]  (all guards `a<b`, `b<n` hold)
      spans 3 ((0,1)::A)                = true      (0—1, 0—3—4—2 connected)
      spans 2 (contractEdges 0 1 A)     = false     (needs fuel > 2)
    so `SpansContractLt` forces `true = false`; and at `i = 2`
      2 ∈ reachClosure 3 …             = true,
      relabelV 0 1 2 = 1 ∈ reachClosure 2 … = false,
    so `ReachTransport` forces `true ↔ false`.

Both refutations are machine-checked below (`spansContractLt_unguarded_false`,
`reachTransport_unguarded_false`).  The MISSING guard is the range condition
`InRange n A` (every endpoint of `A` is `< n`) — exactly the regime the
polymer/`adjGraph` objects live in (vertices `{0,…,n-1}`), and preserved by
contraction (`relabelV_lt` maps `< n` to `< n-1`).

## What is PROVED here (all axiom-clean, genuinely TRUE, non-vacuous)

  * **`reachTransport_inRange`** — THE BFS walk-transport core, the guarded
    `ReachTransport`.  For `a < b < n` and `InRange n A`, a vertex `i < n` is
    reached from `0` in `G = (n, (a,b)::A)` iff its merge image `relabelV a b i`
    is reached in the contraction `G/e = (n-1, contractEdges a b A)`.  Proved by
    the LEAST-FIXPOINT (closure) induction principle for the concrete BFS
    `reachClosure`: both directions are edge-closure inductions, using that the
    fixed-fuel closure SATURATES under `InRange` (bounded monotone chain in the
    `n`-element universe — `reach_sat`) so it is edge-closed (`reach_edgeClosed`),
    plus the merge arithmetic `relabelV_inj_or` (the map is injective off the
    collapsed pair `{a,b}`, which the head edge `(a,b)` re-identifies).
  * **`spansContractLt_inRange`** — the guarded spans-level identity
    `spans n ((a,b)::A) = spans (n-1)(contractEdges a b A)` for `a<b<n`,
    `InRange n A`, derived from `reachTransport_inRange` via the surjection
    `relabelV a b : {0,…,n-1} ↠ {0,…,n-2}` (`relabelV_lt`/`preimg`).

## What is REFUTED here (adversarial correction)

  * `reachTransport_unguarded_false : ¬ SpansContractProof.ReachTransport`.
  * `spansContractLt_unguarded_false : ¬ TreeCountContractProof.SpansContractLt`.

Both original defs (no `InRange` guard) are therefore UNINHABITABLE; the
consumers that thread them (`Csum_nonloop_const_reduced`, `treeCountContractGuarded`)
have an unsatisfiable hypothesis and must be re-pointed at the `InRange` forms
proved here to become applicable to a concrete graph.

## Honest scope

This closes the *sole open weightless BFS fact* of leg (P) — the walk-transport —
now genuinely PROVED (guarded) and axiom-clean, and corrects the record (the
unguarded claims are false).  It does NOT by itself inhabit `penroseIneq` /
`penroseDom` / the `(T′)` tree-graph atom: those additionally need the head
re-orientation (`a > b`) + `InRange`-threading through `penroseIneq_fuel`, leg
(C) Cayley, and the Ursell pin — named residuals elsewhere.  Fixed-spacing
strong-coupling combinatorics; NOT the spacing-uniform continuum modulus; the
Clay Yang–Mills mass gap remains OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1/6/8)

Mathlib-free; only `Nat` / `List` / `Bool` core.  No `Classical.*` (all
case-splits go through `Decidable` instances or concrete `decide`), no `Real`,
no `native_decide`, no `sorry` / new `axiom`.  Every load-bearing declaration is
gated with `#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.SpansMinEdgesProof
import YMGap.Continuum.TreeCountContractProof
import YMGap.Continuum.SpansContractProof

namespace YMGap.Continuum.SpansContractInRange

open YMGap.Continuum.PenroseDomInduction

/-! ## 0. The range guard -/

/-- Every endpoint of every edge of `A` is a vertex label `< n`.  This is the
guard that makes the fixed-fuel BFS `reachClosure n` saturate (and that the
unguarded `ReachTransport`/`SpansContractLt` silently assume). -/
def InRange (n : Nat) (A : List Edge) : Prop := ∀ e, e ∈ A → e.1 < n ∧ e.2 < n

/-! ## 1. Membership bookkeeping for `addV` / `relaxEdge` / `relax` -/

theorem mem_addV {x z : Nat} {R : List Nat} (h : z ∈ addV x R) : z = x ∨ z ∈ R := by
  unfold addV at h
  by_cases hx : x ∈ R
  · rw [if_pos hx] at h; exact Or.inr h
  · rw [if_neg hx] at h
    rcases List.mem_cons.mp h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1

theorem mem_addV_head (x : Nat) (R : List Nat) : x ∈ addV x R := by
  unfold addV
  by_cases hx : x ∈ R
  · rw [if_pos hx]; exact hx
  · rw [if_neg hx]; exact List.mem_cons_self

theorem addV_superset {x z : Nat} {R : List Nat} (h : z ∈ R) : z ∈ addV x R := by
  unfold addV
  by_cases hx : x ∈ R
  · rw [if_pos hx]; exact h
  · rw [if_neg hx]; exact List.mem_cons_of_mem _ h

theorem relaxEdge_superset {e : Edge} {z : Nat} {R : List Nat} (h : z ∈ R) :
    z ∈ relaxEdge e R := by
  unfold relaxEdge
  by_cases h1 : e.1 ∈ R
  · rw [if_pos h1]; exact addV_superset h
  · rw [if_neg h1]
    by_cases h2 : e.2 ∈ R
    · rw [if_pos h2]; exact addV_superset h
    · rw [if_neg h2]; exact h

theorem relax_superset : ∀ (A : List Edge) (R : List Nat) (z : Nat), z ∈ R → z ∈ relax A R := by
  intro A
  induction A with
  | nil => intro R z h; exact h
  | cons e t ih => intro R z h; exact relaxEdge_superset (ih R z h)

theorem reachClosure_superset :
    ∀ (k : Nat) (A : List Edge) (R : List Nat) (z : Nat), z ∈ R → z ∈ reachClosure k A R := by
  intro k
  induction k with
  | zero => intro A R z h; exact h
  | succ k ih => intro A R z h; exact ih A (relax A R) z (relax_superset A R z h)

/-! ## 2. The edge-closure induction principle (the "≤" direction) -/

/-- `T` is closed under the (undirected) adjacency of `A`. -/
def EdgeClosed (A : List Edge) (T : Nat → Prop) : Prop :=
  ∀ x y, T x → ((x, y) ∈ A ∨ (y, x) ∈ A) → T y

theorem relaxEdge_pres {A : List Edge} {T : Nat → Prop} {e : Edge} {acc : List Nat}
    (heA : e ∈ A) (hcl : EdgeClosed A T) (hacc : ∀ z, z ∈ acc → T z) :
    ∀ z, z ∈ relaxEdge e acc → T z := by
  intro z hz
  unfold relaxEdge at hz
  by_cases h1 : e.1 ∈ acc
  · rw [if_pos h1] at hz
    rcases mem_addV hz with hz' | hz'
    · have hTe1 : T e.1 := hacc _ h1
      have hTe2 : T e.2 := hcl e.1 e.2 hTe1 (Or.inl (show (e.1, e.2) ∈ A from heA))
      rw [hz']; exact hTe2
    · exact hacc _ hz'
  · rw [if_neg h1] at hz
    by_cases h2 : e.2 ∈ acc
    · rw [if_pos h2] at hz
      rcases mem_addV hz with hz' | hz'
      · have hTe2 : T e.2 := hacc _ h2
        have hTe1 : T e.1 := hcl e.2 e.1 hTe2 (Or.inr (show (e.1, e.2) ∈ A from heA))
        rw [hz']; exact hTe1
      · exact hacc _ hz'
    · rw [if_neg h2] at hz; exact hacc _ hz

theorem foldr_pres {A : List Edge} {T : Nat → Prop} (hcl : EdgeClosed A T) :
    ∀ (B : List Edge), (∀ e, e ∈ B → e ∈ A) → ∀ (acc : List Nat), (∀ z, z ∈ acc → T z) →
      ∀ z, z ∈ B.foldr relaxEdge acc → T z := by
  intro B
  induction B with
  | nil => intro _ acc hacc z hz; exact hacc z hz
  | cons e t ih =>
      intro hsub acc hacc z hz
      have heA : e ∈ A := hsub e List.mem_cons_self
      have hrec : ∀ z, z ∈ t.foldr relaxEdge acc → T z :=
        ih (fun e' h => hsub e' (List.mem_cons_of_mem _ h)) acc hacc
      exact relaxEdge_pres heA hcl hrec z hz

theorem relax_pres {A : List Edge} {T : Nat → Prop} {R : List Nat}
    (hcl : EdgeClosed A T) (hR : ∀ z, z ∈ R → T z) : ∀ z, z ∈ relax A R → T z :=
  foldr_pres hcl A (fun _ h => h) R hR

theorem reach_pres {A : List Edge} {T : Nat → Prop} (hcl : EdgeClosed A T) :
    ∀ (k : Nat) (R : List Nat), (∀ z, z ∈ R → T z) → ∀ z, z ∈ reachClosure k A R → T z := by
  intro k
  induction k with
  | zero => intro R hR z hz; exact hR z hz
  | succ k ih =>
      intro R hR z hz
      have hrelax : ∀ z, z ∈ relax A R → T z := relax_pres hcl hR
      exact ih (relax A R) hrelax z hz

/-- **The edge-closure induction principle.**  Any `A`-edge-closed predicate `T`
containing `0` contains the whole BFS closure `reachClosure k A [0]`. -/
theorem reach_ind {A : List Edge} {T : Nat → Prop} (hcl : EdgeClosed A T) (h0 : T 0) :
    ∀ (k : Nat) (z : Nat), z ∈ reachClosure k A [0] → T z := by
  intro k z hz
  refine reach_pres hcl k [0] ?_ z hz
  intro w hw
  rw [List.mem_singleton.mp hw]; exact h0

/-- The BFS closure stays `< N` when `A` is in range. -/
theorem reach_lt {N : Nat} {A : List Edge} (hIR : InRange N A) (hN : 0 < N) :
    ∀ (k z : Nat), z ∈ reachClosure k A [0] → z < N := by
  have hcl : EdgeClosed A (fun x => x < N) := by
    intro x y _ hxy
    rcases hxy with h | h
    · exact (hIR _ h).2
    · exact (hIR _ h).1
  exact reach_ind hcl hN

/-! ## 3. One BFS step across an edge, and `reachClosure_succ` -/

theorem reachClosure_succ (A : List Edge) (k : Nat) :
    ∀ (R : List Nat), reachClosure (k + 1) A R = relax A (reachClosure k A R) := by
  induction k with
  | zero => intro R; rfl
  | succ k ih =>
      intro R
      show reachClosure (k + 1) A (relax A R) = relax A (reachClosure (k + 1) A R)
      rw [ih (relax A R)]
      rfl

/-- If `x ∈ R` and `x,y` are adjacent in `A`, then one relaxation pass reaches `y`. -/
theorem relax_edge_mem {x y : Nat} :
    ∀ (A : List Edge) {R : List Nat}, x ∈ R → ((x, y) ∈ A ∨ (y, x) ∈ A) → y ∈ relax A R
  | [], R, _, h => by rcases h with h | h <;> exact absurd h List.not_mem_nil
  | e :: t, R, hx, h => by
      have hxacc : x ∈ relax t R := relax_superset t R x hx
      show y ∈ relaxEdge e (relax t R)
      by_cases hcase : ((x, y) ∈ t ∨ (y, x) ∈ t)
      · exact relaxEdge_superset (relax_edge_mem t hx hcase)
      · have hhead : (x, y) = e ∨ (y, x) = e := by
          rcases h with hh | hh
          · rcases List.mem_cons.mp hh with he | ht
            · exact Or.inl he
            · exact absurd (Or.inl ht) hcase
          · rcases List.mem_cons.mp hh with he | ht
            · exact Or.inr he
            · exact absurd (Or.inr ht) hcase
        rcases hhead with he | he
        · subst he
          show y ∈ relaxEdge (x, y) (relax t R)
          unfold relaxEdge
          rw [if_pos (show (x, y).1 ∈ relax t R from hxacc)]
          exact mem_addV_head y (relax t R)
        · subst he
          show y ∈ relaxEdge (y, x) (relax t R)
          unfold relaxEdge
          by_cases hx1 : (y, x).1 ∈ relax t R
          · rw [if_pos hx1]
            exact addV_superset (show y ∈ relax t R from hx1)
          · rw [if_neg hx1, if_pos (show (y, x).2 ∈ relax t R from hxacc)]
            exact mem_addV_head y (relax t R)

theorem reach_step_edge {A : List Edge} {k x y : Nat}
    (hx : x ∈ reachClosure k A [0]) (hxy : (x, y) ∈ A ∨ (y, x) ∈ A) :
    y ∈ reachClosure (k + 1) A [0] := by
  rw [reachClosure_succ A k [0]]
  exact relax_edge_mem A hx hxy

/-! ## 4. Monotonicity / membership-congruence of `relax` -/

theorem relaxEdge_mono {e : Edge} {R R' : List Nat} (hsub : ∀ z, z ∈ R → z ∈ R') :
    ∀ z, z ∈ relaxEdge e R → z ∈ relaxEdge e R' := by
  intro z hz
  unfold relaxEdge at hz ⊢
  by_cases h1 : e.1 ∈ R
  · rw [if_pos h1] at hz
    have h1' : e.1 ∈ R' := hsub _ h1
    rw [if_pos h1']
    rcases mem_addV hz with hz' | hz'
    · rw [hz']; exact mem_addV_head e.2 R'
    · exact addV_superset (hsub _ hz')
  · rw [if_neg h1] at hz
    by_cases h2 : e.2 ∈ R
    · rw [if_pos h2] at hz
      have h2' : e.2 ∈ R' := hsub _ h2
      by_cases h1' : e.1 ∈ R'
      · rw [if_pos h1']
        rcases mem_addV hz with hz' | hz'
        · rw [hz']; exact addV_superset h1'
        · exact addV_superset (hsub _ hz')
      · rw [if_neg h1', if_pos h2']
        rcases mem_addV hz with hz' | hz'
        · rw [hz']; exact mem_addV_head e.1 R'
        · exact addV_superset (hsub _ hz')
    · rw [if_neg h2] at hz
      show z ∈ relaxEdge e R'
      exact relaxEdge_superset (hsub _ hz)

theorem relax_mono {R R' : List Nat} (hsub : ∀ z, z ∈ R → z ∈ R') :
    ∀ (A : List Edge) (z : Nat), z ∈ relax A R → z ∈ relax A R' := by
  intro A
  induction A with
  | nil => intro z hz; exact hsub z hz
  | cons e t ih => intro z hz; exact relaxEdge_mono (fun w hw => ih w hw) z hz

/-- Membership-equivalence of vertex sets. -/
def MEqv (R R' : List Nat) : Prop := ∀ z, z ∈ R ↔ z ∈ R'

theorem relax_cong {A : List Edge} {R R' : List Nat} (h : MEqv R R') :
    MEqv (relax A R) (relax A R') := by
  intro z
  constructor
  · intro hz; exact relax_mono (fun w hw => (h w).mp hw) A z hz
  · intro hz; exact relax_mono (fun w hw => (h w).mpr hw) A z hz

theorem reach_incr {A : List Edge} {k z : Nat} (hz : z ∈ reachClosure k A [0]) :
    z ∈ reachClosure (k + 1) A [0] := by
  rw [reachClosure_succ A k [0]]
  exact relax_superset A (reachClosure k A [0]) z hz

theorem reach_zero (k : Nat) (A : List Edge) : (0 : Nat) ∈ reachClosure k A [0] :=
  reachClosure_superset k A [0] 0 List.mem_cons_self

/-! ## 5. Saturation: the fixed-fuel closure is a fixpoint under `InRange` -/

theorem reach_len_le {N : Nat} {A : List Edge} (hIR : InRange N A) (hN : 0 < N) (k : Nat) :
    (reachClosure k A [0]).length ≤ N := by
  have hnd : (reachClosure k A [0]).Nodup :=
    SpansMinEdgesProof.reachClosure_nodup k A [0] (by decide)
  have hsub : ∀ a, a ∈ reachClosure k A [0] → a ∈ SpansMinEdgesProof.downRange N := by
    intro a ha
    exact (SpansMinEdgesProof.mem_downRange N a).mpr (reach_lt hIR hN k a ha)
  have hle := CayleyPruferInjection.nodup_subset_length_le
    (reachClosure k A [0]) (SpansMinEdgesProof.downRange N) hnd hsub
  rw [SpansMinEdgesProof.length_downRange] at hle
  exact hle

/-- Constructive witness extraction from a failed bounded subset check. -/
theorem exists_mem_not (M : List Nat) :
    ∀ (L : List Nat), ¬ (∀ z, z ∈ L → z ∈ M) → ∃ z, z ∈ L ∧ z ∉ M
  | [], h => absurd (fun z hz => absurd hz List.not_mem_nil) h
  | a :: t, h => by
      by_cases ha : a ∈ M
      · have h' : ¬ (∀ z, z ∈ t → z ∈ M) := by
          intro hall
          apply h
          intro z hz
          rcases List.mem_cons.mp hz with he | ht
          · rw [he]; exact ha
          · exact hall z ht
        rcases exists_mem_not M t h' with ⟨z, hz, hnz⟩
        exact ⟨z, List.mem_cons_of_mem _ hz, hnz⟩
      · exact ⟨a, List.mem_cons_self, ha⟩

/-- One fuel step either stabilises (membership) or grows the closure by ≥ 1. -/
theorem chain_key {N : Nat} {A : List Edge} (hIR : InRange N A) (hN : 0 < N) (k : Nat) :
    (∀ z, z ∈ reachClosure (k + 1) A [0] → z ∈ reachClosure k A [0])
    ∨ (reachClosure k A [0]).length + 1 ≤ (reachClosure (k + 1) A [0]).length := by
  cases (inferInstance :
      Decidable (∀ z ∈ reachClosure (k + 1) A [0], z ∈ reachClosure k A [0])) with
  | isTrue hsub => exact Or.inl hsub
  | isFalse hsub =>
      rcases exists_mem_not (reachClosure k A [0]) (reachClosure (k + 1) A [0]) hsub
        with ⟨z, hz, hnz⟩
      have hnd : (reachClosure k A [0]).Nodup :=
        SpansMinEdgesProof.reachClosure_nodup k A [0] (by decide)
      have hcons_nd : (z :: reachClosure k A [0]).Nodup := List.nodup_cons.mpr ⟨hnz, hnd⟩
      have hcons_sub : ∀ w, w ∈ z :: reachClosure k A [0] → w ∈ reachClosure (k + 1) A [0] := by
        intro w hw
        rcases List.mem_cons.mp hw with he | ht
        · rw [he]; exact hz
        · exact reach_incr ht
      have hle := CayleyPruferInjection.nodup_subset_length_le
        (z :: reachClosure k A [0]) (reachClosure (k + 1) A [0]) hcons_nd hcons_sub
      rw [List.length_cons] at hle
      exact Or.inr hle

/-- Either the closure has grown to size `≥ 1 + m`, or it has stabilised at some
`k < m` (constructive: decidable step, explicit witness). -/
theorem chain_grow {N : Nat} {A : List Edge} (hIR : InRange N A) (hN : 0 < N) :
    ∀ m, (1 + m ≤ (reachClosure m A [0]).length)
       ∨ (∃ k, k < m ∧ ∀ z, z ∈ reachClosure (k + 1) A [0] → z ∈ reachClosure k A [0]) := by
  intro m
  induction m with
  | zero =>
      refine Or.inl ?_
      exact Nat.le_of_eq (rfl : 1 + 0 = (reachClosure 0 A [0]).length)
  | succ m ih =>
      rcases ih with hlen | hstab
      · rcases chain_key hIR hN m with hsub | hlt
        · exact Or.inr ⟨m, Nat.lt_succ_self m, hsub⟩
        · refine Or.inl ?_
          have hstep : 1 + m + 1 ≤ (reachClosure m A [0]).length + 1 :=
            Nat.add_le_add_right hlen 1
          have he : 1 + (m + 1) = 1 + m + 1 := by omega
          rw [he]
          exact Nat.le_trans hstep hlt
      · rcases hstab with ⟨k, hk, hs⟩
        exact Or.inr ⟨k, Nat.lt_succ_of_lt hk, hs⟩

/-- **Saturation.**  Under `InRange N A`, the fuel-`N` closure equals the
fuel-`(N+1)` closure (membership): the monotone chain in the `N`-element
universe has stabilised. -/
theorem reach_sat {N : Nat} {A : List Edge} (hIR : InRange N A) (hN : 0 < N) :
    MEqv (reachClosure N A [0]) (reachClosure (N + 1) A [0]) := by
  rcases chain_grow hIR hN (N + 1) with hlen | hstab
  · exfalso
    have hb := reach_len_le hIR hN (N + 1)
    omega
  · rcases hstab with ⟨k, hklt, hs⟩
    have hkN : k ≤ N := Nat.le_of_lt_succ hklt
    have hEqk : MEqv (reachClosure k A [0]) (reachClosure (k + 1) A [0]) := by
      intro z
      constructor
      · intro hz; exact reach_incr hz
      · intro hz; exact hs z hz
    have prop : ∀ t, MEqv (reachClosure k A [0]) (reachClosure (k + t) A [0]) := by
      intro t
      induction t with
      | zero => intro z; exact Iff.rfl
      | succ t ih =>
          have hcong : MEqv (reachClosure (k + 1) A [0]) (reachClosure (k + t + 1) A [0]) := by
            have hrc := relax_cong (A := A) ih
            intro z
            have e1 : reachClosure (k + 1) A [0] = relax A (reachClosure k A [0]) :=
              reachClosure_succ A k [0]
            have e2 : reachClosure (k + t + 1) A [0] = relax A (reachClosure (k + t) A [0]) :=
              reachClosure_succ A (k + t) [0]
            rw [e1, e2]; exact hrc z
          intro z
          exact Iff.trans (hEqk z) (hcong z)
    have hN_eq : MEqv (reachClosure k A [0]) (reachClosure N A [0]) := by
      have hp := prop (N - k)
      have hk : k + (N - k) = N := by omega
      rw [hk] at hp; exact hp
    have hN1_eq : MEqv (reachClosure k A [0]) (reachClosure (N + 1) A [0]) := by
      have hp := prop (N + 1 - k)
      have hk : k + (N + 1 - k) = N + 1 := by omega
      rw [hk] at hp; exact hp
    intro z
    exact Iff.trans (hN_eq z).symm (hN1_eq z)

/-- **The saturated closure is edge-closed** (contains everything reachable). -/
theorem reach_edgeClosed {N : Nat} {A : List Edge} (hIR : InRange N A) (hN : 0 < N) :
    EdgeClosed A (fun x => x ∈ reachClosure N A [0]) := by
  intro x y hx hxy
  have hy1 : y ∈ reachClosure (N + 1) A [0] := reach_step_edge hx hxy
  exact (reach_sat hIR hN y).mpr hy1

/-! ## 6. The merge-map arithmetic (injective off the collapsed pair `{a,b}`) -/

theorem relabelV_zero (a b : Nat) (hb : 0 < b) : relabelV a b 0 = 0 := by
  unfold relabelV
  rw [if_neg (by omega : ¬ (0 = b)), if_neg (by omega : ¬ (b < 0))]

theorem relabelV_a (a b : Nat) (hab : a < b) : relabelV a b a = a := by
  unfold relabelV
  rw [if_neg (by omega : ¬ (a = b)), if_neg (by omega : ¬ (b < a))]

theorem relabelV_b (a b : Nat) : relabelV a b b = a := by
  unfold relabelV; rw [if_pos rfl]

/-- **`relabelV a b` is injective off the collapsed pair `{a,b}`.**  If two labels
merge to the same image, they are equal or they are exactly `a` and `b`. -/
theorem relabelV_inj_or (a b : Nat) (hab : a < b) (x x' : Nat)
    (h : relabelV a b x = relabelV a b x') :
    x = x' ∨ (x = a ∧ x' = b) ∨ (x = b ∧ x' = a) := by
  have hx : relabelV a b x = (if x = b then a else if b < x then x - 1 else x) := rfl
  have hx' : relabelV a b x' = (if x' = b then a else if b < x' then x' - 1 else x') := rfl
  rw [hx, hx'] at h
  by_cases c1 : x = b
  · by_cases c3 : x' = b
    · exact Or.inl (by omega)
    · by_cases c4 : b < x'
      · rw [if_pos c1, if_neg c3, if_pos c4] at h; exact absurd h (by omega)
      · rw [if_pos c1, if_neg c3, if_neg c4] at h
        exact Or.inr (Or.inr ⟨c1, by omega⟩)
  · by_cases c2 : b < x
    · by_cases c3 : x' = b
      · rw [if_neg c1, if_pos c2, if_pos c3] at h; exact absurd h (by omega)
      · by_cases c4 : b < x'
        · rw [if_neg c1, if_pos c2, if_neg c3, if_pos c4] at h; exact Or.inl (by omega)
        · rw [if_neg c1, if_pos c2, if_neg c3, if_neg c4] at h; exact absurd h (by omega)
    · by_cases c3 : x' = b
      · rw [if_neg c1, if_neg c2, if_pos c3] at h
        exact Or.inr (Or.inl ⟨by omega, c3⟩)
      · by_cases c4 : b < x'
        · rw [if_neg c1, if_neg c2, if_neg c3, if_pos c4] at h; exact absurd h (by omega)
        · rw [if_neg c1, if_neg c2, if_neg c3, if_neg c4] at h; exact Or.inl h

/-! ## 7. The guarded BFS walk-transport (PROVED) -/

/-- **`reachTransport_inRange` — the guarded `ReachTransport` (PROVED).**  For an
oriented head `a < b < n` and an in-range tail `A`, a vertex `i < n` is reached
from `0` in `G = (n, (a,b)::A)` iff its merge image `relabelV a b i` is reached
in the contraction `G/e = (n-1, contractEdges a b A)`.

Both directions are edge-closure inductions (`reach_ind`).  Forward: the
predicate `x ↦ relabelV a b x ∈ reach(G/e)` is `G`-edge-closed — the head edge
`(a,b)` maps to the invisible self-loop `relabelV a b a = relabelV a b b = a`,
and each `A`-edge maps to a `G/e`-edge along which `reach(G/e)` is closed
(`reach_edgeClosed` for `G/e`).  Backward: the preimage predicate
`j ↦ ∀ x<n, relabelV a b x = j → x ∈ reach(G)` is `G/e`-edge-closed — using
`reach_edgeClosed` for `G` and `relabelV_inj_or` (two labels sharing an image are
either equal or the pair `{a,b}`, which the head edge re-identifies in `G`). -/
theorem reachTransport_inRange :
    ∀ (n a b : Nat) (A : List Edge), a < b → b < n → InRange n A →
      ∀ i, i < n →
        (i ∈ reachClosure n ((a, b) :: A) [0] ↔
         relabelV a b i ∈ reachClosure (n - 1) (contractEdges a b A) [0]) := by
  intro n a b A hab hbn hIR i hin
  have hbpos : 0 < b := by omega
  have hGpos : 0 < n := by omega
  have hGepos : 0 < n - 1 := by omega
  -- in-range for the two graphs
  have hIRG : InRange n ((a, b) :: A) := by
    intro e he
    rcases List.mem_cons.mp he with h0 | h0
    · rw [h0]; exact ⟨by omega, hbn⟩
    · exact hIR e h0
  have hIRGe : InRange (n - 1) (contractEdges a b A) := by
    intro e he
    have he' : e ∈ List.map (fun p : Edge => (relabelV a b p.1, relabelV a b p.2)) A := he
    rcases List.mem_map.mp he' with ⟨p, hpA, hpe⟩
    rw [← hpe]
    have hp := hIR p hpA
    exact ⟨SpansContractProof.relabelV_lt a b p.1 n hab hbn hp.1,
           SpansContractProof.relabelV_lt a b p.2 n hab hbn hp.2⟩
  have hSclosed := reach_edgeClosed hIRG hGpos
  have hTclosed := reach_edgeClosed hIRGe hGepos
  -- FORWARD
  have hEdgeClG : EdgeClosed ((a, b) :: A)
      (fun x => relabelV a b x ∈ reachClosure (n - 1) (contractEdges a b A) [0]) := by
    intro x y hx hxy
    rcases hxy with hxy | hxy
    · rcases List.mem_cons.mp hxy with hhd | htl
      · have hxa : x = a := congrArg Prod.fst hhd
        have hyb : y = b := congrArg Prod.snd hhd
        rw [hyb, relabelV_b]
        rw [hxa, relabelV_a a b hab] at hx
        exact hx
      · have hedge : (relabelV a b x, relabelV a b y) ∈ contractEdges a b A := by
          show (relabelV a b x, relabelV a b y)
             ∈ List.map (fun p : Edge => (relabelV a b p.1, relabelV a b p.2)) A
          exact List.mem_map.mpr ⟨(x, y), htl, rfl⟩
        exact hTclosed (relabelV a b x) (relabelV a b y) hx (Or.inl hedge)
    · rcases List.mem_cons.mp hxy with hhd | htl
      · have hya : y = a := congrArg Prod.fst hhd
        have hxb : x = b := congrArg Prod.snd hhd
        rw [hya, relabelV_a a b hab]
        rw [hxb, relabelV_b] at hx
        exact hx
      · have hedge : (relabelV a b y, relabelV a b x) ∈ contractEdges a b A := by
          show (relabelV a b y, relabelV a b x)
             ∈ List.map (fun p : Edge => (relabelV a b p.1, relabelV a b p.2)) A
          exact List.mem_map.mpr ⟨(y, x), htl, rfl⟩
        exact hTclosed (relabelV a b x) (relabelV a b y) hx (Or.inr hedge)
  have hP0 : relabelV a b 0 ∈ reachClosure (n - 1) (contractEdges a b A) [0] := by
    rw [relabelV_zero a b hbpos]
    exact reach_zero (n - 1) (contractEdges a b A)
  have hforward : i ∈ reachClosure n ((a, b) :: A) [0] →
      relabelV a b i ∈ reachClosure (n - 1) (contractEdges a b A) [0] :=
    fun hi => reach_ind hEdgeClG hP0 n i hi
  -- the "merge" transfer used repeatedly in the backward direction
  have mergeMem : ∀ (x' w : Nat), x' < n → w < n →
      relabelV a b x' = relabelV a b w →
      w ∈ reachClosure n ((a, b) :: A) [0] → x' ∈ reachClosure n ((a, b) :: A) [0] := by
    intro x' w _ _ heq hwS
    rcases relabelV_inj_or a b hab x' w heq with hxw | hcase
    · rw [hxw]; exact hwS
    · rcases hcase with ⟨hxa, hwb⟩ | ⟨hxb, hwa⟩
      · rw [hxa]
        rw [hwb] at hwS
        exact hSclosed b a hwS (Or.inr List.mem_cons_self)
      · rw [hxb]
        rw [hwa] at hwS
        exact hSclosed a b hwS (Or.inl List.mem_cons_self)
  -- BACKWARD
  have hEdgeClGe : EdgeClosed (contractEdges a b A)
      (fun j => ∀ x, x < n → relabelV a b x = j → x ∈ reachClosure n ((a, b) :: A) [0]) := by
    intro j j' hj hjj'
    intro x' hx'n hx'eq
    rcases hjj' with he | he
    · have he' : (j, j') ∈ List.map (fun p : Edge => (relabelV a b p.1, relabelV a b p.2)) A := he
      rcases List.mem_map.mp he' with ⟨p, hpA, hpe⟩
      have hj_eq : relabelV a b p.1 = j := congrArg Prod.fst hpe
      have hj'_eq : relabelV a b p.2 = j' := congrArg Prod.snd hpe
      have hp := hIR p hpA
      have hu : p.1 ∈ reachClosure n ((a, b) :: A) [0] := hj p.1 hp.1 hj_eq
      have hv : p.2 ∈ reachClosure n ((a, b) :: A) [0] :=
        hSclosed p.1 p.2 hu (Or.inl (List.mem_cons_of_mem _ hpA))
      have hxx : relabelV a b x' = relabelV a b p.2 := by rw [hx'eq, ← hj'_eq]
      exact mergeMem x' p.2 hx'n hp.2 hxx hv
    · have he' : (j', j) ∈ List.map (fun p : Edge => (relabelV a b p.1, relabelV a b p.2)) A := he
      rcases List.mem_map.mp he' with ⟨p, hpA, hpe⟩
      have hj'_eq : relabelV a b p.1 = j' := congrArg Prod.fst hpe
      have hj_eq : relabelV a b p.2 = j := congrArg Prod.snd hpe
      have hp := hIR p hpA
      have hv : p.2 ∈ reachClosure n ((a, b) :: A) [0] := hj p.2 hp.2 hj_eq
      have hu : p.1 ∈ reachClosure n ((a, b) :: A) [0] :=
        hSclosed p.2 p.1 hv (Or.inr (List.mem_cons_of_mem _ hpA))
      have hxx : relabelV a b x' = relabelV a b p.1 := by rw [hx'eq, ← hj'_eq]
      exact mergeMem x' p.1 hx'n hp.1 hxx hu
  have hQ0 : ∀ x, x < n → relabelV a b x = 0 → x ∈ reachClosure n ((a, b) :: A) [0] := by
    intro x hxn hx0
    have h0 : relabelV a b x = relabelV a b 0 := by rw [hx0, relabelV_zero a b hbpos]
    exact mergeMem x 0 hxn hGpos h0 (reach_zero n ((a, b) :: A))
  have hbackward : relabelV a b i ∈ reachClosure (n - 1) (contractEdges a b A) [0] →
      i ∈ reachClosure n ((a, b) :: A) [0] := by
    intro hi
    have hQ := reach_ind hEdgeClGe hQ0 (n - 1) (relabelV a b i) hi
    exact hQ i hin rfl
  exact ⟨hforward, hbackward⟩

/-! ## 8. The guarded spans-level identity (PROVED) -/

/-- **`spansContractLt_inRange` — the guarded `SpansContractLt` (PROVED).**  For
`a < b < n` and `InRange n A`,
`spans n ((a,b)::A) = spans (n-1)(contractEdges a b A)`, from
`reachTransport_inRange` via the merge surjection `relabelV a b`. -/
theorem spansContractLt_inRange :
    ∀ (n a b : Nat) (A : List Edge), a < b → b < n → InRange n A →
      spans n ((a, b) :: A) = spans (n - 1) (contractEdges a b A) := by
  intro n a b A hab hbn hIR
  show decide (∀ i, i < n → i ∈ reachClosure n ((a, b) :: A) [0])
     = decide (∀ j, j < n - 1 → j ∈ reachClosure (n - 1) (contractEdges a b A) [0])
  apply decide_eq_decide.mpr
  constructor
  · intro hG j hj
    have hi : SpansContractProof.preimg b j < n := SpansContractProof.preimg_lt b j n hj
    have ht := (reachTransport_inRange n a b A hab hbn hIR (SpansContractProof.preimg b j) hi).mp
      (hG _ hi)
    rwa [SpansContractProof.relabelV_preimg a b j hab] at ht
  · intro hG' i hi
    have hlt : relabelV a b i < n - 1 := SpansContractProof.relabelV_lt a b i n hab hbn hi
    exact (reachTransport_inRange n a b A hab hbn hIR i hi).mpr (hG' _ hlt)

/-! ## 8b. `InRange` is inherited by sublists, and the guarded tree-count
non-loop deletion–contraction identity (the non-loop `treeCount` half of the
recursor, GENUINELY CLOSED in range). -/

/-- Any edge of a sublist of `rest` is an edge of `rest`. -/
theorem mem_of_mem_sublists {α : Type _} {x : α} :
    ∀ (l s : List α), s ∈ sublists l → x ∈ s → x ∈ l
  | [], s, hs, hx => by
      rw [List.mem_singleton.mp hs] at hx
      exact absurd hx List.not_mem_nil
  | a :: l', s, hs, hx => by
      have hs' : s ∈ sublists l' ++ (sublists l').map (fun t => a :: t) := hs
      rcases List.mem_append.mp hs' with h1 | h1
      · exact List.mem_cons_of_mem _ (mem_of_mem_sublists l' s h1 hx)
      · rcases List.mem_map.mp h1 with ⟨t, ht, hts⟩
        rw [← hts] at hx
        rcases List.mem_cons.mp hx with he | he
        · rw [he]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (mem_of_mem_sublists l' t ht he)

/-- `InRange n` is inherited by every sublist of `rest`. -/
theorem inRange_of_mem_sublists {n : Nat} {rest : List Edge} (hIR : InRange n rest) :
    ∀ s, s ∈ sublists rest → InRange n s :=
  fun s hs e he => hIR e (mem_of_mem_sublists rest s hs he)

/-- **`treeCountContract_inRange` — the weightless spanning-tree
deletion–contraction count identity, GENUINELY PROVED (no free hypothesis).**
For `a < b < n` and `InRange n rest`,

    treeCount n ((a,b)::rest)
      = treeCount n rest + treeCount (n-1) (contractEdges a b rest).

Same content as `TreeCountContractProof.treeCountContractGuarded`, but consuming
the now-PROVED `spansContractLt_inRange` (per sublist, via
`inRange_of_mem_sublists`) instead of the unsatisfiable unguarded
`SpansContractLt`.  So this non-loop half of the deletion–contraction recursor is
now closed outright over any in-range graph. -/
theorem treeCountContract_inRange {n a b : Nat} {rest : List Edge}
    (hIR : InRange n rest) (hab : a < b) (hbn : b < n) :
    treeCount n ((a, b) :: rest)
      = treeCount n rest + treeCount (n - 1) (contractEdges a b rest) := by
  have hL := TreeCountContractProof.treeCount_cons_split n (a, b) rest
  have hR := TreeCountContractProof.treeCount_contract_as_filter n a b rest
  have hfil :
      ((sublists rest).filter
        (fun s => spans n ((a, b) :: s) && decide (((a, b) :: s).length = n - 1)))
      = ((sublists rest).filter
        (fun s => spans (n - 1) (contractEdges a b s)
                  && decide ((contractEdges a b s).length = n - 1 - 1))) := by
    apply List.filter_congr
    intro s hs
    have hIRs : InRange n s := inRange_of_mem_sublists hIR s hs
    have hspan : spans n ((a, b) :: s) = spans (n - 1) (contractEdges a b s) :=
      spansContractLt_inRange n a b s hab hbn hIRs
    have e2 : (contractEdges a b s).length = s.length := by
      show (s.map (fun e : Edge => (relabelV a b e.1, relabelV a b e.2))).length = s.length
      rw [List.length_map]
    have hlen : decide (((a, b) :: s).length = n - 1)
              = decide ((contractEdges a b s).length = n - 1 - 1) := by
      show decide (s.length + 1 = n - 1) = decide ((contractEdges a b s).length = n - 1 - 1)
      rw [e2]; exact TreeCountContractProof.decLen n s.length (by omega)
    rw [hspan, hlen]
  rw [hL, hR, hfil]

/-! ## 9. Refutations of the UNGUARDED forms (adversarial correction) -/

/-- **`reachTransport_unguarded_false : ¬ ReachTransport`.**  The unguarded
statement (arbitrary `A`) is FALSE: at `n=3, (a,b)=(0,1), A=[(0,3),(3,4),(2,4)]`
(all guards `a<b`, `b<n` hold, but `A` has out-of-range labels `3,4`), vertex
`i=2` is reached in `G` at fuel `3` while `relabelV 0 1 2 = 1` is NOT reached in
`G/e` at fuel `2` (the merge shortcut needs more fuel than `n-1`).  The missing
guard is `InRange n A` (see `reachTransport_inRange`). -/
theorem reachTransport_unguarded_false : ¬ SpansContractProof.ReachTransport := by
  intro h
  have hbad := h 3 0 1 [(0, 3), (3, 4), (2, 4)] (by decide) (by decide) 2 (by decide)
  revert hbad
  decide

/-- **`spansContractLt_unguarded_false : ¬ SpansContractLt`.**  Same
counterexample at the `spans` level: `spans 3 ((0,1)::A) = true` but
`spans 2 (contractEdges 0 1 A) = false`.  The genuine content is the guarded
`spansContractLt_inRange`. -/
theorem spansContractLt_unguarded_false : ¬ TreeCountContractProof.SpansContractLt := by
  intro h
  have hbad := h 3 0 1 [(0, 3), (3, 4), (2, 4)] (by decide) (by decide)
  revert hbad
  decide

end YMGap.Continuum.SpansContractInRange

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SpansContractInRange.reach_ind
#print axioms YMGap.Continuum.SpansContractInRange.reach_edgeClosed
#print axioms YMGap.Continuum.SpansContractInRange.reach_sat
#print axioms YMGap.Continuum.SpansContractInRange.relabelV_inj_or
#print axioms YMGap.Continuum.SpansContractInRange.reachTransport_inRange
#print axioms YMGap.Continuum.SpansContractInRange.spansContractLt_inRange
#print axioms YMGap.Continuum.SpansContractInRange.treeCountContract_inRange
#print axioms YMGap.Continuum.SpansContractInRange.reachTransport_unguarded_false
#print axioms YMGap.Continuum.SpansContractInRange.spansContractLt_unguarded_false
