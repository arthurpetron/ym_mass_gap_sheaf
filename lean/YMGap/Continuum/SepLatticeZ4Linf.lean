/-
A SECOND, strictly-finer genuine inhabitant of the named `(D2)` structural
residual `Ursell4DProgress.SepLatticeZ4`: the **L∞ per-coordinate** plaquette
separation metric on the CLOSED degree-24 Z⁴ plaquette lattice `z4Chain`.

# Why a second inhabitant

`SepLatticeZ4Close.z4Sep` already closes `(D2)` with the L¹ coordinate-SUM
projection `z4dist p q = |Σᵢvᵢ(p) − Σᵢvᵢ(q)|`.  That metric is honest and
sound but **non-tight**: it COLLAPSES along constant-sum directions (e.g. a
`+e_x`, `−e_y` displacement gives `z4dist = 0`).  Its own docstring names the
strictly-stronger drop-in — the per-coordinate L∞ metric
`maxᵢ |vᵢ(p) − vᵢ(q)|`.  This module BUILDS that metric.

Constructing a second, structurally-independent inhabitant does two honest jobs:

  1. **Adversarial satisfiability cross-check.**  `(D2)` is NOT an over-constrained
     or false carrier (unlike the refuted `SixJPentagon`): it is inhabited by two
     genuinely different real metrics.  A false carrier would not admit an
     independent second construction of a strictly finer separating metric.
  2. **A strictly-finer real metric.**  `linf_strictly_refines_l1` exhibits a
     concrete pair on which the L¹ metric collapses to `0` while the L∞ metric is
     strictly positive — so `z4SepLinf` is the genuine directional geometry, not a
     placeholder.

# What is delivered (all PROVED, axiom-clean)

  * `vComp` / `cPlaq` — the per-direction coordinate of a vertex / a plaquette's
    base vertex; `natDist` — the Mathlib-free `Nat` distance `(a−b)+(b−a)`.
  * `linfDist p q = maxᵢ natDist(cᵢ p, cᵢ q)` — the L∞ per-coordinate metric.
  * `vComp_addE_cases` / `edge_base_comp` — the load-bearing structural fact,
    PER COORDINATE: every boundary edge base sits in the width-1 window
    `[vᵢ(p.1), vᵢ(p.1)+1]` in each of the 4 coordinates simultaneously.
  * `linfDist_le` / `le_linfDist_comp` / `natDist_triangle` — the max-glue lemmas.
  * `z4SepLinf : SepLattice` over `z4Lattice` with `dist := linfDist`, all three
    `SepLattice` axioms discharged (`dist_adj_le ≤ 1` from the per-coordinate
    width-1 windows; `dist_triangle` glued component-wise since core `omega`
    atomizes `max` under addition).
  * `SepLatticeZ4_linf_witness : SepLatticeZ4` — the second closure of `(D2)`.
  * `linf_strictly_refines_l1` — the non-vacuity / strict-refinement certificate.

# Honest scope (what this does and does NOT advance)

`(D2)` is a structural PREREQUISITE that only TYPES the genuinely-open `(T′)`
`TreeGraphBound.tree_graph` (phrased over `d2Sep.val`).  Inhabiting `(D2)` — with
either the L¹ or this L∞ metric — supplies the plaquette-graph separation the
size-floor bound `PinnedCluster.connected_spanning_size_ge` consumes; it does NOT
prove `(T′)`, `(D1)`, the pentagon `(A2)`, Sub-wall B, or the Minlos lift, and does
NOT inhabit `SubWallA` / `Tier0Scorecard`.  The frontier stays open; the guard
`YMGapFrontierGuard` still reports all 5 Clay-frontier types uninhabited.

# Constructive contract (`lean/AGENTS.md`)

Mathlib-free; only `Nat` / `List` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `sorry` / `admit` / new `axiom`.  All witnesses are
`Type`-level data.  Permitted axioms only `propext` / `Quot.sound`.
-/

import YMGap.Continuum.SepLatticeZ4Close

namespace YMGap.Continuum.SepLatticeZ4Linf

open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Ursell4DProgress
open Dir4

/-! ## 1. Per-coordinate potentials and the `Nat` distance -/

/-- The coordinate of a `Z4Vertex` in direction `m` (destructured so the
equation lemmas expose the coordinate directly, with no residual `Prod.fst`). -/
def vComp : Z4Vertex → Dir4 → Nat
  | (a, _, _, _), x0 => a
  | (_, b, _, _), x1 => b
  | (_, _, c, _), x2 => c
  | (_, _, _, d), x3 => d

/-- The `m`-coordinate of a plaquette's base vertex. -/
def cPlaq (p : Z4Plaq) (m : Dir4) : Nat := vComp p.1 m

/-- The Mathlib-free `Nat` distance, written so `omega` sees it transparently. -/
def natDist (a b : Nat) : Nat := (a - b) + (b - a)

/-- **The L∞ per-coordinate metric.**  `maxᵢ natDist(cᵢ p, cᵢ q)` over the 4 axis
directions — the non-collapsing directional separation. -/
def linfDist (p q : Z4Plaq) : Nat :=
  Nat.max (Nat.max (natDist (cPlaq p x0) (cPlaq q x0))
                   (natDist (cPlaq p x1) (cPlaq q x1)))
          (Nat.max (natDist (cPlaq p x2) (cPlaq q x2))
                   (natDist (cPlaq p x3) (cPlaq q x3)))

/-! ## 2. The per-coordinate width-1 window (load-bearing structural fact) -/

/-- A single `addE` step changes each coordinate by `0` or `+1` (exactly `+1` on
the incremented direction, `0` on the others) — never a decrement. -/
theorem vComp_addE_cases (v : Z4Vertex) (d m : Dir4) :
    vComp (addE v d) m = vComp v m ∨ vComp (addE v d) m = vComp v m + 1 := by
  obtain ⟨a, b, c, e⟩ := v
  cases d <;> cases m <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- **`edge_base_comp` (PROVED — the load-bearing per-coordinate fact).**  For each
of the 4 axis directions `m`, the `m`-coordinate of a boundary edge's base of `p`
sits in the width-1 window `[cPlaq p m, cPlaq p m + 1]`. -/
theorem edge_base_comp {p : Z4Plaq} {ℓ : Z4Link} (h : ℓ ∈ edgesOf p) (m : Dir4) :
    vComp ℓ.1 m = cPlaq p m ∨ vComp ℓ.1 m = cPlaq p m + 1 := by
  simp only [edgesOf, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact vComp_addE_cases _ _ _
  · exact vComp_addE_cases _ _ _

/-! ## 3. Max-glue lemmas (core `omega` atomizes `max` under addition) -/

/-- Per-coordinate `Nat`-distance triangle inequality (no `max`). -/
theorem natDist_triangle (a b c : Nat) : natDist a c ≤ natDist a b + natDist b c := by
  simp only [natDist]; omega

/-- `natDist a a = 0`. -/
theorem natDist_self (a : Nat) : natDist a a = 0 := by
  simp only [natDist]; omega

/-- If every coordinate distance is `≤ B`, then the L∞ distance is `≤ B`.  Glued
with `Nat.max_le` (core `omega` atomizes a NESTED `max`, so we chain explicitly). -/
theorem linfDist_le (p q : Z4Plaq) (B : Nat)
    (h0 : natDist (cPlaq p x0) (cPlaq q x0) ≤ B)
    (h1 : natDist (cPlaq p x1) (cPlaq q x1) ≤ B)
    (h2 : natDist (cPlaq p x2) (cPlaq q x2) ≤ B)
    (h3 : natDist (cPlaq p x3) (cPlaq q x3) ≤ B) :
    linfDist p q ≤ B := by
  unfold linfDist
  exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨h0, h1⟩, Nat.max_le.mpr ⟨h2, h3⟩⟩

/-- Each coordinate distance is dominated by the L∞ distance (chained
`Nat.le_max_left` / `Nat.le_max_right`, again to dodge the nested-`max` `omega`
limitation). -/
theorem le_linfDist_comp (p q : Z4Plaq) (m : Dir4) :
    natDist (cPlaq p m) (cPlaq q m) ≤ linfDist p q := by
  unfold linfDist
  cases m
  · exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  · exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  · exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  · exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

/-! ## 4. The genuine L∞ `SepLattice` over `z4Lattice` -/

/-- **`z4SepLinf` (PROVED).**  The L∞ per-coordinate separation metric as a genuine
`SepLattice` over the CLOSED degree-24 Z⁴ plaquette lattice.  All three axioms
discharged; `dist_adj_le ≤ 1` because a shared boundary edge places its base in the
width-1 window of BOTH plaquettes in EVERY coordinate simultaneously
(`edge_base_comp`), so every coordinate distance is `≤ 1`, hence so is their max. -/
def z4SepLinf : SepLattice where
  toLattice := z4Lattice
  dist := linfDist
  dist_self := by
    intro p
    unfold linfDist
    simp only [natDist_self, Nat.max_self]
  dist_adj_le := by
    intro p q adj
    have hp : adj.link ∈ edgesOf p := of_decide_eq_true adj.on_p
    have hq : adj.link ∈ edgesOf q := of_decide_eq_true adj.on_q
    -- per-coordinate width-1 windows on both p and q
    have b0 : natDist (cPlaq p x0) (cPlaq q x0) ≤ 1 := by
      have := edge_base_comp hp x0; have := edge_base_comp hq x0
      simp only [natDist]; omega
    have b1 : natDist (cPlaq p x1) (cPlaq q x1) ≤ 1 := by
      have := edge_base_comp hp x1; have := edge_base_comp hq x1
      simp only [natDist]; omega
    have b2 : natDist (cPlaq p x2) (cPlaq q x2) ≤ 1 := by
      have := edge_base_comp hp x2; have := edge_base_comp hq x2
      simp only [natDist]; omega
    have b3 : natDist (cPlaq p x3) (cPlaq q x3) ≤ 1 := by
      have := edge_base_comp hp x3; have := edge_base_comp hq x3
      simp only [natDist]; omega
    exact linfDist_le p q 1 b0 b1 b2 b3
  dist_triangle := by
    intro p q r
    apply linfDist_le
    · have t := natDist_triangle (cPlaq p x0) (cPlaq q x0) (cPlaq r x0)
      have h1 := le_linfDist_comp p q x0
      have h2 := le_linfDist_comp q r x0
      omega
    · have t := natDist_triangle (cPlaq p x1) (cPlaq q x1) (cPlaq r x1)
      have h1 := le_linfDist_comp p q x1
      have h2 := le_linfDist_comp q r x1
      omega
    · have t := natDist_triangle (cPlaq p x2) (cPlaq q x2) (cPlaq r x2)
      have h1 := le_linfDist_comp p q x2
      have h2 := le_linfDist_comp q r x2
      omega
    · have t := natDist_triangle (cPlaq p x3) (cPlaq q x3) (cPlaq r x3)
      have h1 := le_linfDist_comp p q x3
      have h2 := le_linfDist_comp q r x3
      omega

/-! ## 5. Inhabiting the named residual subtype (second closure) -/

/-- **`SepLatticeZ4_linf_witness` (PROVED — a SECOND closure of `(D2)`).**  The
subtype proof is `rfl` because `z4SepLinf.toLattice` and `z4Chain.toLattice` are
both definitionally `z4Lattice`. -/
def SepLatticeZ4_linf_witness : SepLatticeZ4 := ⟨z4SepLinf, rfl⟩

/-! ## 6. Non-vacuity: the L∞ metric strictly refines the L¹ metric -/

/-- **`linf_strictly_refines_l1` (PROVED — non-vacuity / strict refinement).**  A
concrete `+e_x`, `−e_y` (constant coordinate-sum) displacement on which the L¹
projection `SepLatticeZ4Close.z4dist` COLLAPSES to `0`, while the L∞ metric
`linfDist` is strictly positive.  So `z4SepLinf` is the genuine directional
metric, strictly finer than the sum projection — not a collapsed placeholder. -/
theorem linf_strictly_refines_l1 :
    SepLatticeZ4Close.z4dist ((1, 1, 0, 0), Z4Plane.p01) ((2, 0, 0, 0), Z4Plane.p01) = 0
      ∧ 0 < linfDist ((1, 1, 0, 0), Z4Plane.p01) ((2, 0, 0, 0), Z4Plane.p01) :=
  ⟨by decide, by decide⟩

end YMGap.Continuum.SepLatticeZ4Linf
