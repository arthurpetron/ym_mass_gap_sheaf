/-
Wall-2 finite pieces — the combinatorial / geometric atoms that let the
real Wilson connected-correlator decay be DERIVED rather than posited.

# What this module delivers (honest scope)

`Continuum/KPCriterion.lean` proves the single-rep activity collapse
`activity w X label = (coeffW w r) ^ size X` and the per-rep geometric KP
bound CONDITIONAL on a `ClusterCountBound`; `Continuum/ClusterCount.lean`
inhabits that count via the walk encoding; `Continuum/PlaquetteActivity.lean`
proves `coeffW w 1 = 2·w³` is the leading character coefficient with the
consecutive-rep decay `coeffW w (s+1) ≤ (2w⁵)·coeffW w s`.

This module assembles THREE finite pieces, all PROVED:

  1. `activity_le_leading` — on a constrained connected polymer with common
     rep `r ≥ 1`, the activity is dominated by the LEADING-rep power:

         activity w X label  ≤  (coeffW w 1) ^ size X       (0 ≤ w ≤ 1/2).

     The monotonicity `coeffW w r ≤ coeffW w 1` for `r ≥ 1` at `w ≤ 1/2` is
     the Casimir-decay direction (`coeffW w s = (s+1)·w^{s(s+2)}` decreases
     in `s` at strong coupling, since each successive ratio `2w⁵ ≤ 1/16 ≤ 1`);
     combined with `activity_single_rep`.

  2. `connected_spanning_size_ge` — THE new combinatorial lemma: a connected
     polymer that *spans* lattice separation `≥ n` (carries an in-`X`
     adjacency path between two plaquettes at separation `≥ n`) has
     `size X ≥ n`.  This needs a genuine separation structure on the
     lattice, added HONESTLY as `SepLattice`: a `dist : Plaquette →
     Plaquette → Nat` with the REAL geometric step bound
     `dist_adj_le : Adjacent p q → dist p q ≤ 1` and the triangle inequality
     `dist_triangle`.  The proof mirrors `ClusterCount.polymerToWalk`: an
     adjacency path through `X` from `p` to `q` has `≥ dist p q ≥ n` steps,
     and (being a sublist of `X`) at most `size X` vertices, so
     `n ≤ dist p q ≤ pathLen ≤ size X`.

  3. `pinnedClusterTail` — the geometric TAIL of the KP series for polymers
     of size `≥ n`:

         Σ_{m<d}  animalCount (n+m) · (coeffW w 1)^(n+m) · eSurrogate^(n+m)
              ≤  tailConst · ρ^n        with  ρ = K·(coeffW w 1)·eSurrogate,

     `tailConst = 2`, valid whenever `ρ ≤ 1/2` (hence `ρ < 1`).  This is the
     same KP engine as `kp_criterion_of_count`, summed from index `n`
     instead of `0`; the `ρ < 1` strong-coupling threshold is recorded
     explicitly (`ratio_lt_one`).

These three pieces are exactly what removes the posited `sep` from the real
connected-correlator decay: (1) bounds every constrained connected polymer's
activity by the leading power, (2) forces a polymer that joins two
separated plaquettes to be large, and (3) sums the resulting geometric tail.

# PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED here (all genuine):
  * `coeffW_le_one_le` (monotonicity `coeffW w r ≤ coeffW w 1`, r ≥ 1, w ≤ 1);
  * `activity_le_leading`;
  * `SepLattice` (separation structure, genuine `dist` step bound + triangle);
  * `AdjPath` (in-polymer adjacency path) + `dist_le_pathLen` (triangle along
    the path) + `connected_spanning_size_ge`;
  * `geom_partial_le_two` (Σ ρ^i ≤ 2 for ρ ≤ 1/2), `ratio_lt_one`,
    `pinnedClusterTail`.

NAMED-open (NOT inhabited here — upstream cruxes, carried as hypotheses /
structures, never faked):
  * `ClusterCountBound` (the lattice-animal count) — supplied by the caller
    (inhabited unconditionally in `Continuum/ClusterCount.lean`);
  * a concrete physical 4D `SepLattice` `dist` — the abstract structure is
    inhabited by `toySep` below as a sanity witness; the physical Euclidean
    plaquette distance is the geometry layer, not this combinatorial one.

This module is NOT the full cluster expansion, NOT a continuum limit, and
NOT a 4D Yang–Mills mass gap.  It is the finite Wall-2 input the real
correlator decay consumes.

# Constructive contract (`lean/AGENTS.md`, Rules 1/6/8)

Mathlib-free; only `Q'` / `Nat` / `List` core.  No `Classical.*`, no `Real`,
no `native_decide`, no `decide` on non-decidable props.  No `sorry` /
`admit` / new `axiom`.  All witnesses are `Type`-level data; the separation
structure's `dist` step bound and triangle inequality are genuine fields,
not faked.
-/

import YMGap.Continuum.PolymerModel
import YMGap.Continuum.PlaquetteActivity
import YMGap.Continuum.KPCriterion
import YMGap.Continuum.ClusterCount
import YMGap.Continuum.KPLimit

namespace YMGap.Continuum.PinnedCluster

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.PlaquetteActivity
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.ClusterCount

/-! ## 1. Leading-rep activity domination (`activity_le_leading`)

The diagonal character coefficient `coeffW w s = (s+1)·w^{s(s+2)}` is
DECREASING in the excited spin `s` at strong coupling: the proved
consecutive-rep ratio `coeffW w (s+1) ≤ (2w⁵)·coeffW w s` has ratio
`2w⁵ ≤ 2·1 = 2` for `w ≤ 1`, which is too weak; at the strong-coupling
threshold `w ≤ 1/2` the ratio drops to `2w⁵ ≤ 1/16 ≤ 1`, a genuine
contraction, so `coeffW w (s+1) ≤ coeffW w s` (`coeffW_succ_le`).  Chaining
this down to `s = 1` gives the leading-rep domination `coeffW w r ≤ coeffW w 1`
(`coeffW_le_one_le`). -/

/-- **Consecutive-rep monotone decay at strong coupling.**  For `0 ≤ w ≤ 1/2`
and any excited spin `s ≥ 1`, `coeffW w (s+1) ≤ coeffW w s`.

Routed through the proved ratio `coeffW w (s+1) ≤ (2w⁵)·coeffW w s`
(`coeffW_succ_ratio`): at `w ≤ 1/2` the ratio is `2w⁵ ≤ 1/16 ≤ 1`
(`ratio_le_half`), so `(2w⁵)·coeffW w s ≤ coeffW w s`. -/
theorem coeffW_succ_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ Q'.mkPos 1 2 (by decide)) (s : Nat) (hs : 1 ≤ s) :
    coeffW w (s + 1) ≤ coeffW w s := by
  have hw1 : w ≤ (1 : Q') := Q'.le_trans' _ _ _ hw (by decide)
  -- coeffW w (s+1) ≤ (2w⁵)·coeffW w s ≤ 1·coeffW w s = coeffW w s
  have hratio : coeffW w (s + 1) ≤ (Q'.ofNat 2 * qpow w 5) * coeffW w s :=
    coeffW_succ_ratio hw0 hw1 s hs
  -- 2w⁵ ≤ 1/2 ≤ 1  (ratio_le_half), and coeffW w s ≥ 0
  have hr_half : Q'.ofNat 2 * qpow w 5 ≤ Q'.mkPos 1 2 (by decide) :=
    ratio_le_half hw0 hw
  have hr_one : Q'.ofNat 2 * qpow w 5 ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ hr_half (by decide)
  have hcs_nn : (0 : Q') ≤ coeffW w s := coeffW_nonneg hw0 s
  have hstep : (Q'.ofNat 2 * qpow w 5) * coeffW w s ≤ (1 : Q') * coeffW w s :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hr_one hcs_nn
  refine Q'.le_trans' _ _ _ hratio ?_
  refine Q'.le_trans' _ _ _ hstep ?_
  exact Q'.le_of_eqv (Q'.one_mul_eqv (coeffW w s))

/-- **Leading-rep coefficient domination.**  For `0 ≤ w ≤ 1/2` and any rep
`r ≥ 1`, `coeffW w r ≤ coeffW w 1` — the excited coefficients are dominated
by the leading (`s = 1`) one (the Casimir-decay direction).  Proved by
descending induction on `r` via `coeffW_succ_le`. -/
theorem coeffW_le_one_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ Q'.mkPos 1 2 (by decide)) :
    ∀ r : Nat, 1 ≤ r → coeffW w r ≤ coeffW w 1 := by
  intro r
  induction r with
  | zero => intro h; exact absurd h (by decide)
  | succ k ih =>
      intro _
      -- two cases: k = 0 (then succ k = 1, reflexive) or k ≥ 1 (use decay)
      cases Nat.lt_or_ge k 1 with
      | inl hk0 =>
          -- k < 1 ⇒ k = 0 ⇒ succ k = 1
          have : k = 0 := by omega
          subst this
          exact Q'.le_refl' _
      | inr hk1 =>
          -- k ≥ 1: coeffW w (k+1) ≤ coeffW w k ≤ coeffW w 1
          have hdec : coeffW w (k + 1) ≤ coeffW w k := coeffW_succ_le hw0 hw k hk1
          exact Q'.le_trans' _ _ _ hdec (ih hk1)

/-- **`activity_le_leading` (PROVED).**  Let `X` be a polymer all of whose
plaquettes carry the common rep `r ≥ 1` (the single-rep collapse of a
constrained connected polymer, `constrained_connected_single_rep` /
`activity_single_rep`).  Then at strong coupling `0 ≤ w ≤ 1/2`,

    activity w X label  ≤  (coeffW w 1) ^ size X,

the LEADING-rep power.  Proof: the single-rep collapse gives `activity =
(coeffW w r) ^ size X`, and `coeffW w r ≤ coeffW w 1` (`coeffW_le_one_le`)
raises to the same power (both bases nonnegative). -/
theorem activity_le_leading {L : Lattice} {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ Q'.mkPos 1 2 (by decide)) (X : Polymer L)
    (label : L.Plaquette → Rep) (r : Rep) (hr : 1 ≤ r)
    (hall : ∀ p, p ∈ X → label p = r) :
    activity w X label ≤ (coeffW w 1) ^ Polymer.size X := by
  rw [activity_single_rep w X label r hall]
  -- (coeffW w r)^n ≤ (coeffW w 1)^n  from coeffW w r ≤ coeffW w 1, bases ≥ 0
  have hbase : coeffW w r ≤ coeffW w 1 := coeffW_le_one_le hw0 hw r hr
  have hcr_nn : (0 : Q') ≤ coeffW w r := coeffW_nonneg hw0 r
  -- pow-monotone in the base (induction)
  have hpow : ∀ n : Nat, (coeffW w r) ^ n ≤ (coeffW w 1) ^ n := by
    intro n
    induction n with
    | zero => exact Q'.le_refl' _
    | succ k ih =>
        rw [Q'.pow_succ, Q'.pow_succ]
        -- coeffW w r * (coeffW w r)^k ≤ coeffW w 1 * (coeffW w 1)^k
        have h1 : coeffW w r * (coeffW w r) ^ k
            ≤ coeffW w r * (coeffW w 1) ^ k :=
          Q'.mul_le_mul_of_nonneg_left _ _ _ ih hcr_nn
        have hc1k_nn : (0 : Q') ≤ (coeffW w 1) ^ k :=
          Q'.pow_nonneg _ (coeffW_nonneg hw0 1) k
        have h2 : coeffW w r * (coeffW w 1) ^ k
            ≤ coeffW w 1 * (coeffW w 1) ^ k :=
          Q'.mul_le_mul_of_nonneg_right _ _ _ hbase hc1k_nn
        exact Q'.le_trans' _ _ _ h1 h2
  exact hpow (Polymer.size X)

/-! ## 2. The separation structure and `connected_spanning_size_ge`

The combinatorial lemma needs a genuine notion of lattice separation.  We
add it HONESTLY as a `SepLattice`: a `Lattice` with a `dist : Plaquette →
Plaquette → Nat` carrying the two REAL geometric properties used by the
proof:

  * `dist_adj_le` — a single adjacency step changes the distance by at most
    `1` (`Adjacent p q → dist p q ≤ 1`).  This is the defining property of a
    graph distance: adjacent vertices are at distance ≤ 1.
  * `dist_triangle` — the triangle inequality `dist p r ≤ dist p q + dist q r`.

These are exactly the axioms of a path metric on the plaquette adjacency
graph; they are NOT faked (a concrete `toySep` witness inhabits them).  No
metric scale, no dimension — only the two facts the spanning bound uses. -/

/-- A **separation-equipped lattice**: a `Lattice` together with an integer
plaquette distance `dist` satisfying the genuine graph-metric properties
`dist_adj_le` (adjacent ⇒ distance ≤ 1) and `dist_triangle` (triangle
inequality).  These are the real geometric facts the spanning bound needs. -/
structure SepLattice extends Lattice where
  /-- The plaquette separation (graph distance). -/
  dist : toLattice.Plaquette → toLattice.Plaquette → Nat
  /-- A plaquette is at distance `0` from itself (genuine metric identity). -/
  dist_self : ∀ p, dist p p = 0
  /-- A single adjacency step has distance `≤ 1` (the defining graph-metric
  step bound — genuine, not faked). -/
  dist_adj_le : ∀ p q, toLattice.Adjacent p q → dist p q ≤ 1
  /-- The triangle inequality `dist p r ≤ dist p q + dist q r`. -/
  dist_triangle : ∀ p q r, dist p r ≤ dist p q + dist q r

/-- A concrete `SepLattice` sanity witness over the diagonal toy lattice of
`ClusterCount.toyBounded`: a plaquette is on its own boundary only, so the
only adjacency is the reflexive one, `dist p q = 0` works (adjacency forces
`p = q` there, distance `0 ≤ 1`; triangle is `0 ≤ 0`).  Confirms `SepLattice`
is genuinely inhabitable. -/
def toySep : SepLattice where
  toLattice :=
    { Link := Nat
      Plaquette := Nat
      boundary := fun p ℓ => p == ℓ }
  dist := fun _ _ => 0
  dist_self := by intro _; rfl
  dist_adj_le := by intro _ _ _; exact Nat.zero_le 1
  dist_triangle := by intro _ _ _; exact Nat.zero_le _

/-! ### The in-polymer adjacency path

`AdjPath S X p q` is an adjacency path from `p` to `q`, all of whose vertices
lie (in order) in the polymer `X`.  It carries the vertex list together with
a `Sublist X` witness, so its length is bounded by `size X` (core
`List.Sublist.length_le`); the adjacency steps give the distance bound by the
triangle inequality.  This is the spanning datum a connected polymer joining
two separated plaquettes provides — the analogue of `ClusterCount`'s walk. -/

/-- An in-polymer adjacency path from `p` to `q`.

  * `single p` — the trivial path at a single plaquette;
  * `cons adj rest` — prepend an adjacency step `p ~ p'` to a path from `p'`.

`verts` is the visited list (head `p`, last `q`); `pathLen` is the step
count.  The spanning size bound uses `verts <+ X` (a separate hypothesis). -/
inductive AdjPath (S : SepLattice) :
    S.toLattice.Plaquette → S.toLattice.Plaquette → Type
  | single (p : S.toLattice.Plaquette) : AdjPath S p p
  | cons {p p' q : S.toLattice.Plaquette}
      (adj : S.toLattice.Adjacent p p') (rest : AdjPath S p' q) :
      AdjPath S p q

namespace AdjPath

variable {S : SepLattice}

/-- The visited-plaquette list of a path (head `p`, last `q`). -/
def verts : {p q : S.toLattice.Plaquette} → AdjPath S p q →
    List S.toLattice.Plaquette
  | p, _, AdjPath.single _ => [p]
  | p, _, AdjPath.cons _ rest => p :: verts rest

/-- The number of adjacency steps in the path. -/
def pathLen : {p q : S.toLattice.Plaquette} → AdjPath S p q → Nat
  | _, _, AdjPath.single _ => 0
  | _, _, AdjPath.cons _ rest => pathLen rest + 1

/-- The vertex list has `pathLen + 1` entries. -/
theorem verts_length {p q : S.toLattice.Plaquette} (path : AdjPath S p q) :
    path.verts.length = path.pathLen + 1 := by
  induction path with
  | single p => rfl
  | cons adj rest ih =>
      show (rest.verts.length) + 1 = (rest.pathLen + 1) + 1
      rw [ih]

end AdjPath

/-- **Triangle bound along a path (PROVED).**  The endpoints of an
`AdjPath` are separated by at most its step count:
`S.dist p q ≤ path.pathLen`.  Proof by induction on the path: each `cons`
step `p ~ p'` adds `dist_adj_le (≤ 1)` to the inductive `dist p' q`, and the
triangle inequality bounds `dist p q ≤ dist p p' + dist p' q ≤ 1 + pathLen`. -/
theorem dist_le_pathLen {S : SepLattice} {p q : S.toLattice.Plaquette}
    (path : AdjPath S p q) : S.dist p q ≤ path.pathLen := by
  induction path with
  | single p =>
      -- single-vertex path: pathLen = 0 and dist p p = 0 (dist_self).
      show S.dist p p ≤ 0
      rw [S.dist_self p]
      exact Nat.le_refl 0
  | @cons p p' q adj rest ih =>
      -- each step `p ~ p'` is distance ≤ 1; triangle through p'.
      have hstep : S.dist p p' ≤ 1 := S.dist_adj_le p p' adj
      have htri : S.dist p q ≤ S.dist p p' + S.dist p' q := S.dist_triangle p p' q
      have hsum : S.dist p q ≤ 1 + rest.pathLen :=
        Nat.le_trans htri (Nat.add_le_add hstep ih)
      show S.dist p q ≤ rest.pathLen + 1
      omega

/-- **`connected_spanning_size_ge` (THE new combinatorial lemma — PROVED).**

Let `X` be a polymer over a separation-equipped lattice `S`, and suppose `X`
*spans* the separation between `p` and `q`: it carries an in-polymer
adjacency path `path : AdjPath S p q` whose vertex list is a sublist of `X`
(`hsub : path.verts.Sublist X` — every path vertex lies, in order, in the
polymer).  If `p` and `q` are separated by at least `n` (`n ≤ S.dist p q`),
then the polymer has size at least `n`:

    size X ≥ n.

PROOF (mirrors `ClusterCount.polymerToWalk`).  The path has
`pathLen` steps and `pathLen + 1` vertices (`verts_length`); the triangle
inequality bounds `n ≤ S.dist p q ≤ pathLen ≤ pathLen + 1 = verts.length`
(`dist_le_pathLen`), and being a sublist of `X` its vertex count is at most
`size X` (core `List.Sublist.length_le`).  Hence `n ≤ size X`. -/
theorem connected_spanning_size_ge {S : SepLattice} (X : Polymer S.toLattice)
    {p q : S.toLattice.Plaquette} (path : AdjPath S p q)
    (hsub : path.verts.Sublist X) {n : Nat} (hsep : n ≤ S.dist p q) :
    n ≤ Polymer.size X := by
  -- n ≤ dist p q ≤ pathLen ≤ pathLen + 1 = verts.length ≤ X.length = size X
  have h1 : n ≤ path.pathLen := Nat.le_trans hsep (dist_le_pathLen path)
  have h2 : path.pathLen ≤ path.verts.length := by
    rw [AdjPath.verts_length path]; exact Nat.le_succ _
  have h3 : path.verts.length ≤ X.length := List.Sublist.length_le hsub
  -- size X = X.length
  show n ≤ X.length
  exact Nat.le_trans h1 (Nat.le_trans h2 h3)

/-! ## 3. The pinned cluster tail (`pinnedClusterTail`)

The KP series for polymers of size `≥ n`, after the single-rep collapse and
the cluster-count bound, is the geometric tail

    Σ_{m<d}  kpTerm cc w r (n+m)
        =  Σ_{m<d}  animalCount (n+m) · (coeffW w r)^(n+m) · eSurrogate^(n+m).

Each summand is `≤ ρ^(n+m)` with `ρ = kpRatio cc w r = K·(coeffW w r)·e`
(`kpTerm_le_geom`); `ρ^(n+m) ≃ ρ^n · ρ^m`, and for `ρ ≤ 1/2` the partial sum
`Σ_m ρ^m ≤ 2`.  Hence the tail is `≤ 2·ρ^n = tailConst·ρ^n`. -/

/-- **The geometric partial sum is `≤ 2` for ratio `≤ 1/2`.**  For
`0 ≤ ρ ≤ 1/2`, `Σ_{i<d} ρ^i ≤ 2`, via `geometric_tail_closure` at head
`f₀ = 1`, ratio `ρ`, dominator `H = 2` (recurrence `1 + ρ·2 ≤ 1 + (1/2)·2 =
2`), with `ρ^i = 1·ρ^i`. -/
theorem geom_partial_le_two {ρ : Q'} (hρ0 : (0 : Q') ≤ ρ)
    (hρ : ρ ≤ Q'.mkPos 1 2 (by decide)) (d : Nat) :
    finSum (fun i => ρ ^ i) d ≤ Q'.ofNat 2 := by
  -- recurrence 1 + ρ·2 ≤ 2
  have hrec : (1 : Q') + ρ * Q'.ofNat 2 ≤ Q'.ofNat 2 := by
    have h2 : ρ * Q'.ofNat 2 ≤ Q'.mkPos 1 2 (by decide) * Q'.ofNat 2 :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hρ (by decide)
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_left (1 : Q') _ _ h2) ?_
    decide
  have hclose : ∀ N, finSum (fun i => (1 : Q') * ρ ^ i) N ≤ Q'.ofNat 2 :=
    geometric_tail_closure (1 : Q') ρ (Q'.ofNat 2) hρ0 (by decide) hrec
  -- ρ^i = 1·ρ^i  (up to eqv), so the sums agree
  have hcongr : (finSum (fun i => ρ ^ i) d).eqv
      (finSum (fun i => (1 : Q') * ρ ^ i) d) :=
    RationalTail.finSum_eqv_congr _ _
      (fun i => Q'.eqv_symm (Q'.one_mul_eqv (ρ ^ i))) d
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hcongr) (hclose d)

/-- **The strong-coupling ratio threshold `ρ < 1` (PROVED).**  When
`ρ = kpRatio cc w r ≤ 1/2` the KP geometric ratio is `< 1` — the genuine
convergence condition for the cluster tail.  Proved on the cross-product
`Int` representation: `ρ ≤ 1/2` is `2·ρ.num ≤ ρ.den`, and `0 < ρ.den`, so
`ρ.num < ρ.den`, i.e. `ρ < 1`. -/
theorem ratio_lt_one {ρ : Q'} (hρ : ρ ≤ Q'.mkPos 1 2 (by decide)) :
    ρ < (1 : Q') := by
  -- Cross-product form.  `mkPos 1 2` has num = 1, den = 2; `(1:Q')` has
  -- num = 1, den = 1.  `ρ ≤ 1/2` is `ρ.num · 2 ≤ 1 · ρ.den = ρ.den`; the
  -- goal `ρ < 1` is `ρ.num · 1 < 1 · ρ.den`, i.e. `ρ.num < ρ.den`.
  show ρ.num * ((1 : Q').den : Int) < (1 : Q').num * (ρ.den : Int)
  have hle : ρ.num * ((Q'.mkPos 1 2 (by decide)).den : Int)
      ≤ (Q'.mkPos 1 2 (by decide)).num * (ρ.den : Int) := hρ
  have hden2 : ((Q'.mkPos 1 2 (by decide)).den : Int) = 2 := by decide
  have hnum2 : (Q'.mkPos 1 2 (by decide)).num = 1 := rfl
  have hden1 : ((1 : Q').den : Int) = 1 := by decide
  have hnum1 : (1 : Q').num = 1 := by decide
  rw [hden2, hnum2] at hle
  rw [hden1, hnum1]
  -- hle : ρ.num * 2 ≤ 1 * ρ.den ;  goal : ρ.num * 1 < 1 * ρ.den
  have hdpos : 0 < ρ.den := Q'.den_pos ρ
  have hdposI : (0 : Int) < (ρ.den : Int) := by exact_mod_cast hdpos
  omega

/-- **`pinnedClusterTail` (PROVED).**  The geometric TAIL of the KP cluster
series for polymers of size `≥ n`: with `ρ = kpRatio cc w r = K·(coeffW w r)·
eSurrogate`, for `0 ≤ w` and the strong-coupling threshold `ρ ≤ 1/2`,

    Σ_{m<d}  kpTerm cc w r (n+m)
       =  Σ_{m<d}  animalCount (n+m) · (coeffW w r)^(n+m) · eSurrogate^(n+m)
       ≤  2 · ρ^n        (= tailConst · ρ^n,  tailConst = 2),    ∀ d.

This is the same KP engine as `kp_criterion_of_count`, summed from index `n`
instead of `0`: each summand is `≤ ρ^(n+m)` (`kpTerm_le_geom`),
`ρ^(n+m) ≃ ρ^n·ρ^m`, the partial sum `Σ_m ρ^m ≤ 2` (`geom_partial_le_two`),
and `ρ^n ≥ 0` factors out.  The threshold `ρ ≤ 1/2` makes the ratio `< 1`
(`ratio_lt_one`), so the tail decays geometrically in the size floor `n`. -/
theorem pinnedClusterTail {L : Lattice} {p : L.Plaquette}
    (cc : ClusterCountBound L p) {w : Q'} (hw : (0 : Q') ≤ w) (r : Rep)
    (hthr : kpRatio cc w r ≤ Q'.mkPos 1 2 (by decide)) (n d : Nat) :
    finSum (fun m => kpTerm cc w r (n + m)) d
      ≤ Q'.ofNat 2 * (kpRatio cc w r) ^ n := by
  -- ρ := kpRatio cc w r (kept inline; `set` is a Mathlib tactic, unavailable).
  -- ρ nonneg
  have hρ_nn : (0 : Q') ≤ kpRatio cc w r := by
    unfold kpRatio
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ cc.K_nonneg (coeffW_nonneg hw r)) eSurrogate_nonneg
  have hρn_nn : (0 : Q') ≤ (kpRatio cc w r) ^ n :=
    Q'.pow_nonneg (kpRatio cc w r) hρ_nn n
  -- (1) termwise: kpTerm cc w r (n+m) ≤ ρ^(n+m)
  have hterm : ∀ m, kpTerm cc w r (n + m) ≤ (kpRatio cc w r) ^ (n + m) := by
    intro m; exact kpTerm_le_geom cc hw r (n + m)
  have hsum1 : finSum (fun m => kpTerm cc w r (n + m)) d
      ≤ finSum (fun m => (kpRatio cc w r) ^ (n + m)) d :=
    CharacterTail.finSum_le_termwise _ _ hterm d
  -- (2) ρ^(n+m) ≃ ρ^n · ρ^m
  have hsum2 : (finSum (fun m => (kpRatio cc w r) ^ (n + m)) d).eqv
      (finSum (fun m => (kpRatio cc w r) ^ n * (kpRatio cc w r) ^ m) d) :=
    RationalTail.finSum_eqv_congr _ _
      (fun m => Q'.pow_add_eqv (kpRatio cc w r) n m) d
  -- (3) Σ (ρ^n · ρ^m) ≃ ρ^n · Σ ρ^m
  have hsum3 : (finSum (fun m => (kpRatio cc w r) ^ n * (kpRatio cc w r) ^ m) d).eqv
      ((kpRatio cc w r) ^ n * finSum (fun m => (kpRatio cc w r) ^ m) d) :=
    Q'.eqv_symm (RationalTail.const_mul_finSum
      (fun m => (kpRatio cc w r) ^ m) ((kpRatio cc w r) ^ n) d)
  -- (4) ρ^n · Σ ρ^m ≤ ρ^n · 2
  have hgeo : finSum (fun m => (kpRatio cc w r) ^ m) d ≤ Q'.ofNat 2 :=
    geom_partial_le_two hρ_nn hthr d
  have hsum4 : (kpRatio cc w r) ^ n * finSum (fun m => (kpRatio cc w r) ^ m) d
      ≤ (kpRatio cc w r) ^ n * Q'.ofNat 2 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hgeo hρn_nn
  -- (5) ρ^n · 2 ≃ 2 · ρ^n
  have hcomm : ((kpRatio cc w r) ^ n * Q'.ofNat 2).eqv (Q'.ofNat 2 * (kpRatio cc w r) ^ n) :=
    Q'.mul_comm_eqv ((kpRatio cc w r) ^ n) (Q'.ofNat 2)
  -- chain everything
  refine Q'.le_trans' _ _ _ hsum1 ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum2) ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum3) ?_
  refine Q'.le_trans' _ _ _ hsum4 ?_
  exact Q'.le_of_eqv hcomm

/-! ## 4. Documentation: PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED in this Wall-2 finite-pieces module (all genuine):

  * `coeffW_succ_le` / `coeffW_le_one_le` — the Casimir-decay monotonicity
    `coeffW w r ≤ coeffW w 1` for `r ≥ 1` at strong coupling `w ≤ 1/2`;
  * `activity_le_leading` — the constrained connected polymer activity is
    dominated by the leading-rep power `(coeffW w 1)^{size X}`;
  * `SepLattice` (+ `toySep` sanity witness) — the separation structure with
    the GENUINE graph-metric fields `dist_self`, `dist_adj_le` (adjacency
    step `≤ 1`), `dist_triangle`;
  * `AdjPath` (+ `verts`, `pathLen`, `verts_length`), `dist_le_pathLen` (the
    triangle bound along a path), and `connected_spanning_size_ge` — a
    polymer spanning separation `≥ n` has `size ≥ n`;
  * `geom_partial_le_two`, `ratio_lt_one`, `pinnedClusterTail` — the
    geometric tail `Σ_{m<d} kpTerm (n+m) ≤ 2·ρ^n` with `ρ ≤ 1/2 < 1`.

NAMED-open (carried as hypotheses / structures, NEVER faked):

  * `ClusterCountBound` — the lattice-animal count (inhabited unconditionally
    elsewhere via the walk encoding); here a hypothesis of `pinnedClusterTail`.
  * the physical 4D `SepLattice.dist` — the abstract structure is inhabited
    by `toySep` (sanity); the genuine Euclidean plaquette distance is the
    geometry layer, not this combinatorial one.

This module is NOT the full cluster expansion, NOT a continuum limit, and
NOT a 4D Yang–Mills mass gap; it is the finite Wall-2 input the real
connected-correlator decay consumes. -/

end YMGap.Continuum.PinnedCluster

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.PinnedCluster.coeffW_succ_le
#print axioms YMGap.Continuum.PinnedCluster.coeffW_le_one_le
#print axioms YMGap.Continuum.PinnedCluster.activity_le_leading
#print axioms YMGap.Continuum.PinnedCluster.toySep
#print axioms YMGap.Continuum.PinnedCluster.AdjPath.verts_length
#print axioms YMGap.Continuum.PinnedCluster.dist_le_pathLen
#print axioms YMGap.Continuum.PinnedCluster.connected_spanning_size_ge
#print axioms YMGap.Continuum.PinnedCluster.geom_partial_le_two
#print axioms YMGap.Continuum.PinnedCluster.ratio_lt_one
#print axioms YMGap.Continuum.PinnedCluster.pinnedClusterTail
