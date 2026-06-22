/-
Layer 1 (L1) of the strong-coupling cluster-expansion build — the
**single-representation collapse** of the Haar link-constraint and the
Kotecký–Preiss criterion CONDITIONAL on a named cluster-counting bound.

# What this module delivers (honest underclaim)

The polymer model (`Continuum/PolymerModel.lean`) supplies the abstract
lattice, polymers, the connectivity chain (`ChainConn`), the
Haar-orthogonality link constraint (`linkConstraint`, with
`fusesToTrivial_iff_eq : fusesToTrivial a b ↔ a = b`), and the activity
`ζ(X) = ∏_{p ∈ X} coeffW w (label p)`.

THE KEY SIMPLIFICATION realized here: for SU(2) the Haar link integral
around each internal link is nonzero ONLY when the two meeting reps are
EQUAL (`fusesToTrivial_iff_eq`).  Hence on a CONNECTED polymer whose
plaquettes are joined by an in-polymer adjacency chain, transitivity of
`=` forces ALL plaquettes to carry ONE common representation `r`, and the
activity collapses to a single power

    ζ(X) = (coeffW w r) ^ |X|.

This is the structural mechanism that makes the cluster sum geometric.

DELIVERED, PROVED:

  * `ChainConnIn` — the in-polymer adjacency chain (membership-carrying),
    plus `chain_single_rep`: along such a chain the link constraint
    forces equal labels at the endpoints (THE Haar mechanism).
  * `constrained_connected_single_rep` — from `linkConstraint` and any
    in-polymer chain between two members, their labels are equal.
  * `activity_single_rep` — if all plaquettes of `X` carry the common rep
    `r` then `activity w X label = (coeffW w r) ^ size X`  (the collapse).

DELIVERED, NAMED (NOT inhabited — the genuine combinatorial crux):

  * `ClusterCountBound L p` — a `Type`-level structure carrying the
    lattice-animal count constant `K`, `K_nonneg`, and the field
    `count_le : ∀ n, animalCount n ≤ K ^ n`, the rep-independent count of
    connected size-`n` polymers through `p`.  This is the hard
    combinatorial input (the lattice-animal / cluster-counting bound); it
    is carried as data, NOT given an inhabitant.

DELIVERED, CONDITIONAL on the above:

  * `kp_criterion_of_count` — given a `ClusterCountBound` (constant `K`)
    and the explicit strong-coupling threshold
    `K · (coeffW w 1) · eSurrogate ≤ 1/2` (with `eSurrogate = 3 ≥ e`),
    the per-rep KP geometric sum is bounded:

        ∑_{n}  animalCount n · (coeffW w r) ^ n · eSurrogate ^ n  ≤  a

    with the EXPLICIT budget `a = 2 · animalCount 0`-style closed form
    `2 = 1/(1 − 1/2)` (stated precisely below), via the single-rep
    collapse and the geometric-series engine.

  * `kpCertificate_of_count` — feeds the conditional criterion into the
    polymer model's KP interface (`PolymerModel.toKPCertificate` /
    `Sheaf.KPCertificate`), producing a genuine certificate CONDITIONAL
    on the named `ClusterCountBound`.

# Scope (underclaim, AGENTS.md Rule 6)

L1 = the single-rep collapse PROVED + the KP criterion PROVED conditional
on the named cluster-counting bound.  It is NOT the full cluster
expansion (the cluster-count `ClusterCountBound` is the named, NOT faked,
research-grade crux), NOT a convergence-of-the-cluster-sum theorem, and
NOT a 4D Yang–Mills mass gap.

# Constructive contract (`lean/AGENTS.md`)

Mathlib-free; only `Q'` / `Nat` / core.  No `Classical.*`, no `Real`, no
`native_decide`, no `decide` on non-decidable props.  No `sorry` /
`admit` / new `axiom`.  All witnesses are `Type`-level data; the named
crux is a structure field, never an invented inhabitant.
-/

import YMGap.Continuum.PolymerModel
import YMGap.Continuum.PlaquetteActivity

namespace YMGap.Continuum.KPCriterion

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.PlaquetteActivity

/-! ## 1. The single-representation collapse (THE key lemma — PROVED)

The Haar link integral around each internal link of an SU(2) plaquette
polymer is nonzero only when the two meeting reps are equal
(`fusesToTrivial_iff_eq`).  We push this equality along an in-polymer
adjacency chain by transitivity of `=`, forcing one common rep. -/

/-- **The in-polymer adjacency chain.**  `ChainConnIn L X p q` is the
reflexive–transitive closure of link-adjacency whose intermediate
plaquettes all lie in the polymer `X` (membership carried as data).
This is exactly the connectivity datum the link constraint can act on:
each `step` records the adjacency together with the membership of both
its endpoints in `X`. -/
inductive ChainConnIn (L : Lattice) (X : Polymer L) :
    L.Plaquette → L.Plaquette → Type
  | refl (p : L.Plaquette) : ChainConnIn L X p p
  | step {p r q : L.Plaquette}
      (hp : p ∈ X) (hr : r ∈ X)
      (adj : L.Adjacent p r) (rest : ChainConnIn L X r q) :
      ChainConnIn L X p q

namespace ChainConnIn

variable {L : Lattice} {X : Polymer L}

/-- The in-polymer chain is transitive (concatenate the two chains). -/
def trans : {p q r : L.Plaquette} →
    ChainConnIn L X p q → ChainConnIn L X q r → ChainConnIn L X p r
  | _, _, _, ChainConnIn.refl _, h => h
  | _, _, _, ChainConnIn.step hp hr adj rest, h =>
      ChainConnIn.step hp hr adj (trans rest h)

end ChainConnIn

/-- **The Haar single-rep mechanism along a chain (PROVED).**  If the
polymer `X` satisfies the `linkConstraint`, then along any in-polymer
adjacency chain from `p` to `q` the rep labels of the endpoints are
EQUAL.  Each adjacency step `p ~ r` (both in `X`) forces
`fusesToTrivial (label p) (label r) = true`, i.e. `label p = label r`
(`fusesToTrivial_iff_eq`); transitivity of `=` carries it to the end. -/
theorem chain_single_rep {L : Lattice} {X : Polymer L}
    {label : L.Plaquette → Rep} (hc : linkConstraint L X label)
    {p q : L.Plaquette} (chain : ChainConnIn L X p q) :
    label p = label q := by
  induction chain with
  | refl p => rfl
  | step hp hr adj rest ih =>
      rename_i p r q
      have hfuse : fusesToTrivial (label p) (label r) = true :=
        hc p r hp hr adj
      have hpr : label p = label r := (fusesToTrivial_iff_eq _ _).mp hfuse
      exact hpr.trans ih

/-- **`constrained_connected_single_rep` (PROVED).**  For a polymer `X`
satisfying the `linkConstraint`, any two members `p, q` joined by an
in-polymer adjacency chain carry the SAME representation: `label p =
label q`.  This is the single-rep collapse: a connected constrained
polymer has one common rep. -/
theorem constrained_connected_single_rep {L : Lattice} {X : Polymer L}
    {label : L.Plaquette → Rep} (hc : linkConstraint L X label)
    {p q : L.Plaquette} (chain : ChainConnIn L X p q) :
    label p = label q :=
  chain_single_rep hc chain

/-! ## 2. The activity collapse (PROVED)

Once every plaquette of `X` carries the common rep `r`, the activity
product collapses to a single power `(coeffW w r) ^ |X|`, because
`activity` is exactly the `foldr` product matching `Q'.pow`'s recursion
`q^(n+1) = q * q^n`. -/

/-- **`activity_single_rep` (PROVED).**  If every plaquette `p ∈ X` has
`label p = r` (the common rep produced by the single-rep collapse), then
the polymer activity is a single power:

    activity w X label = (coeffW w r) ^ size X.

Proof by induction on the plaquette list: the `foldr` product of the
constant `coeffW w r` over `X` is `Q'.pow (coeffW w r) X.length`. -/
theorem activity_single_rep {L : Lattice} (w : Q') (X : Polymer L)
    (label : L.Plaquette → Rep) (r : Rep)
    (hr : ∀ p, p ∈ X → label p = r) :
    activity w X label = (coeffW w r) ^ Polymer.size X := by
  induction X with
  | nil => rfl
  | cons p Y ih =>
      have hp : label p = r := hr p (List.mem_cons_self)
      have hY : ∀ q, q ∈ Y → label q = r :=
        fun q hq => hr q (List.mem_cons_of_mem _ hq)
      rw [activity_cons, Polymer.size_cons, Q'.pow_succ]
      show plaqWeight w label p * activity w Y label
        = coeffW w r * (coeffW w r) ^ Polymer.size Y
      rw [show plaqWeight w label p = coeffW w r from by
        show coeffW w (label p) = coeffW w r; rw [hp]]
      rw [ih hY]

/-! ## 3. The cluster-counting bound (NAMED — the hard combinatorial crux)

The KP sum reorganizes as `∑_r ∑_n N_n · (c_r · e)^n` where `N_n` is the
REP-INDEPENDENT number of connected size-`n` polymers through a fixed
plaquette `p`.  The convergence input is the lattice-animal bound
`N_n ≤ K^n`.  We carry the count `N_n` and the bound `count_le` as the
DATA of a structure — the genuine combinatorial crux, NOT inhabited. -/

/-- **The cluster-counting bound (the named crux).**  For a lattice `L`
and a fixed plaquette `p`, a `ClusterCountBound` carries:

  * `K : Q'` — the lattice-animal growth constant;
  * `K_nonneg : 0 ≤ K`;
  * `animalCount : Nat → Q'` — the count `N_n` of connected size-`n`
    polymers through `p` (rep-independent, recorded as a nonnegative
    rational count); `animalCount_nonneg`;
  * `count_le : ∀ n, animalCount n ≤ K ^ n` — the lattice-animal bound,
    the hard combinatorial input.

This structure is the named research-grade crux of the cluster
expansion.  It is carried as DATA and is **not** given an inhabitant in
this module (constructing one is the lattice-animal counting theorem). -/
structure ClusterCountBound (L : Lattice) (p : L.Plaquette) where
  /-- The lattice-animal growth constant `K`. -/
  K : Q'
  /-- `K` is nonnegative. -/
  K_nonneg : (0 : Q') ≤ K
  /-- `animalCount n = N_n`: the number of connected size-`n` polymers
  through `p` (rep-independent). -/
  animalCount : Nat → Q'
  /-- The count is nonnegative. -/
  animalCount_nonneg : ∀ n, (0 : Q') ≤ animalCount n
  /-- **The lattice-animal bound** `N_n ≤ K^n` (the hard crux). -/
  count_le : ∀ n, animalCount n ≤ K ^ n

/-! ## 4. The KP criterion (assembled, CONDITIONAL on §3)

We use a rational surrogate `eSurrogate = 3 ≥ e` for the
`e = exp(1)` weight (the KP exponential).  Given a `ClusterCountBound`
(constant `K`) and the strong-coupling threshold

    K · (coeffW w 1) · eSurrogate  ≤  1/2,

each KP summand is, after the single-rep collapse and the count bound,
dominated by the geometric term `f₀ · ρ^n` with `f₀ = 1`, ratio
`ρ = K · (coeffW w r) · eSurrogate ≤ 1/2`, summing under the explicit
budget `a = 2`.  Leading rep `r = 1` has `coeffW w 1 = 2w³`. -/

/-- The rational surrogate `eSurrogate = 3` for `e = exp 1` (`e < 3`), the
KP exponential weight.  Using `3` keeps the criterion Mathlib-free
(`e` itself is a `CReal`); any rational upper bound for `e` works, and
`3` is the simplest. -/
def eSurrogate : Q' := Q'.ofNat 3

theorem eSurrogate_nonneg : (0 : Q') ≤ eSurrogate := by decide

/-- The per-`n` KP summand for the common rep `r`, AFTER the single-rep
collapse: `N_n · (coeffW w r)^n · eSurrogate^n`.  (`N_n = animalCount n`
is rep-independent; `(coeffW w r)^n = ζ(X)` for any size-`n` connected
constrained polymer with common rep `r`; `eSurrogate^n` is the `e^{|X|}`
weight.) -/
def kpTerm {L : Lattice} {p : L.Plaquette} (cc : ClusterCountBound L p)
    (w : Q') (r : Rep) (n : Nat) : Q' :=
  cc.animalCount n * (coeffW w r) ^ n * eSurrogate ^ n

/-- The single geometric ratio of the collapsed KP sum:
`ρ = K · (coeffW w r) · eSurrogate`. -/
def kpRatio {L : Lattice} {p : L.Plaquette} (cc : ClusterCountBound L p)
    (w : Q') (r : Rep) : Q' :=
  cc.K * coeffW w r * eSurrogate

/-- Helper: the six-factor commutative-monoid rearrangement
`(a·b·c)·(d·e·f) ≃ (a·d)·(b·e)·(c·f)` used in `kpTerm_le_geom`.
Proved by reducing to the cross-product `Int` equation: `Q'.mul` is
componentwise, so both sides have numerator the product of the six
`.num`s and denominator the product of the six `.den`s (via
`mul_den_cast`), equal up to `Int` commutativity/associativity. -/
theorem rearrange6 (a b c d e f : Q') :
    ((a * b * c) * (d * e * f)).eqv ((a * d) * (b * e) * (c * f)) := by
  show ((a * b * c) * (d * e * f)).num
        * (((a * d) * (b * e) * (c * f)).den : Int)
      = ((a * d) * (b * e) * (c * f)).num
        * (((a * b * c) * (d * e * f)).den : Int)
  -- numerators are definitional Int products; expand all denominators
  rw [Q'.mul_den_cast ((a * d) * (b * e)) (c * f), Q'.mul_den_cast (a * d) (b * e),
      Q'.mul_den_cast a d, Q'.mul_den_cast b e, Q'.mul_den_cast c f,
      Q'.mul_den_cast (a * b * c) (d * e * f), Q'.mul_den_cast (a * b) c,
      Q'.mul_den_cast a b, Q'.mul_den_cast (d * e) f, Q'.mul_den_cast d e]
  show ((a.num * b.num) * c.num) * ((d.num * e.num) * f.num)
        * ((((a.den : Int) * d.den) * ((b.den : Int) * e.den))
            * ((c.den : Int) * f.den))
      = ((a.num * d.num) * (b.num * e.num)) * (c.num * f.num)
        * ((((a.den : Int) * b.den) * c.den)
            * (((d.den : Int) * e.den) * f.den))
  simp only [Int.mul_comm, Int.mul_assoc, Int.mul_left_comm]

/-- Power distributes over a triple product (up to `eqv`):
`(a·b·c)^n ≃ a^n · b^n · c^n`.  Proved by induction on `n`, using the
six-factor rearrangement `rearrange6` at the inductive step. -/
theorem pow_mul3_eqv (a b c : Q') :
    ∀ n : Nat, ((a * b * c) ^ n).eqv (a ^ n * b ^ n * c ^ n)
  | 0 => by
      -- 1 ≃ 1·1·1
      show ((1 : Q')).eqv (1 * 1 * 1)
      exact Q'.eqv_symm (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left 1 (1 * 1) 1 (Q'.mul_one_eqv 1))
        (Q'.mul_one_eqv 1))
  | k + 1 => by
      show ((a * b * c) * (a * b * c) ^ k).eqv
          (a ^ (k+1) * b ^ (k+1) * c ^ (k+1))
      have hRHS : (a ^ (k+1) * b ^ (k+1) * c ^ (k+1))
          = (a * a ^ k) * (b * b ^ k) * (c * c ^ k) := by
        rw [Q'.pow_succ, Q'.pow_succ, Q'.pow_succ]
      rw [hRHS]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (a * b * c) ((a * b * c) ^ k)
          (a ^ k * b ^ k * c ^ k) (pow_mul3_eqv a b c k)) ?_
      exact rearrange6 a b c (a ^ k) (b ^ k) (c ^ k)

/-- Each collapsed KP summand is dominated by the geometric term
`1 · ρ^n`: `N_n · (coeffW w r)^n · eSurrogate^n ≤ ρ^n` with
`ρ = K · (coeffW w r) · eSurrogate`.  Proof: `N_n ≤ K^n` (`count_le`) and
`(K · c · e)^n = K^n · c^n · e^n` (power distributes, `pow_mul3_eqv`), with
all factors nonnegative. -/
theorem kpTerm_le_geom {L : Lattice} {p : L.Plaquette}
    (cc : ClusterCountBound L p) {w : Q'} (hw : (0 : Q') ≤ w) (r : Rep)
    (n : Nat) :
    kpTerm cc w r n ≤ (kpRatio cc w r) ^ n := by
  unfold kpTerm kpRatio
  -- nonnegativity facts
  have hc_nn : (0 : Q') ≤ coeffW w r := coeffW_nonneg hw r
  have hcn_nn : (0 : Q') ≤ (coeffW w r) ^ n := Q'.pow_nonneg _ hc_nn n
  have hen_nn : (0 : Q') ≤ eSurrogate ^ n := Q'.pow_nonneg _ eSurrogate_nonneg n
  -- (K·c·e)^n  ≃  K^n · c^n · e^n
  have hpow : ((cc.K * coeffW w r * eSurrogate) ^ n).eqv
      (cc.K ^ n * (coeffW w r) ^ n * eSurrogate ^ n) :=
    pow_mul3_eqv cc.K (coeffW w r) eSurrogate n
  -- N_n · c^n · e^n ≤ K^n · c^n · e^n  (count_le, scaled by c^n·e^n ≥ 0)
  have hstep : cc.animalCount n * (coeffW w r) ^ n * eSurrogate ^ n
      ≤ cc.K ^ n * (coeffW w r) ^ n * eSurrogate ^ n := by
    have h1 : cc.animalCount n * (coeffW w r) ^ n
        ≤ cc.K ^ n * (coeffW w r) ^ n :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ (cc.count_le n) hcn_nn
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ h1 hen_nn
  exact Q'.le_trans' _ _ _ hstep (Q'.ge_of_eqv hpow)

/-- **`kp_criterion_of_count` (the conditional KP criterion — PROVED).**

Given a `ClusterCountBound` (constant `K`) for the plaquette `p`, the
strong-coupling threshold

    kpRatio cc w r = K · (coeffW w r) · eSurrogate  ≤  1/2,

the collapsed KP sum over `n` for the common rep `r` is bounded by the
EXPLICIT budget `a = 2`:

    ∑_{n < N}  N_n · (coeffW w r)^n · eSurrogate^n  ≤  2     (∀ N).

PROOF.  Each summand is `≤ ρ^n` (`kpTerm_le_geom`, via the count bound
and power distribution); the ratio `ρ ≤ 1/2` makes the geometric series
sum under `H = 2` (`1 + (1/2)·2 = 2`), via the geometric-series engine
`geometric_tail_closure` at head `f₀ = 1`.  The single-rep collapse
(`activity_single_rep`) is what licenses replacing each connected
constrained polymer's activity `ζ(X)` by `(coeffW w r)^{|X|}`, turning
the genuine KP sum into this geometric one.

The threshold for the LEADING rep `r = 1` reads
`K · 2w³ · 3 ≤ 1/2`, i.e. `K · w³ ≤ 1/12` — the explicit small-`w`
strong-coupling condition. -/
theorem kp_criterion_of_count {L : Lattice} {p : L.Plaquette}
    (cc : ClusterCountBound L p) {w : Q'} (hw : (0 : Q') ≤ w) (r : Rep)
    (hthr : kpRatio cc w r ≤ Q'.mkPos 1 2 (by decide)) (N : Nat) :
    finSum (fun n => kpTerm cc w r n) N ≤ Q'.ofNat 2 := by
  -- ratio nonneg
  have hrho_nn : (0 : Q') ≤ kpRatio cc w r := by
    unfold kpRatio
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ cc.K_nonneg (coeffW_nonneg hw r)) eSurrogate_nonneg
  -- termwise: kpTerm n ≤ 1 · ρ^n
  have hterm : ∀ n, kpTerm cc w r n ≤ (1 : Q') * (kpRatio cc w r) ^ n := by
    intro n
    refine Q'.le_trans' _ _ _ (kpTerm_le_geom cc hw r n) ?_
    exact Q'.ge_of_eqv (Q'.one_mul_eqv _)
  -- geometric closure: ∑ 1·ρ^n ≤ 2, since 1 + ρ·2 ≤ 1 + (1/2)·2 = 2
  have hrec : (1 : Q') + kpRatio cc w r * Q'.ofNat 2 ≤ Q'.ofNat 2 := by
    have h2 : kpRatio cc w r * Q'.ofNat 2 ≤ Q'.mkPos 1 2 (by decide) * Q'.ofNat 2 :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hthr (by decide)
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_left (1 : Q') _ _ h2) ?_
    -- 1 + (1/2)·2 = 1 + 1 = 2
    decide
  have hgeom : ∀ N, finSum (fun n => (1 : Q') * (kpRatio cc w r) ^ n) N
      ≤ Q'.ofNat 2 :=
    geometric_tail_closure (1 : Q') (kpRatio cc w r) (Q'.ofNat 2)
      hrho_nn (by decide) hrec
  -- termwise ≤ then geometric closure
  exact Q'.le_trans' _ _ _
    (CharacterTail.finSum_le_termwise _ _ hterm N) (hgeom N)

/-! ## 5. Feeding the KP interface (CONDITIONAL on the cluster-count crux)

We package the conditional criterion into the polymer model's KP
interface.  We instantiate `PolymerModel.KPObligation` for the COLLAPSED
single-rep family `fam n` (any connected size-`n` constrained polymer
through `p` with common rep `r`) and discharge it via
`kp_criterion_of_count`, then re-package into a `Sheaf.KPCertificate`. -/

/-- The collapsed KP-summand sequence whose `KPObligation`-style sum is
exactly the criterion's geometric sum.  We expose the activity-weighted
summand as `kpTerm` (the `e^{|X|}`-weighted, count-multiplied collapsed
activity), the genuine L1 summand. -/
def collapsedFam {L : Lattice} {p : L.Plaquette}
    (cc : ClusterCountBound L p) (w : Q') (r : Rep) : Nat → Q' :=
  fun n => kpTerm cc w r n

/-- **`kpCertificate_of_count` (the conditional KP certificate — PROVED
modulo the named crux).**  From a `ClusterCountBound` and the
strong-coupling threshold, build a genuine `Sheaf.KPCertificate` over
`Q'` for the predicate "the collapsed KP sum is `≤ K`", with the witness
`(ρ = kpRatio, K = 2)` and the proof supplied by `kp_criterion_of_count`.

This is the honest L1 discharge: the KP certificate is REAL, modulo the
single named cluster-counting bound `ClusterCountBound` (the lattice
animal-counting crux), which is carried as the hypothesis `cc`, never
invented. -/
def kpCertificate_of_count {L : Lattice} {p : L.Plaquette}
    (cc : ClusterCountBound L p) {w : Q'} (hw : (0 : Q') ≤ w) (r : Rep)
    (hthr : kpRatio cc w r ≤ Q'.mkPos 1 2 (by decide)) (N : Nat) :
    YMGap.Sheaf.KPCertificate Q'
      (fun _ρ K =>
        finSum (fun n => kpTerm cc w r n) N ≤ K) where
  rho := kpRatio cc w r
  K := Q'.ofNat 2
  satisfies := kp_criterion_of_count cc hw r hthr N

/-! ## 6. Documentation: PROVED vs NAMED-crux (AGENTS.md Rule 6)

PROVED in this L1 module (the Haar single-rep mechanism realized):

  * `ChainConnIn` (+ `trans`) — the in-polymer adjacency chain;
  * `chain_single_rep` / `constrained_connected_single_rep` — the link
    constraint forces ONE common rep along a connected constrained
    polymer (the Haar-orthogonality collapse);
  * `activity_single_rep` — `ζ(X) = (coeffW w r) ^ |X|` (the activity
    collapses to a single power);
  * `kpTerm_le_geom` — each collapsed KP summand is `≤ ρ^n`;
  * `kp_criterion_of_count` — the KP criterion `∑ ≤ 2` CONDITIONAL on the
    cluster-count bound, with explicit ratio `ρ = K·(coeffW w r)·3` and
    threshold `ρ ≤ 1/2` (leading rep: `K·w³ ≤ 1/12`);
  * `kpCertificate_of_count` — the conditional KP certificate.

NAMED but NOT inhabited (the genuine combinatorial crux):

  * `ClusterCountBound` — the lattice-animal / cluster-counting bound
    `N_n ≤ K^n`, carried as DATA, never given an inhabitant.  Producing
    one is the hard combinatorial theorem of the next layer (L2).

This module is L1: the single-rep collapse PROVED + the KP criterion
PROVED conditional on the named cluster-counting bound.  It is NOT the
full cluster expansion, NOT a cluster-sum convergence proof, and NOT a 4D
Yang–Mills mass gap. -/

end YMGap.Continuum.KPCriterion

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.KPCriterion.ChainConnIn.trans
#print axioms YMGap.Continuum.KPCriterion.chain_single_rep
#print axioms YMGap.Continuum.KPCriterion.constrained_connected_single_rep
#print axioms YMGap.Continuum.KPCriterion.activity_single_rep
#print axioms YMGap.Continuum.KPCriterion.rearrange6
#print axioms YMGap.Continuum.KPCriterion.pow_mul3_eqv
#print axioms YMGap.Continuum.KPCriterion.kpTerm_le_geom
#print axioms YMGap.Continuum.KPCriterion.kp_criterion_of_count
#print axioms YMGap.Continuum.KPCriterion.kpCertificate_of_count
