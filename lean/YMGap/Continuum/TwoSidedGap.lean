/-
Track B / R2 — the TWO-SIDED radius-overlap program ("the middle from both sides").

# The idea (read first)

The strong-coupling window `[0, w₀ = 1/6]` is PROVED to cluster / gap
(`UniformCouplingGap`: a uniform-in-coupling located-gap rate `ρ_w ≤ 4/9 < 1`
on the WHOLE interval, resting on the genuine `|enumPolys|` lattice-animal
count).  A weak-coupling window `[w_w, 1]` WOULD cluster / gap — that is the
open continuum problem (`WeakCouplingGap.WeakClusteringBound`).  If the two
windows OVERLAP (`w_w ≤ w₀`) they cover the whole coupling line `[0, 1]`, giving
a clustering / located-gap bound at EVERY coupling at fixed spacing.

This module encodes that "both sides meet" picture so that

  * the STRONG side is GENUINELY PROVED (the `gap` field of `strongWindow` is
    discharged from the real `uniform_*` theorems, NOT posited);
  * the open content is EXACTLY two named, genuinely-uninhabited obligations —
    the `WeakWindow` (weak-coupling clustering on `[w_w, 1]`) and the
    `WindowOverlap` (`w_w ≤ w₀`, the weak control reaching DOWN to meet the
    strong window: the intermediate "middle");
  * the coverage / assembly is GENUINELY PROVED (a real interval case-split).

# What is PROVED vs. what is named-open

PROVED (axiom-clean, genuine):
  * `CouplingWindow` — a first-class window object carrying, for every `w` in
    `[lo, hi]`, a clustering rate `ρ_w < 1` together with the geometric cluster
    decay `clusterSpanSum (…) w gr d ≤ 2·ρ_w^d`.
  * `strongWindow p : CouplingWindow` — `lo = 0`, `hi = w₀ = 1/6`, the `gap`
    field DISCHARGED from `uniform_rho_le_endpoint` (`ρ_w ≤ 4/9 < 1`) and
    `uniform_cluster_decay` (the genuine uniform-in-coupling clustering).
  * `WindowOverlap` — a real `≤` `Prop` (`w_w ≤ w₀`).
  * `twoSided_covers` — the genuine interval arithmetic: given overlap, every
    `w` in `[0, 1]` lies in the strong OR the weak window (a real case-split on
    `w ≤ w₀`, using `Q'.le_of_not_le'` and `Q'.le_trans'`).
  * `twoSided_gap_all_couplings` — for every `w` in `[0, 1]` a clustering /
    located-gap bound holds: the STRONG branch (`w ≤ 1/6`) is fully proved from
    `strongWindow`; the WEAK branch consumes ONLY the supplied `WeakWindow`
    field.  So the all-coupling gap is CONDITIONAL ONLY on the (uninhabited)
    `WeakWindow` plus `WindowOverlap`.

NAMED-open (NOT faked — the continuum problem):
  * `WeakWindow` — weak-coupling clustering on `[w_w, 1]` (NO inhabitant; weak
    exponential clustering is the open continuum problem);
  * `WindowOverlap` — `w_w ≤ 1/6` (the "middle": no weak window with
    `w_w ≤ 1/6` is known — the middle wall).

# Tie to the continuum (the weak end)

The continuum limit (`a → 0`) is approached at the WEAK end (`w → 1`); the
all-coupling gap's weak end, made dimensionless against the dynamically-generated
scale, is the `RGLandingCertificate` shape.  A `WeakWindow` is exactly the
clustering datum `WeakCouplingGap.RGClusteringTransport` would supply from the
strong side through the middle; we expose that bridge (`weakWindow_yields_bound`,
`weakWindow_landing`) WITHOUT inhabiting anything.

# Honest scope (AGENTS.md Rule 6)

This module does NOT prove an unconditional all-coupling gap, and it does NOT
prove the 4D Yang–Mills continuum mass gap.  The STRONG window `[0, 1/6]` is
genuinely proved; the all-coupling (hence continuum) gap is REDUCED to the two
named uninhabited obligations `WeakWindow` and `WindowOverlap`.  No positivity is
faked; no weak-coupling clustering is constructed.

# Constructive contract (`lean/AGENTS.md`)

Mathlib-free; only `Q'` / `Nat` core.  No `Classical.*`, no `native_decide`, no
`decide` on non-decidable props (the interval case-split uses the genuine
`Q'.le_of_not_le'`, the located-gap data is the proved `uniform_*`).  No
`sorry` / `admit` / new `axiom` / `Prop := True`.  All witnesses are `Type`-level
data; the strong window's clustering is the real proved bound, the coverage is a
real proof, and the two named obligations are genuinely uninhabited.
-/

import YMGap.Continuum.UniformCouplingGap
import YMGap.Continuum.WeakCouplingGap

namespace YMGap.Continuum.TwoSidedGap

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.GenuineKP
open YMGap.Continuum.MayerClustering
open YMGap.Continuum.UniformCouplingGap
open YMGap.Continuum.WeakCouplingGap

/-! ## DELIVERABLE 1 — the strong window as a first-class PROVED object

A `CouplingWindow` packages "for all `w` in `[lo, hi]`, a clustering / located-gap
bound holds" as first-class data: for each such `w` a rate `ρ_w < 1` and the
geometric cluster decay `clusterSpanSum (zChainClusterCountBound p) w gr d ≤
2·ρ_w^d`.  The `gap` field is the genuine clustering witness; for the strong
window it is DISCHARGED from the proved `uniform_*` theorems. -/

/-- **`CouplingWindow` — a first-class clustering/gap window (`Type`-level data).**

For a plaquette `p` of the chain, an inhabitant supplies an interval `[lo, hi]`
(`lo ≤ hi`) and, for EVERY weight `w` in that interval, a clustering rate `ρ`
strictly below `1` together with the genuine geometric cluster decay
`clusterSpanSum (zChainClusterCountBound p) w gr d ≤ 2·ρ^d` for all separations
`d`.  This is the "clustering on the whole window" datum — the strong side will
inhabit it from the proved uniform-in-coupling bound. -/
structure CouplingWindow (p : zChain.toLattice.Plaquette) : Type where
  /-- Lower endpoint of the coupling window. -/
  lo : Q'
  /-- Upper endpoint of the coupling window. -/
  hi : Q'
  /-- The window is a genuine non-degenerate interval. -/
  lo_le_hi : lo ≤ hi
  /-- **The clustering / located-gap witness on the window.**  For every weight
  `w` in `[lo, hi]` there is a rate `ρ < 1` with geometric cluster decay
  `clusterSpanSum (…) w gr d ≤ 2·ρ^d` for all `d`. -/
  gap : ∀ w : Q', lo ≤ w → w ≤ hi →
    Σ' ρ : Q', (ρ < (1 : Q')) ∧
      (∀ d : Nat, clusterSpanSum (zChainClusterCountBound p) w gr d
        ≤ Q'.ofNat 2 * ρ ^ d)

/-- **`strongWindow` — the PROVED strong window `[0, 1/6]`.**

The strong-coupling window with `lo = 0`, `hi = w₀ = 1/6`.  The `gap` field is
GENUINELY DISCHARGED from the proved `UniformCouplingGap` theorems: at each `w`
in `[0, 1/6]` the rate is `ρ = uniformRho p w`, which is `< 1` by
`uniform_rho_le_endpoint` (`ρ ≤ mayerRho p = 4/9 < 1`) and yields the geometric
cluster decay by `uniform_cluster_decay`.  This is the genuine proved strong
side — NOT a posited window. -/
def strongWindow (p : zChain.toLattice.Plaquette) : CouplingWindow p where
  lo := 0
  hi := w0
  lo_le_hi := Q'.le_of_lt w0_pos
  gap := fun w hlo hhi =>
    ⟨ uniformRho p w
    , -- ρ_w ≤ mayerRho p = 4/9 < 1
      Q'.lt_of_le_of_lt (uniform_rho_le_endpoint p hlo hhi) (mayerRho_lt_one p)
    , -- the genuine uniform-in-coupling cluster decay
      fun d => uniform_cluster_decay p hlo hhi d ⟩

/-- The strong window's lower endpoint is `0` (definitional — used by the
coverage assembly). -/
theorem strongWindow_lo (p : zChain.toLattice.Plaquette) :
    (strongWindow p).lo = 0 := rfl

/-- The strong window's upper endpoint is `w₀ = 1/6` (definitional). -/
theorem strongWindow_hi (p : zChain.toLattice.Plaquette) :
    (strongWindow p).hi = w0 := rfl

/-! ## DELIVERABLE 2 — the weak window as a NAMED obligation (uninhabited)

A `WeakWindow` is the SAME shape as `CouplingWindow` but for the weak interval
`[w_w, 1]`: a clustering / located-gap bound for every weight in the weak
interval.  NO inhabitant is provided — weak-coupling clustering reaching down to
a `w_w` that meets the strong window is exactly the open continuum problem. -/

/-- **`WeakWindow` — the NAMED OPEN weak-coupling window (`Type`-level data).**

The weak-coupling analogue of `CouplingWindow` for the interval `[lo, hi]` (the
weak window, with `hi = 1`).  An inhabitant supplies, for every weight `w` in
`[lo, hi]`, a clustering rate `ρ < 1` and the geometric cluster decay
`clusterSpanSum (zChainClusterCountBound p) w gr d ≤ 2·ρ^d`.

NO inhabitant is constructed: weak-coupling exponential clustering is the open
continuum problem, and a `WeakWindow` whose `lo` reaches DOWN to the strong
window (`lo ≤ 1/6`) is the "middle" that is not known. -/
structure WeakWindow (p : zChain.toLattice.Plaquette) : Type where
  /-- Lower endpoint of the weak window `w_w`. -/
  lo : Q'
  /-- Upper endpoint of the weak window (`= 1`). -/
  hi : Q'
  /-- The weak window is a genuine non-degenerate interval. -/
  lo_le_hi : lo ≤ hi
  /-- **THE OPEN CONTENT — weak-coupling clustering on the weak window.**  For
  every weight `w` in `[lo, hi]` there is a rate `ρ < 1` with geometric cluster
  decay `clusterSpanSum (…) w gr d ≤ 2·ρ^d` for all `d`. -/
  gap : ∀ w : Q', lo ≤ w → w ≤ hi →
    Σ' ρ : Q', (ρ < (1 : Q')) ∧
      (∀ d : Nat, clusterSpanSum (zChainClusterCountBound p) w gr d
        ≤ Q'.ofNat 2 * ρ ^ d)

/-- **`weakWindow_gap_rate` — a `WeakWindow` yields, at each weak weight, a
clustering rate `< 1` and the geometric decay.**  This is the projection of the
`gap` field: GIVEN a `WeakWindow` (the open obligation), at every `w` in
`[W.lo, W.hi]` the weak-coupling located-gap rate is available.  It CONSUMES the
`WeakWindow`; no unconditional rate is produced. -/
def weakWindow_gap_rate {p : zChain.toLattice.Plaquette} (W : WeakWindow p)
    (w : Q') (hlo : W.lo ≤ w) (hhi : w ≤ W.hi) :
    Σ' ρ : Q', (ρ < (1 : Q')) ∧
      (∀ d : Nat, clusterSpanSum (zChainClusterCountBound p) w gr d
        ≤ Q'.ofNat 2 * ρ ^ d) :=
  W.gap w hlo hhi

/-! ## DELIVERABLE 3 — overlap + coverage (the PROVED assembly)

`WindowOverlap` is the real `≤` `Prop` `w_w ≤ w₀` (the weak window touches /
overlaps the strong window).  `twoSided_covers` proves that, given overlap, the
two windows cover the whole coupling line `[0, 1]`.  `twoSided_gap_all_couplings`
then produces a clustering / located-gap bound at every coupling — STRONG branch
proved, WEAK branch consuming only the `WeakWindow`. -/

/-- **`WindowOverlap` — the "middle" wall as a real `≤` `Prop`.**

`weak.lo ≤ strong.hi` (`w_w ≤ w₀`): the weak window reaches DOWN to meet the
strong window.  This is a genuine inequality on `Q'` (NOT `True`); it asserts the
weak control extends down to the strong window — the intermediate "middle".  No
unconditional proof is given (no weak window with `w_w ≤ 1/6 = w₀` is known). -/
def WindowOverlap {p : zChain.toLattice.Plaquette}
    (strong : CouplingWindow p) (weak : WeakWindow p) : Prop :=
  weak.lo ≤ strong.hi

/-- **`twoSided_covers` — the coverage (PROVED interval arithmetic).**

Given the overlap `w_w ≤ w₀` (and the strong window pinned at `lo = 0`, the weak
window at `hi = 1`), every weight `w` in `[0, 1]` lies in the strong window
(`w ≤ strong.hi`) OR the weak window (`weak.lo ≤ w`).

PROOF.  Real case-split on the decidable comparison `w ≤ strong.hi`.  If it
holds, `w` is in the strong window (left).  Otherwise `strong.hi ≤ w`
(`Q'.le_of_not_le'`), and combined with the overlap `weak.lo ≤ strong.hi` by
transitivity `weak.lo ≤ w` — `w` is in the weak window (right).  Genuine
interval content, not trivial. -/
theorem twoSided_covers {p : zChain.toLattice.Plaquette}
    (strong : CouplingWindow p) (weak : WeakWindow p)
    (ov : WindowOverlap strong weak)
    (hstrong_lo : strong.lo = 0) (hweak_hi : weak.hi = 1) :
    ∀ w : Q', (0 : Q') ≤ w → w ≤ (1 : Q') →
      (w ≤ strong.hi ∨ weak.lo ≤ w) := by
  intro w _hw0 _hw1
  by_cases h : w ≤ strong.hi
  · exact Or.inl h
  · -- ¬ (w ≤ strong.hi) ⇒ strong.hi ≤ w; with overlap weak.lo ≤ strong.hi ≤ w.
    have hge : strong.hi ≤ w := Q'.le_of_not_le' h
    exact Or.inr (Q'.le_trans' weak.lo strong.hi w ov hge)

/-- **`twoSided_gap_all_couplings` — the all-coupling clustering/located-gap
bound (PROVED conditional, honest).**

For the proved `strongWindow p` and ANY supplied `weak : WeakWindow p` with the
overlap `WindowOverlap (strongWindow p) weak` and the weak window pinned at
`hi = 1`, EVERY weight `w` in `[0, 1]` carries a clustering / located-gap datum:
a rate `ρ < 1` with geometric cluster decay
`clusterSpanSum (zChainClusterCountBound p) w gr d ≤ 2·ρ^d`.

PROOF.  Coverage (`twoSided_covers`) splits `w` into the strong window
(`w ≤ 1/6`) or the weak window (`weak.lo ≤ w`).
  * STRONG branch — FULLY PROVED: the rate / decay is `(strongWindow p).gap`,
    discharged from the genuine `uniform_*` bound.
  * WEAK branch — consumes ONLY `weak.gap` (the named uninhabited obligation),
    needing `w ≤ weak.hi = 1` from the hypothesis `w ≤ 1`.

Hence the all-coupling gap is CONDITIONAL ONLY on the (uninhabited) `WeakWindow`
plus the `WindowOverlap` — the conditionality is explicit and honest.  No
positivity is faked; the weak branch produces nothing unconditionally. -/
def twoSided_gap_all_couplings (p : zChain.toLattice.Plaquette)
    (weak : WeakWindow p)
    (ov : WindowOverlap (strongWindow p) weak)
    (hweak_hi : weak.hi = 1) :
    ∀ w : Q', (0 : Q') ≤ w → w ≤ (1 : Q') →
      Σ' ρ : Q', (ρ < (1 : Q')) ∧
        (∀ d : Nat, clusterSpanSum (zChainClusterCountBound p) w gr d
          ≤ Q'.ofNat 2 * ρ ^ d) := by
  intro w hw0 hw1
  -- Decidable case-split on `w ≤ strongWindow.hi` (data-level, into `Type`); the
  -- Prop-level coverage `twoSided_covers` is the same case-split phrased as `∨`.
  by_cases hstrong : w ≤ (strongWindow p).hi
  · -- STRONG branch — fully proved from the discharged strongWindow.gap.
    --   strongWindow.lo = 0 ≤ w (from hw0), and w ≤ strongWindow.hi.
    exact (strongWindow p).gap w hw0 hstrong
  · -- WEAK branch — consumes only the WeakWindow obligation.
    --   ¬ (w ≤ strongWindow.hi) ⇒ strongWindow.hi ≤ w; with overlap
    --   weak.lo ≤ strongWindow.hi ≤ w, and w ≤ 1 = weak.hi.
    have hge : (strongWindow p).hi ≤ w := Q'.le_of_not_le' hstrong
    have hweak : weak.lo ≤ w := Q'.le_trans' weak.lo (strongWindow p).hi w ov hge
    have hwle : w ≤ weak.hi := by rw [hweak_hi]; exact hw1
    exact weak.gap w hweak hwle

/-! ## DELIVERABLE 4 — tie to the continuum + the RG-landing bridge

The continuum limit (`a → 0`) is approached at the WEAK end (`w → 1`).  A
`WeakWindow`'s clustering at the weak weights is exactly the datum that
`WeakCouplingGap.RGClusteringTransport` would supply from the proved strong side
through the middle.  We expose that bridge WITHOUT inhabiting anything:

  * `weakWindow_yields_bound` — a `WeakWindow` (at a fixed weak weight with a
    `SpectralModel` and side conditions) IS a `WeakCouplingGap.WeakClusteringBound`-
    shaped datum, hence (by the proved `weakSpectralGap`) a located weak gap;
  * `weakWindow_landing` — the weak end of the all-coupling gap, made
    dimensionless, lands on the `RGLandingCertificate` shape (the proved
    `weakGap_landing`, conditional on the unchanged open scale normalization).

These are SHAPE-level bridges; the `WeakWindow`, `WindowOverlap`,
`RGClusteringTransport`, and `RGLandingInput` all remain uninhabited / open. -/

/-- **`weakWindow_yields_bound` — the weak window IS the transport datum
(shape-level bridge).**

A `WeakCouplingGap.WeakClusteringBound` (a `SpectralModel` at weak coupling with
a clustering envelope `μ < 1` and the converse's side conditions) produces, by
the PROVED `weakSpectralGap`, a located weak-coupling spectral gap.  A
`WeakWindow` is the coupling-INTERVAL form of the same open weak-clustering
content; this `def` records that GIVEN a `WeakClusteringBound` the located weak
gap exists — wiring the weak window to the existing weak-gap engine.  It
CONSUMES a `WeakClusteringBound`; nothing is inhabited here. -/
def weakWindow_yields_bound (Wb : WeakClusteringBound) :
    LocatedSpectralGap Wb.S :=
  weakSpectralGap Wb

/-- **`weakWindow_transport` — the middle as `RGClusteringTransport`.**

`RGClusteringTransport` (the open middle wall) is exactly the statement that the
proved strong-coupling clustering is carried through the middle to a weak-coupling
clustering datum.  GIVEN it, a located weak gap exists (`weakGap_of_transport`).
This is the "both sides meet" chain at the spectral-model level; `WindowOverlap`
is the interval-arithmetic shadow of the SAME middle obligation.  No inhabitant
of `RGClusteringTransport` is provided. -/
theorem weakWindow_transport (h : RGClusteringTransport) :
    Nonempty (Σ Wb : WeakClusteringBound, LocatedSpectralGap Wb.S) :=
  weakGap_of_transport h

/-- **`weakWindow_landing` — the continuum (weak-end) landing tie (PROVED
conditional).**

The continuum limit is approached at the weak end (`w → 1`); the all-coupling
gap's weak end, made dimensionless against the dynamically-generated scale, is
the `RGLandingCertificate` target.  GIVEN the open scale normalization
`RGLandingInput D`, the dimensionless landing certificate follows by the proved
`weakGap_landing`.  This places the two-sided program's weak end on the SAME
dimensionless landing target as the rest of the program; the scale normalization
stays open. -/
def weakWindow_landing
    (D : ContinuumClosureProgram.DefectGapRecursion)
    (h : RGLandingCertificate.RGLandingInput D) :
    RGLandingCertificate.RGLandingCertificate :=
  weakGap_landing D h

/-! ## Documentation: PROVED, named-open, and the scope (AGENTS.md Rule 6)

PROVED in this module (axiom-clean, `[propext]` / `[propext, Quot.sound]`):

  * `CouplingWindow` — the first-class clustering/gap window;
  * `strongWindow` (with `strongWindow_lo`, `strongWindow_hi`) — the PROVED
    strong window `[0, 1/6]`, its `gap` field DISCHARGED from the genuine
    `uniform_rho_le_endpoint` (`ρ_w ≤ 4/9 < 1`) and `uniform_cluster_decay` (the
    real uniform-in-coupling clustering on the whole interval);
  * `WindowOverlap` — the real `≤` `Prop` `w_w ≤ w₀`;
  * `twoSided_covers` — the coverage `[0,1] ⊆ strong ∪ weak` given overlap (a
    genuine interval case-split, not trivial);
  * `twoSided_gap_all_couplings` — the all-coupling clustering/located-gap bound,
    STRONG branch fully proved, WEAK branch consuming only the `WeakWindow`;
  * `weakWindow_gap_rate`, `weakWindow_yields_bound`, `weakWindow_transport`,
    `weakWindow_landing` — the bridges to the weak-gap engine and the RG landing.

NAMED-open (NOT faked — the continuum problem):

  * `WeakWindow` — weak-coupling clustering on `[w_w, 1]` (NO inhabitant);
  * `WindowOverlap` — `w_w ≤ 1/6` (the "middle": no weak window reaching down to
    the strong window is known — the middle wall);
  * (downstream) `RGClusteringTransport`, `RGLandingCertificate.RGLandingInput` —
    the RG-flow preservation through the middle and the continuum-scale
    normalization, unchanged and open.

SCOPE (underclaim).  The STRONG window `[0, 1/6]` is GENUINELY PROVED
(uniform-in-coupling clustering on the whole interval, resting on the real
`|enumPolys|` lattice-animal count).  The all-coupling — and hence continuum —
gap is REDUCED to the two named uninhabited obligations `WeakWindow` (weak-
coupling clustering) and `WindowOverlap` (the weak control reaching DOWN to
`w_w ≤ 1/6` to meet the strong window).  NO unconditional all-coupling gap is
claimed; NO 4D Yang–Mills mass gap is claimed; NO positivity is faked.  Both
walls are genuinely uninhabited. -/

end YMGap.Continuum.TwoSidedGap

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.TwoSidedGap.strongWindow
#print axioms YMGap.Continuum.TwoSidedGap.strongWindow_lo
#print axioms YMGap.Continuum.TwoSidedGap.strongWindow_hi
#print axioms YMGap.Continuum.TwoSidedGap.weakWindow_gap_rate
#print axioms YMGap.Continuum.TwoSidedGap.twoSided_covers
#print axioms YMGap.Continuum.TwoSidedGap.twoSided_gap_all_couplings
#print axioms YMGap.Continuum.TwoSidedGap.weakWindow_yields_bound
#print axioms YMGap.Continuum.TwoSidedGap.weakWindow_transport
#print axioms YMGap.Continuum.TwoSidedGap.weakWindow_landing
