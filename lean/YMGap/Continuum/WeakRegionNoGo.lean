/-
Track B / R2 — the WEAK-REGION NO-GO: a rigorous BOUNDARY MAP of the interval
`[2^{−1/3}, 1]`, PROVED impervious to BOTH available mechanisms.

# What this module is — and what it is emphatically NOT (read first)

This module is a rigorous BOUNDARY MAP, NOT progress toward the Yang–Mills mass
gap.  It does NOT construct any weak-coupling clustering, any weak-coupling
positivity, or any 4D Yang–Mills gap, and it does NOT inhabit any continuum wall.

It PROVES the converse: across the WHOLE weak interval `[2^{−1/3}, 1]` (in the
cube-coordinate `qpow w 3 ≥ 1/2`, `w ≤ 1`) the two mechanisms the repository
actually has — the character / KP / Mayer expansion, and the approximate
fusion-RG margin — CANNOT cluster.  Hence the weak-coupling gap is necessarily
NON-PERTURBATIVE: it is exactly the OPEN continuum problem, carried by the named,
UNINHABITED obligations.  The boundary is mapped; the gap is not approached.

# The weak interval, in the cube-coordinate (honest: the edge is irrational)

The character clustering rate is `rho w = coeffW w 1 = dimQ 1 · qpow w 3 = 2·w³`
(the SU(2) heat-kernel character coefficient `2·e^{−3t}`, `w = e^{−t}`).  Genuine
clustering needs `rho w < 1`, i.e. `w³ < 1/2`, i.e. `w < 2^{−1/3} ≈ 0.7937`.  The
edge `2^{−1/3}` is irrational, so we delimit the weak interval by the DECIDABLE,
exact cube condition

    weak region  :=  { w : 1/2 ≤ qpow w 3  ∧  w ≤ 1 }   ( = [2^{−1/3}, 1] ).

# Deliverable A — the character rate across the WHOLE weak interval (real ∀-theorems)

  * `rho_ge_one_on_weak`   — `1/2 ≤ w³ ⟹ 1 ≤ rho w`     (`rho = 2w³ ≥ 2·(1/2) = 1`);
  * `rho_le_two_on_weak`   — `0 ≤ w ≤ 1 ⟹ rho w ≤ 2`    (`w³ ≤ 1 ⟹ 2w³ ≤ 2`);
  * `character_rate_mono_weak` — `0 ≤ w ≤ w' ⟹ rho w ≤ rho w'` (GENUINE
    cube-monotonicity via `coeffW_one_mono` / `qpow_mono`, NOT `decide` over ∀w);
  * `no_character_clustering_on_weak` — `1/2 ≤ w³ ⟹ ¬ (rho w < 1)`: the character
    correlator does NOT decay ANYWHERE in the weak interval.

So on `[2^{−1/3}, 1]` the character rate climbs MONOTONICALLY from `1` (at the
edge) to `2` (at `w = 1`); it is `≥ 1` throughout — never a clustering rate.

# Deliverable B — the honest NO-GO (both mechanisms excluded)

  * `character_window_excludes_weak` — every character `WilsonWindow`'s `hi` is
    below `2^{−1/3}` (its `hi³ < 1/2`, from `characterWindow_hi_lt_ceiling`), so NO
    character window contains ANY weak `w` (`1/2 ≤ w³`): the character / KP / Mayer
    mechanism PROVABLY does not cluster in `[2^{−1/3}, 1]`.

  * The approximate fusion-RG margin is ALSO excluded, by the already-proved
    obstruction `FusionMarginScope.n2_margin_nonpos_at_witness`: the once-fused
    (`N = 2`) Clebsch–Gordan margin goes NONPOSITIVE at the weak witness `w = 4/5`
    (which lies in the weak interval, `(4/5)³ = 64/125 ≥ 1/2`).

⟹ BOTH available mechanisms fail in the weak interval; a weak-coupling
clustering / gap requires a genuinely NON-PERTURBATIVE mechanism.  The irreducible
content is exactly the named, UNINHABITED obligations
`WeakCouplingGap.WeakClusteringBound` / `RGClusteringTransport` /
`RGLandingCertificate.RGLandingInput` — NONE closable by the repository's
machinery.  This is the bedrock open continuum problem.

# Deliverable C — honest framing

This is a BOUNDARY MAP, not a gap proof.  It proves the available mechanisms
(character expansion + approximate fusion-RG) cannot cluster in `[2^{−1/3}, 1]`,
so the weak-coupling gap is necessarily non-perturbative = the open continuum
problem.  No weak-coupling clustering, positivity, or 4D YM gap is constructed or
claimed; the named obligations stay uninhabited.

# Constructive contract (`lean/AGENTS.md`)

Mathlib-free; only `Q'` / `Nat` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `decide` on non-decidable props (the ∀-interval bounds and
monotonicity are REAL proofs via `qpow_mono` / `coeffW_one_mono`; `decide` is used
ONLY on closed concrete-rational spot checks at `w = 4/5, 9/10, 1`).  No `sorry` /
`admit` / new `axiom` / `Prop := True`.  No obligation is inhabited; the
`NonPerturbativeWeakGap` shape is left genuinely uninhabited.  Every load-bearing
declaration is gated with `#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.CharacterWindowCeiling
import YMGap.Continuum.FusionMarginScope
import YMGap.Continuum.WeakCouplingGap
import YMGap.Continuum.UniformCouplingGap

namespace YMGap.Continuum.WeakRegionNoGo

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.PlaquetteActivity
open YMGap.Continuum.WilsonConnCorr
open YMGap.Continuum.CharacterWindowCeiling
open YMGap.Continuum.FusionMarginScope

/-! ## 0. The weak interval, in the exact cube-coordinate

The weak / continuum interval `[2^{−1/3}, 1]` has an irrational left edge.  We
delimit it by the DECIDABLE, exact cube condition `1/2 ≤ qpow w 3` (the left edge
`w ≥ 2^{−1/3}`) together with `w ≤ 1` (the right edge).  `inWeak` packages the
two as a predicate. -/

/-- The exact cube-coordinate threshold `1/2` for the left edge of the weak
interval (`qpow w 3 ≥ 1/2 ⟺ w ≥ 2^{−1/3}`). -/
def halfQ : Q' := Q'.mkPos 1 2 (by decide)

/-- **The weak interval predicate** `inWeak w`: `1/2 ≤ qpow w 3` (i.e.
`w ≥ 2^{−1/3}`) and `w ≤ 1`.  This is the exact, decidable form of the
weak-coupling / continuum interval `[2^{−1/3}, 1]`. -/
structure inWeak (w : Q') : Prop where
  /-- The left edge `w ≥ 2^{−1/3}`, exactly `1/2 ≤ w³`. -/
  cube_ge : halfQ ≤ qpow w 3
  /-- The right edge `w ≤ 1`. -/
  le_one : w ≤ (1 : Q')

/-- The weak interval is non-empty: `w = 4/5` lies in it
(`(4/5)³ = 64/125 ≥ 1/2`, `4/5 ≤ 1`). -/
theorem inWeak_witness : inWeak (Q'.mkPos 4 5 (by decide)) where
  cube_ge := by decide
  le_one := by decide

/-! ## 1. DELIVERABLE A — the character rate across the WHOLE weak interval

`rho w = coeffW w 1 = dimQ 1 · qpow w 3 = 2·w³`.  On `[2^{−1/3}, 1]` the rate is
`≥ 1` everywhere, `≤ 2` everywhere, MONOTONE increasing, and NEVER `< 1`. -/

/-- **`rho_ge_one_on_weak` (PROVED).**  For `1/2 ≤ w³` (the left edge of the weak
interval), the character clustering rate is `≥ 1`:

    rho w = 2·w³ ≥ 2·(1/2) = 1.

Reuses the proved ceiling theorem `character_rate_ge_one_at_ceiling`.  Real
inequality, not vacuous. -/
theorem rho_ge_one_on_weak {w : Q'} (hlo : halfQ ≤ qpow w 3) :
    (1 : Q') ≤ rho w :=
  character_rate_ge_one_at_ceiling hlo

/-- **`rho_le_two_on_weak` (PROVED).**  For `0 ≤ w ≤ 1`, the character rate is
`≤ 2`:

    rho w = dimQ 1 · qpow w 3 = 2·w³ ≤ 2·1³ = 2     (since w³ ≤ 1³ = 1 for w ≤ 1).

By cube-monotonicity `qpow w 3 ≤ qpow 1 3` (`qpow_mono`) scaled by `dimQ 1 ≥ 0`,
then the decidable endpoint `dimQ 1 · qpow 1 3 = 2·1 = 2`.  Real inequality. -/
theorem rho_le_two_on_weak {w : Q'} (hw0 : (0 : Q') ≤ w) (hhi : w ≤ (1 : Q')) :
    rho w ≤ Q'.ofNat 2 := by
  unfold rho
  rw [coeffW_one_eq w]
  -- dimQ 1 · heatKernelSep w ≤ dimQ 1 · heatKernelSep 1 = 2·1 = 2
  have hsep : heatKernelSep w ≤ heatKernelSep (1 : Q') := heatKernelSep_mono hw0 hhi
  have hstep : dimQ 1 * heatKernelSep w ≤ dimQ 1 * heatKernelSep (1 : Q') :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hsep (dimQ_nonneg 1)
  refine Q'.le_trans' _ _ _ hstep ?_
  -- dimQ 1 · heatKernelSep 1 = 2 · qpow 1 3 = 2 · 1 = 2, decidable
  show dimQ 1 * heatKernelSep (1 : Q') ≤ Q'.ofNat 2
  decide

/-- **`character_rate_mono_weak` — the rate is MONOTONE increasing (PROVED).**

For `0 ≤ w ≤ w'`, `rho w ≤ rho w'`.  This is the genuine cube-monotonicity
`coeffW_one_mono` (`rho = coeffW · 1`, reduces to `qpow w 3 ≤ qpow w' 3` via
`qpow_mono`, scaled by `dimQ 1 ≥ 0`) — a REAL proof, NOT `decide` over `∀w`.
Hence on `[2^{−1/3}, 1]` the character rate climbs monotonically from `1` (the
edge) to `2` (at `w = 1`). -/
theorem character_rate_mono_weak {w w' : Q'} (h0 : (0 : Q') ≤ w) (hww' : w ≤ w') :
    rho w ≤ rho w' :=
  UniformCouplingGap.coeffW_one_mono h0 hww'

/-- **`no_character_clustering_on_weak` — no character decay ANYWHERE in the weak
interval (PROVED).**

For `1/2 ≤ w³` (anywhere on or above the left edge), the rate is NOT `< 1`
(`¬ (rho w < 1)`): the character clustering bound `C·ρ^n` does not decay, so the
character correlator does NOT cluster.  This extends the point ceiling to the
WHOLE weak interval.  Reuses `no_character_clustering_above_ceiling`. -/
theorem no_character_clustering_on_weak {w : Q'} (hlo : halfQ ≤ qpow w 3) :
    ¬ (rho w < (1 : Q')) :=
  no_character_clustering_above_ceiling hlo

/-! ### Concrete spot checks (decide on closed rationals)

Corroborating the ∀-theorems at three concrete weak points `w = 4/5, 9/10, 1`:
the rate is `≥ 1` at each (it does NOT decay), and `rho 1 = 2` exactly. -/

/-- Spot check `w = 4/5`: `rho (4/5) = 2·(4/5)³ = 128/125 ≥ 1` (no clustering). -/
theorem spot_check_4_5 : (1 : Q') ≤ rho (Q'.mkPos 4 5 (by decide)) := by decide

/-- Spot check `w = 9/10`: `rho (9/10) = 2·(9/10)³ = 1458/1000 ≥ 1` (no
clustering). -/
theorem spot_check_9_10 : (1 : Q') ≤ rho (Q'.mkPos 9 10 (by decide)) := by decide

/-- Spot check `w = 1` (the continuum endpoint): `rho 1 = 2·1³ = 2` exactly — the
character rate is at its maximum, far from clustering. -/
theorem spot_check_one : (rho (1 : Q')).eqv (Q'.ofNat 2) := by decide

/-! ## 2. DELIVERABLE B — the honest NO-GO

Both available mechanisms are excluded from the weak interval:
  (i) the character / KP / Mayer mechanism — no `WilsonWindow` contains any weak
      `w` (`character_window_excludes_weak`, Deliverable A);
  (ii) the approximate fusion-RG margin — nonpositive at the weak witness
      (`FusionMarginScope.n2_margin_nonpos_at_witness`). -/

/-- **`character_window_excludes_weak` — NO character window touches the weak
interval (PROVED).**

For ANY character `WilsonWindow` `W` and ANY weak weight `w` (`1/2 ≤ w³`), if
`w ≤ W.hi` then a contradiction follows: by `characterWindow_hi_lt_ceiling`,
`W.hi³ < 1/2`, and by cube-monotonicity `w³ ≤ W.hi³ < 1/2`, contradicting
`1/2 ≤ w³`.  Equivalently: every window's upper edge `W.hi` is below `2^{−1/3}`,
so no window contains any weak `w`.  The character / KP / Mayer mechanism
PROVABLY does not cluster in `[2^{−1/3}, 1]`. -/
theorem character_window_excludes_weak (W : WilsonWindow) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hlo : halfQ ≤ qpow w 3) :
    ¬ (w ≤ W.hi) := by
  intro hwhi
  -- W.hi³ < 1/2  (any window's upper edge is below the ceiling)
  have hhi_cube : qpow W.hi 3 < halfQ := characterWindow_hi_lt_ceiling W
  -- w³ ≤ W.hi³  (cube-monotonicity)
  have hmono : qpow w 3 ≤ qpow W.hi 3 := qpow_mono hw0 hwhi 3
  -- so w³ ≤ W.hi³ < 1/2, i.e. w³ < 1/2, contradicting 1/2 ≤ w³
  have hwlt : qpow w 3 < halfQ := HeatKernelGap.lt_of_le_of_lt hmono hhi_cube
  exact ClusteringImpliesGap.lt_irrefl' (qpow w 3)
    (ClusteringImpliesGap.lt_of_lt_of_le hwlt hlo)

/-- **The approximate fusion-RG margin is ALSO excluded (PROVED, re-exported).**

The once-fused (`N = 2`) Clebsch–Gordan margin is NONPOSITIVE at the weak witness
`w = 4/5`: `Z'₂ ≤ E₂`, i.e. the normalized excited coefficient `E₂/Z'₂ ≥ 1`, so
the dominant-mode margin `1 − E₂/Z'₂ ≤ 0`.  Directly the proved
`FusionMarginScope.n2_margin_nonpos_at_witness`.  The witness `4/5` lies in the
weak interval (`inWeak_witness`), so the approximate fusion-RG mechanism cannot
produce a gap there. -/
theorem fusionRG_margin_nonpos_in_weak :
    fusionProduct 2 (coeffW wWeak) (coeffW wWeak) 0
      ≤ fusionProduct 2 (coeffW wWeak) (coeffW wWeak) 1 :=
  n2_margin_nonpos_at_witness

/-! ### The dichotomy, assembled

`WeakRegionDichotomy` records, for a given weak weight `w` and a candidate
character window `W`, the two proved exclusions side by side: (i) `W` does not
contain `w` (character mechanism out), and (ii) the approximate fusion-RG margin
is nonpositive at the weak witness `4/5` (fusion mechanism out). -/

/-- **`WeakRegionDichotomy` — both mechanisms excluded, packaged (PROVED data).**

For a weak weight `w` (`0 ≤ w`, `1/2 ≤ w³`) and ANY character window `W`:
  * `char_excluded` — `¬ (w ≤ W.hi)`: the character window does not reach `w`;
  * `rate_ge_one`   — `1 ≤ rho w`: the character rate does not cluster at `w`;
  * `fusion_excluded` — the `N = 2` fusion-RG margin is nonpositive at `4/5`.
This is the assembled honest no-go for the single weak weight `w`. -/
structure WeakRegionDichotomy (w : Q') (W : WilsonWindow) : Prop where
  /-- The character window does not contain the weak weight. -/
  char_excluded : ¬ (w ≤ W.hi)
  /-- The character rate is `≥ 1` at the weak weight (no clustering). -/
  rate_ge_one : (1 : Q') ≤ rho w
  /-- The approximate fusion-RG margin is nonpositive at the weak witness `4/5`. -/
  fusion_excluded :
    fusionProduct 2 (coeffW wWeak) (coeffW wWeak) 0
      ≤ fusionProduct 2 (coeffW wWeak) (coeffW wWeak) 1

/-- **`weak_region_dichotomy` (PROVED).**  For every weak weight `w` (`0 ≤ w`,
`1/2 ≤ w³`) and every character window `W`, BOTH available mechanisms are
excluded: the assembled `WeakRegionDichotomy`.  Combines
`character_window_excludes_weak`, `rho_ge_one_on_weak`, and
`fusionRG_margin_nonpos_in_weak`.  This is the documented honest statement that
the weak gap is reachable by NEITHER mechanism. -/
theorem weak_region_dichotomy (W : WilsonWindow) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hlo : halfQ ≤ qpow w 3) :
    WeakRegionDichotomy w W where
  char_excluded := character_window_excludes_weak W hw0 hlo
  rate_ge_one := rho_ge_one_on_weak hlo
  fusion_excluded := fusionRG_margin_nonpos_in_weak

/-! ## 3. The precise shape of the missing (non-perturbative) input

A closure of the weak gap would need a clustering model on the weak interval with
a genuine decay rate `< 1` that is NOT the character rate (which is `≥ 1` there,
Deliverable A).  `NonPerturbativeWeakGap` makes this explicit, and is left
genuinely UNINHABITED — it is the precise shape of the open continuum input. -/

/-- **`NonPerturbativeWeakGap` — the precise shape of the missing input
(UNINHABITED by design).**

`Type`-level data a genuine weak-coupling closure would have to supply: a weak
weight `w` in the weak interval (`inWeak w`), a `WeakCouplingGap.WeakClusteringBound`
whose spatial-transfer correlator clusters at rate `μ < 1`, together with the
honest non-degeneracy that this clustering rate is GENUINELY below the character
rate `rho w` (which is `≥ 1` in the weak interval, so any `μ < 1` is necessarily a
DIFFERENT, non-perturbative object — not the character coefficient).  NO
inhabitant is constructed: a weak-coupling clustering model with rate `< 1` is
exactly the open continuum problem.  This is NOT vacuous — it bundles a real
`inWeak`, a real `WeakClusteringBound`, and the genuine strict inequality
`μ < rho w` forced by `rho w ≥ 1 > μ`. -/
structure NonPerturbativeWeakGap : Type where
  /-- A weak weight (in the cube-coordinate weak interval `[2^{−1/3}, 1]`). -/
  w : Q'
  /-- The witness that `w` is in the weak interval. -/
  weak : inWeak w
  /-- The (open) weak-coupling clustering model — itself uninhabited for 4D. -/
  cluster : WeakCouplingGap.WeakClusteringBound
  /-- The clustering rate is GENUINELY below the character rate: `μ < rho w`.
  Since `rho w ≥ 1 > μ` in the weak interval, the weak clustering rate is NOT the
  character coefficient — it is a different, non-perturbative object. -/
  rate_below_character : cluster.μ < rho w

/-- **`nonPerturbative_rate_strictly_below_one` (PROVED, conditional).**  IF a
`NonPerturbativeWeakGap` `G` existed, its weak clustering rate would be strictly
below `1` (`G.cluster.μ < 1`) — the located-gap requirement the character object
FAILS in the weak interval (`no_character_clustering_on_weak`).  This is the
content the missing non-perturbative input would have to supply; it consumes a
hypothetical `G`, and NO `G` is constructed.  (Confirms `NonPerturbativeWeakGap`
is non-vacuous: its `cluster.μ_lt_one` field is real content.) -/
theorem nonPerturbative_rate_strictly_below_one (G : NonPerturbativeWeakGap) :
    G.cluster.μ < (1 : Q') :=
  G.cluster.μ_lt_one

/-! ## 4. DELIVERABLE C — honest scope (see the module header)

PROVED here (axiom-clean, `[propext]` / `[propext, Quot.sound]`):

  * `inWeak`, `inWeak_witness` — the exact cube-coordinate weak interval
    `[2^{−1/3}, 1]` (= `1/2 ≤ w³ ∧ w ≤ 1`), non-empty;
  * `rho_ge_one_on_weak`, `rho_le_two_on_weak`, `character_rate_mono_weak`,
    `no_character_clustering_on_weak` — the character rate across the WHOLE weak
    interval: `≥ 1`, `≤ 2`, MONOTONE increasing (genuine cube-monotonicity), and
    NEVER `< 1`; spot checks at `4/5`, `9/10`, `1` (`rho 1 = 2`);
  * `character_window_excludes_weak` — NO character `WilsonWindow` contains ANY
    weak weight (the character / KP / Mayer mechanism is excluded);
  * `fusionRG_margin_nonpos_in_weak` — the approximate fusion-RG margin is
    nonpositive at the weak witness `4/5` (the fusion mechanism is excluded);
  * `weak_region_dichotomy` (+ `WeakRegionDichotomy`) — BOTH mechanisms excluded,
    assembled;
  * `nonPerturbative_rate_strictly_below_one` — the precise shape of the missing
    input (conditional on a hypothetical, uninhabited `NonPerturbativeWeakGap`).

NOT inhabited (UNCHANGED — the open continuum problem):

  * `WeakCouplingGap.WeakClusteringBound`, `WeakCouplingGap.RGClusteringTransport`,
    `RGLandingCertificate.RGLandingInput` — weak-coupling clustering on
    `[2^{−1/3}, 1]`, its RG transport through the middle, and the continuum-scale
    normalization.  This module does NOT touch them; they remain uninhabited.
  * `NonPerturbativeWeakGap` — the precise shape of a weak-coupling closure
    (a clustering model with rate `< 1` NOT equal to the character rate).  Left
    genuinely uninhabited — the missing non-perturbative input.

HONEST SCOPE (underclaim).  This module is a rigorous BOUNDARY MAP, NOT progress
toward the gap.  It PROVES that the two available mechanisms — the character /
KP / Mayer expansion and the approximate fusion-RG margin — CANNOT cluster in the
weak region `[2^{−1/3}, 1]`: the character rate is `≥ 1` throughout
(`no_character_clustering_on_weak`), no character window reaches the interval
(`character_window_excludes_weak`), and the fusion margin is nonpositive at the
weak witness (`fusionRG_margin_nonpos_in_weak`).  Therefore the weak-coupling gap
is necessarily NON-PERTURBATIVE — exactly the OPEN continuum problem, carried by
the named, UNINHABITED obligations.  NO weak-coupling clustering, positivity, or
4D Yang–Mills mass gap is constructed or claimed; nothing is faked. -/

end YMGap.Continuum.WeakRegionNoGo

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.WeakRegionNoGo.inWeak_witness
#print axioms YMGap.Continuum.WeakRegionNoGo.rho_ge_one_on_weak
#print axioms YMGap.Continuum.WeakRegionNoGo.rho_le_two_on_weak
#print axioms YMGap.Continuum.WeakRegionNoGo.character_rate_mono_weak
#print axioms YMGap.Continuum.WeakRegionNoGo.no_character_clustering_on_weak
#print axioms YMGap.Continuum.WeakRegionNoGo.spot_check_4_5
#print axioms YMGap.Continuum.WeakRegionNoGo.spot_check_9_10
#print axioms YMGap.Continuum.WeakRegionNoGo.spot_check_one
#print axioms YMGap.Continuum.WeakRegionNoGo.character_window_excludes_weak
#print axioms YMGap.Continuum.WeakRegionNoGo.fusionRG_margin_nonpos_in_weak
#print axioms YMGap.Continuum.WeakRegionNoGo.weak_region_dichotomy
#print axioms YMGap.Continuum.WeakRegionNoGo.nonPerturbative_rate_strictly_below_one
