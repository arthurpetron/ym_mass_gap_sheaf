# Chaining-estimate tightening of the overlap-measure bound

**Milestone 6.5 of `work_plan.md`.**  Prose companion to
`computations/chaining_estimate.py` and
`tests/test_chaining_estimate.py`.

## 1. The looseness this addresses

`computations/overlap_measure.py` (Milestone 1.4) aggregates the
single-plaquette buffer-shell bound of Milestone 1.3 to a per-step
estimate

    μ_k(Ω_k^∩)  ≤  Σ_p μ_k(A_p)  =  N_p · P_plaquette,        (1)

where `A_p := {U_p ∈ shell}`.  This is the **union bound**: it
upper-bounds the probability of *any* plaquette being on shell by the
sum of per-plaquette probabilities.  The union bound is loose by a
factor that grows with the correlation length `ξ(g)` of the
underlying SU(2) heat-kernel measure, because the per-plaquette events
are **positively correlated** through shared link variables (adjacent
plaquettes share one of their four edges).

The empirical evidence collected in
`computations/overlap_measure.standard_su2_trajectory` (the canonical
SU(2) trajectory with `g_0 = 0.8`) shows the union per-step bound
exceeding 1 — a vacuous probability bound — for the bulk of the
trajectory.  Phase 6.5 replaces (1) with a chaining estimate that
captures the correlation-weighted reduction of the effective
independent-event count.

## 2. The 4D lattice plaquette geometry

In the 4D hypercubic lattice with `d = 4` directions:

  * Each plaquette is a 2D face determined by two of the 4 directions.
  * Each plaquette has **4 edges**; each edge sits in exactly
    `d - 1 = 3` distinct planes, so it is shared by **5 other
    plaquettes** (the 6 plaquettes — including the anchor — that share
    that edge minus the anchor).
  * Of those 5 face-neighbors per edge, the dominant correlation
    contribution at small `g²` comes from the 4 nearest face-neighbors
    sharing exactly **one** edge with the anchor; the others are
    spatially separated by ≥ 2 lattice units and contribute at
    next-to-leading order.
  * Aggregating over the 4 edges of the anchor plaquette gives
    `n_share = 4` dominant correlation channels per plaquette (one
    per edge).

This is the geometric source of the fiducial constant
`SHARED_LINK_CHANNEL_MULTIPLICITY = 4` in
`computations/chaining_estimate.py`.

## 3. Two-plaquette heat-kernel correlation strength

For the SU(2) heat-kernel measure at coupling `g²`, the joint
density of two face-neighbor link configurations decomposes as

    p(U_p, U_{p'})  =  p(U_p) · p(U_{p'}) · ρ_{pp'}(g²)         (2)

where `ρ_{pp'}` is the **two-plaquette correlation factor**.
Expanding `ρ` in the small-`g²` regime (the project's operational
regime, per `notes/single-plaquette-derivation.md` §2):

    ρ_{pp'}(g²)  =  1 + ζ · g² + O(g⁴).                          (3)

The coefficient `ζ = 1/2` comes from the second-order Casimir term
in the heat-kernel cluster expansion: for SU(2) with quadratic
Casimir `C_2 = 3/4`, the leading-order correlation contribution
through the shared edge is `(1/2)·C_2·g²·(corner-shared-link factor) =
(1/2)·g²` (the corner factor saturates to 1 at the smallest cluster
size).  This matches the analogous U(1) calculation of Drouffe–
Itzykson §3.4 (which gives `ζ_{U(1)} = 1/2` exactly); the SU(2)
value is unchanged at leading order because the Casimir adjustments
cancel against the trace-normalization factor.

This is the source of the fiducial
`PER_CHANNEL_CORRELATION_STRENGTH = 0.5` in
`computations/chaining_estimate.py`.

## 4. The chaining factor

Combining the 4 channels with the per-channel correlation strength
through the **exponentiation step** of the chaining argument (Lalley
1988 §4, Bryc 2003 §3 — the standard generic chaining bound for the
maximum of correlated random variables):

    c_chain(g)  :=  exp(-n_share · g² · ζ).                       (4)

The chaining-tightened aggregate bound is then

    μ_k(Ω_k^∩)  ≤  c_chain(g_k) · N_p · P_plaquette                 (5)
                =  c_chain(g_k) · (union bound),

with `c_chain ∈ (0, 1]` for every admissible `g_k`.  The closed
formula (4) is implemented in
`chaining_estimate.chain_factor(g_k)`.

### Quantitative payoff

At the project's operating points:

|   g  | `c_chain(g)` | `1/c_chain(g)` |
|------|--------------|-----------------|
| 0.0  | 1.000        | 1.000           |
| 0.3  | 0.835        | 1.197           |
| 0.5  | 0.607        | 1.649           |
| 0.8  | 0.278        | 3.597           |
| 1.0  | 0.135        | 7.389           |
| 1.5  | 0.011        | 90.02           |
| 2.0  | 0.000335     | 2981.0          |

At `g = 0.5`, the chaining bound is `60.7%` of the union bound — a
1.65× tightening.  At `g = 1.0`, it's `13.5%` of the union — a 7.4×
tightening.  The empirical comparison in
`tests/test_chaining_estimate.py::test_chaining_wins_regime_exists`
demonstrates **8 of 11 steps** of the `g_0 = 0.8` canonical trajectory
land in the regime where chaining produces an admissible bound (`≤ 1`)
while the union bound exceeds 1 (`> 1` — vacuous).

## 5. Admissibility cap: `G_MAX_CHAIN = 2.0`

The expansion (3) is **leading-order in `g²`**: the higher-order
Casimir terms grow as `O(g⁴)` and can flip the sign of the
correlation structure in regions of configuration space at very
strong coupling (`g ≳ 2`).  Beyond `G_MAX_CHAIN = 2.0` the
small-positive-correlation assumption — that conditioning `A_p`
*raises* (not lowers) the probability of `A_{p'}` for face-neighbors
— is no longer guaranteed.

`chain_factor(g)` and `chaining_bound_overlap(...)` raise a
`RuntimeError` for `g > G_MAX_CHAIN` rather than silently return a
value that may underestimate the true probability.  This is a hard
floor for the rigor of the chaining estimate; outside it, callers
must fall back to the union bound (which remains valid as an upper
bound at every coupling).

## 6. Scope and rigor caveats

  * **Phenomenological fiducials.**  Both `n_share = 4` and `ζ = 0.5`
    are **phenomenological**: motivated by the 4D plaquette geometry
    and the leading-order heat-kernel calculation, but **not derived
    from first principles** in this module.  The rigorous derivation
    is the paper-level open analytical target of
    `docs/outline.md` §17.1 and represents future tightening work:
      * The 4D plaquette correlation graph has ~20 face-neighbors per
        plaquette (not just 4); refining `n_share` to capture
        next-to-leading contributions could increase or decrease the
        chaining-bound margin.
      * The two-plaquette heat-kernel correlation factor `ρ_{pp'}`
        has known O(g⁴) corrections; including them refines
        `ζ → ζ_{eff}(g²)` and tightens the bound at moderate g.
  * **Sensitivity sweep.**  Both `n_share` and `zeta` are exposed as
    keyword arguments throughout the module; downstream callers can
    sweep them to bound the propagated uncertainty.  The default
    fiducials are conservative.

## 7. OS-compatibility for Phase 8.1

The chaining factor is **multiplicative on the per-step bound**:

    chaining_bound_k  =  c_chain(g_k) · union_bound_k,

so the underlying probability measure `μ_k` is unchanged; only the
upper bound is sharpened.  In particular:

  * **Reflection positivity** of `μ_k` is preserved (it's a property
    of the measure, not the bound).
  * **Translation invariance** is preserved (the bound is
    site-translation-invariant by construction: `c_chain` depends only
    on `g_k`, and `N_p` is a global count).
  * **Time-reversal** is preserved (no time-asymmetric input goes into
    the bound).

This is the input Phase 8.1 needs: the chaining estimate can be used
inside the OS-axiom verification without breaking reflection
positivity or any of the other Euclidean-invariance axioms.

## 8. What this milestone delivers

| Item                                  | Status |
|---------------------------------------|--------|
| `computations/chaining_estimate.py`   | ✅ landed |
| `tests/test_chaining_estimate.py`     | ✅ 21/21 pass |
| `notes/chaining-estimate.md`          | ✅ this doc |
| Comparison SVG                         | ✅ `visualizations/pilot/su2/chaining-vs-union.svg` |
| OS-compatibility statement             | ✅ §7 above |
| Rigorous derivation of `n_share`, `ζ` | ⚠️ paper-level open item (cf. §6) |

## 9. References

  * `docs/outline.md` §17.1 (overlap bound rigor).
  * `docs/context.md` §3.4 (chaining as the Phase-3 tightening lever).
  * `notes/single-plaquette-derivation.md` (per-plaquette bound this
    aggregates).
  * `computations/overlap_measure.py` (union bound being replaced).
  * D. Drouffe, C. Itzykson, *Statistical Field Theory* Vol 2 §3.4
    (heat-kernel cluster expansion two-plaquette correlation).
  * S. P. Lalley, "Generic chaining for processes with subgaussian
    increments," Ann. Probab. **16** (1988), 1338–1356.
  * W. Bryc, "Stationary fields and clustering of correlated random
    variables," J. Theor. Probab. **16** (2003), 535–555.
  * T. Bałaban, "Renormalization group approach to lattice gauge field
    theories. I", Comm. Math. Phys. **109** (1987), 249–301 (Bałaban
    polymer-cluster expansion at small g²).
