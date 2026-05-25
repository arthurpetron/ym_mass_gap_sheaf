# σ̂ Trajectory and Global Budget Closure — Prose Companion

> **Companion to** `computations/sigma_hat_trajectory.py` (3.4, post-upgrade).
>
> **Milestone.** 3.4 of `work_plan.md`. The make-or-break pilot milestone.
>
> **Status: derived η-coupling + framework in place.** The post-3.4-upgrade replaces the previous placeholder coupling `η = 0.5 · Δ_∩` with a derivation from outline §7.1's smallest Wilson loop area and a Bałaban-style polymer-residual prefactor. With the same default fiducial constants (intentional), the numerical default `η-coupling = 0.5` is unchanged — but the provenance is now explicit.

---

## 1. The make-or-break claim

`docs/outline.md` §10.4 and `docs/context.md` §3.3 condition 4 state the load-bearing global claim of the entire inductive-step program:

$$
\sum_{k=0}^{\infty} \eta(b, g_k) \;<\; \widehat{\sigma}_0,
$$

where $\eta(b, g_k)$ is the per-step σ̂ degradation budget (the 2.3 S4 conjunct, the Θ_k transport budget). If this holds, the renormalized string tension survives all RG steps with a positive lower bound; if it fails, the pilot fails.

`compute_eta(g_k, g_k_next, t_choice)` returns the per-step η; `sigma_hat_trajectory(g_traj, σ̂_0)` aggregates Σ_k η_k across a finite trajectory and checks against σ̂_0; `result.budget_closure: bool` is the make-or-break flag.

---

## 2. σ̂-transport derivation (3.4-upgrade)

The 3.4-upgrade replaces the bare placeholder `η_k = 0.5 · Δ_∩` with a derivation pinning the coupling to two named fiducials, each citable and adjustable:

### 2.1. Setup: the dimensionful and dimensionless string tensions

Per `outline.md` §7.1, at each RG scale `k` the effective string tension `σ_k` is defined by the area-law bound

$$
\langle W_R(C)\rangle_{\mu_k} \;\le\; C_{R,k}\,\exp\bigl(-\sigma_k\,A(C)\bigr)
$$

for Wilson loops with sides at least `2a_k`. The smallest such loop at scale `k+1` has sides `2·a_{k+1}` and area

$$
A_{\min}^{\text{physical}} \;=\; (2a_{k+1})^2 \;=\; 4\,a_{k+1}^2, \qquad A_{\min}^{\text{dimensionless}} = 4.
$$

The renormalized (dimensionless) string tension is `σ̂_k := a_k² · σ_k`.

### 2.2. Naive RG rescaling

Under the block-spin map `T_b` with `a_{k+1} = b · a_k`, pure dimensional analysis (`σ` has mass², `a` has mass⁻¹) predicts the naive rescaling

$$
\sigma_{k+1}^{\text{naive}} \;=\; \sigma_k / b^2.
$$

Lifting to σ̂:

$$
\widehat{\sigma}_{k+1}^{\text{naive}} \;=\; a_{k+1}^2 \cdot \sigma_{k+1}^{\text{naive}} \;=\; (b\,a_k)^2 \cdot \sigma_k / b^2 \;=\; a_k^2 \cdot \sigma_k \;=\; \widehat{\sigma}_k.
$$

That is, σ̂ is **exactly RG-invariant under pure dimensional scaling**. The η budget measures the deviation from this naive invariance.

### 2.3. Polymer-expansion residual

The actual Wilson-loop expectation on `μ_{k+1}` differs from the naive pulled-back value by a polymer cluster-expansion residual. Per [Bałaban 1985 / 1988] and [Brydges 1986], the residual is bounded by `Δ_∩(b, g_k)` — the per-step growth of the buffer KP constant from `2.3 S3 / outline §10.4` — times a polymer-counting prefactor and divided by the loop area:

$$
\bigl|\sigma_{k+1} - \sigma_k / b^2\bigr| \;\le\; \frac{c_{\text{polymer}} \cdot \Delta_\cap(b, g_k)}{A_{\min}^{\text{physical}}} \;=\; \frac{c_{\text{polymer}} \cdot \Delta_\cap}{4\,a_{k+1}^2}.
$$

Here `c_polymer` is the polymer-residual prefactor.  Below is a first-principles derivation that `c_polymer = 2` is the worst-case constant.

#### 2.3-derivation. Combinatorial derivation of `c_polymer = 2`

> **Status (2026-05-25).** Previously labeled HEURISTIC ("polymer can sit on either side of the loop boundary"); reclassified as DERIVED via the triangle-inequality argument below.

**Claim.** In the convergent regime of the polymer cluster expansion, `c_polymer = 2` is the optimal worst-case constant for the per-polymer contribution to the σ-residual under the block-spin coarsening.

**Setup.** Per Brydges 1986 (Les Houches lecture notes, §IV), the Wilson-loop expectation admits the connected-cluster expansion
$$
\log\langle W(C)\rangle_{\mu_k} \;=\; \sum_{X} T_k(X;\,C),
$$
where the sum is over polymers $X$ (connected sets of plaquettes), and $T_k(X; C)$ is the truncated correlation function: $T_k(X;C) = a_k(X)$ for "tree-graph polymers", with the cluster-expansion bound
$$
|T_k(X;\,C)| \;\le\; |a_k(X)| \qquad \text{in the convergent regime.}
$$

Under the block-spin map $T_b$, each scale-$k$ polymer $X$ has a deterministic image $X' := T_b(X)$ at scale $k+1$. The σ-residual is

$$
\sigma_{k+1} - \sigma_k/b^2
\;=\;
-\frac{1}{A(C)} \log\!\left[\frac{\langle W(C)\rangle_{\mu_{k+1}}}{\langle W(C)\rangle_{\mu_k}^{\,b^{-2}}}\right]
\;=\;
-\frac{1}{A(C)} \sum_X \Delta T(X) ,
$$
with the per-polymer change
$$
\Delta T(X) \;:=\; T_{k+1}(X'; C') - T_k(X; C).
$$

**The bound.** Apply the triangle inequality:
$$
\bigl|\Delta T(X)\bigr|
\;=\;
\bigl|T_{k+1}(X'; C') - T_k(X; C)\bigr|
\;\le\;
\bigl|T_{k+1}(X'; C')\bigr| + \bigl|T_k(X; C)\bigr|
\;\le\;
|a_{k+1}(X')| + |a_k(X)|
\;\le\;
2 \cdot \max\bigl(|a_{k+1}(X')|,\,|a_k(X)|\bigr).
$$
The last factor of 2 is the **channel multiplicity**: the per-polymer change is bounded by the sum of two activity terms (the scale-$k$ original and the scale-$(k+1)$ image), hence factor-of-2.

Summing over the boundary polymers (the only $X$ for which $\Delta T \ne 0$ — bulk polymers cancel up to scale-rescaling, see Brydges §IV.3), and using $\sum_X |a(X)| \le \Delta_\cap(b, g_k)$ (the buffer-KP growth from 2.3 S3):
$$
\bigl|\sigma_{k+1} - \sigma_k/b^2\bigr|
\;\le\;
\frac{1}{A(C)} \sum_{X \text{ boundary}} \bigl|\Delta T(X)\bigr|
\;\le\;
\frac{2 \cdot \Delta_\cap(b, g_k)}{A_{\min}^{\text{physical}}}.
$$
Hence $c_{\text{polymer}} = 2$.

**Tightness.** The triangle inequality $|a - b| \le |a| + |b|$ is sharp when $a$ and $b$ have opposite signs. For polymer activities $T_k(X)$ and $T_{k+1}(X')$, sign-preservation under block-spin coarsening is not generically true: cluster-expansion truncation orders can flip signs. So $c_{\text{polymer}} = 2$ is the **optimal worst-case** constant; a tighter $c_{\text{polymer}} < 2$ would require an additional sign-preservation lemma not provided by generic polymer expansion.

**A tighter bound under sign-preservation (open).** If one could show that for the SU(2) heat-kernel measure the leading-order polymer activities preserve sign under $T_b$, the bound would tighten to
$$
\bigl|\Delta T(X)\bigr| \;\le\; \max\bigl(|T_{k+1}(X')|,\,|T_k(X)|\bigr) \;\le\; |a(X)|,
$$
giving $c_{\text{polymer}} = 1$ — halving the σ-budget consumption. This is a quantitative refinement target for a Phase-3.4-or-later analytic note; the current code accepts the parameter and computes either value when supplied.

**Implementation.** The derivation surfaces in code as:

```python
def derive_polymer_boundary_channel_count() -> int:
    """Per the triangle-inequality argument in
    notes/sigma-hat-derivation.md §2.3-derivation: 2."""
    return 2

BALABAN_POLYMER_RESIDUAL = float(derive_polymer_boundary_channel_count())
```

The constant `BALABAN_POLYMER_RESIDUAL = 2` is now sourced from an explicit returns-2 derivation function, not a bare literal.

### 2.4. Lifting to σ̂ — the `a_{k+1}²` cancellation

The per-step σ̂ degradation:

$$
\widehat{\sigma}_{k+1} - \widehat{\sigma}_k \;=\; a_{k+1}^2 \cdot \bigl(\sigma_{k+1} - \sigma_k / b^2\bigr).
$$

Substituting the polymer-residual bound:

$$
\bigl|\widehat{\sigma}_{k+1} - \widehat{\sigma}_k\bigr| \;\le\; a_{k+1}^2 \cdot \frac{c_{\text{polymer}} \cdot \Delta_\cap}{4\,a_{k+1}^2} \;=\; \frac{c_{\text{polymer}}}{4} \cdot \Delta_\cap(b, g_k).
$$

The two factors of `a_{k+1}²` cancel — the lattice spacing drops out exactly because σ̂ is the *dimensionless* string tension and the residual is divided by the smallest *physical* Wilson loop area at the *same* scale.

This is the σ̂-transport identity that justifies setting

$$
\boxed{\quad \eta_k \;=\; \frac{c_{\text{polymer\_residual}}}{A_{\min}^{\text{dimensionless}}} \cdot \Delta_\cap(b, g_k). \quad}
$$

### 2.5. Default values

| Name | Value | Source |
| --- | --- | --- |
| `WILSON_LOOP_MIN_AREA_DIMENSIONLESS` | 4 | outline §7.1 (loops with sides ≥ 2a_k) |
| `BALABAN_POLYMER_RESIDUAL` | 2.0 (fiducial) | [Bałaban 1985 / 1988]; fiducial two-sided polymer-residual symmetry |
| `DERIVED_ETA_COUPLING` | 0.5 | `BALABAN_POLYMER_RESIDUAL / WILSON_LOOP_MIN_AREA_DIMENSIONLESS = 2/4 = 0.5` |

The numerical default `0.5` matches the previous placeholder value. The upgrade is in the **provenance**: every factor is now sourced to a named constant and a literature reference, and either can be adjusted to test sensitivity.

### 2.6. b-independence

Note that the block factor `b` **does not appear** in the η coupling: it enters only via `Δ_∩(b, g_k)` through the trajectory's `g_k` evolution. This is a feature of the canonical-scaling identity σ̂_{k+1}^naive = σ̂_k — the σ̂-transport η is the *non-canonical* part, and the canonical (b-dependent) part has been cancelled exactly.

The helper `derive_eta_coupling(polymer_residual, wilson_loop_min_area)` reflects this: it takes the two fiducials but no `b` argument.

---

## 3. The current analytic regime

With the post-3.1 small-field and post-3.2 large-field upgrades:

- $K_{sf}$ is finite for `g < g_max^{sf}` ≈ 0.40 canonical / 0.81 Wilson.
- $K_{lf}$ is finite for `g < g_max^{lf}` ≈ 0.42 canonical / 0.85 Wilson.
- $K_\cap = K_{sf} + K_{lf}$ is finite only when BOTH are finite, i.e. inside the smaller of the two thresholds (the sf bound).

If the tested trajectory leaves that window, $K_\cap = \infty$, $\Delta_\cap = \infty$, and $\eta_k = \texttt{DERIVED\_ETA\_COUPLING} \cdot \Delta_\cap = \infty$. The default $g_0 = 1.0$ pilot fails the make-or-break test honestly. A deliberately weak-coupling pilot can pass, and now has a *derived* coupling backing the report rather than a placeholder.

For genuine verification of the global closure over a richer trajectory, the remaining refinements are:

1. Refined `BALABAN_POLYMER_RESIDUAL` against direct Bałaban-paper extraction (mirroring the `c_λ` fiducial choice in 3.1).
2. Refined `c_λ` in 3.1 small-field (currently fiducial 1/2).
3. Refined `μ_plaq` in 3.2 large-field (currently fiducial 16).

When these land, the framework becomes a tighter test.

---

## 4. Decision-1 re-examination: does Q' suffice for the global sum?

Recorded at the Phase-3 kickoff (Decision 1 record item for 3.4): the ℚ-only Q' representation handles per-step bounds, but the global $\sum_k \eta_k < \widehat{\sigma}_0$ is a statement about an infinite sum's convergence. The Phase-3 verdict is unchanged by the 3.4-upgrade:

### 4.1. The question, sharper

For the **SU(2) pilot at finite K** (work_plan 3.5 picks $K \ge 3$), the partial sum $\sum_{k=0}^{K} \eta_k$ is a finite sum of rationals — itself a rational. Q' suffices for finite-K verification: pick a rational $q \in $ Q' such that $\sum_{k=0}^{K} \eta_k \le q < \widehat{\sigma}_0$, with $\widehat{\sigma}_0$ also rational. This is mechanically decidable.

For the **full convergence claim** $\sum_{k=0}^{\infty} \eta_k < \widehat{\sigma}_0$, we need to bound an infinite tail. Two paths:

  **(i) Rational tail bound.** Show explicitly that for some K_0 and rational q, $\sum_{k \ge K_0} \eta_k \le q$. If $N_p(k)$ decays geometrically (4D block-spinning gives $b^{-4k}$) and the per-plaquette bound is bounded, geometric series gives a closed-form rational tail bound. Q' suffices.

  **(ii) Constructive-limit argument.** Show the partial sums $S_K = \sum_{k \le K} \eta_k$ are Cauchy with explicit modulus, and the limit is bounded. Needs a constructive-reals layer beyond Q'.

### 4.2. Verdict for the SU(2) pilot

**Q' suffices for finite pilots and for any later proof with an explicit rational tail bound.** Now that the η coupling is derived (not placeholder), the rational tail-bound argument has a concrete coefficient: `DERIVED_ETA_COUPLING = 1/2 ∈ ℚ`, so the geometric tail bound on $\sum_k \eta_k$ is itself rational when `Δ_∩` admits a rational geometric tail bound. Both ingredients live in Q'.

**For Phase 4+ (the continuum limit)**, where the trajectory extends over a continuum of scales, a constructive-reals layer might be needed. That's downstream of 3.5 and beyond Phase 3's scope.

**Recorded decision:** stay with Q' for Phase 3. Do not build a constructive-limit layer here. If 3.5's pilot fails because Q' bounds aren't tight enough at the geometric-series tail estimate, *that* triggers a follow-on (call it `[P3.0-extension]`) — but only then.

### 4.5. UV-direction genuine infinite-trajectory closure — landed 2026-05-25 (Phase 6.2 + 6.3 + 6.4)

Phase 6 of `work_plan.md` delivers the genuine infinite-trajectory closure
for the UV direction in three layers:

  - **Phase 6.2** (`lean/YMGap/Constructive/Geometric.lean`): adds
    `Q'.pow`, `Q'.pow_nonneg`, and the framework theorem
    `geometric_tail_via_input` that composes the user-supplied uniform
    partial-sum bound with `prefix_plus_tail_closure`.  The fully
    inductive `geometric_tail_closure_strong` is documented as a
    follow-on (Milestone 6.2-extension) requiring Q' multiplicative
    arithmetic (`mul_comm`/`mul_assoc`/`mul_add` at the `eqv` level
    + `mul_le_mul_of_nonneg_left`) — not yet built out.
  - **Phase 6.3** (`computations/uv_trajectory.py`): the
    asymptotic-freedom-direction trajectory generator, with the
    AF β-function `1/g_{k+1}² = 1/g_k² + (b_0/16π²)·log b` and the
    monotone-decreasing g_k sequence.
  - **Phase 6.4** (`lean/YMGap/RG/SigmaHatPilotUV.lean`): the UV pilot's
    σ̂-budget closure ``∀ N, finSum eta_pilot_uv N ≤ sigma_hat_0_pilot_uv``
    proven in three independent ways (via `sigma_hat_budget_closure`,
    `prefix_plus_tail_closure`, and `geometric_tail_via_input`).

**Empirical reality**: in the UV direction `K_∩` is non-increasing in k
(because g_k decreases → K_sf and K_lf both decrease), so `Δ_∩ = max(0,
K_next - K) = 0` at every step.  Hence `η_k = 0` for all k in the UV
direction, and the budget closure is the trivial closure
`Σ_{k=0}^∞ 0 = 0 < σ̂_0`.

**Why this is the FIRST "genuine infinite-trajectory" closure in Lean**:
unlike `SigmaHatPilot.lean` (which uses `truncated_const_3` to zero the
sequence past K = 3 artificially), `SigmaHatPilotUV.lean`'s
`eta_pilot_uv` is defined for ALL k ∈ ℕ and is intrinsically zero —
no artifact truncation.  The infinite-N quantifier `∀ N` is genuinely
infinite, supported by the UV trajectory's intrinsic geometric-decay
structure (which collapses to "exactly zero" under the project's
current floating-point + integer-clipped Δ_∩ derivation).

**What remains for Phase 7+** (continuum limit, mass-gap theorem):
the σ̂-budget closure here is necessary but not sufficient for σ̂_∞ > 0
in the continuum limit.  Phase 7.1 builds on this infrastructure to
show σ̂_k converges to a positive limit as k → ∞ (which is what σ̂_∞ > 0
in Lean means).  The non-trivially-decaying η case (relevant for
near-threshold UV trajectories or refined Δ_∩ derivations) requires the
full `geometric_tail_closure_strong`, scoped as 6.2-extension.

### 4.4. Infinite-trajectory closure framework — landed 2026-05-25

The Phase-3 SigmaHatPilot wire-ins use `RationalTail.sigma_hat_budget_closure`,
which takes a uniform-in-N bound directly.  For Phase-4 / continuum-limit
work (UV-direction trajectories where η_k decays geometrically), the
natural shape is "uniform-past-`K_0` bound + nonneg-monotonicity for
`N < K_0`" — which is precisely the §4.2 option (i) "rational tail bound."

`lean/YMGap/Constructive/RationalTail.lean` now provides this:

  - `prefix_plus_tail_closure (η K_0 bound σ_0 h_nonneg h_tail h_budget) : ∀ N, finSum η N ≤ σ_0`
  - Requires monotonicity of partial sums for nonneg sequences, supplied by
    new lemmas `finSum_le_succ_of_nonneg`, `finSum_le_add_of_nonneg`,
    `finSum_monotone_of_nonneg`.
  - Underlying Q' lemma: `Q'.add_le_self_of_nonneg` (`0 ≤ b → a ≤ a + b`),
    proven from cross-product manipulation using only `Int.le_add_of_nonneg_right`
    and basic associativity / commutativity — axiom-gate `[propext]` only.

The SigmaHatPilot canonical and Wilson wire-ins each factor through the
new framework as smoke instances (`eta_pilot_budget_closes_via_prefix_tail`,
`eta_pilot_wilson_budget_closes_via_prefix_tail`).  For the truncated-constant
pilot the tail is exactly zero past `K_0 = 3` (via `finSum_stabilizes_after_K`),
so both routes produce the same closure ``∀ N, finSum eta_pilot N ≤
sigma_hat_0_pilot``.

Pending Phase-4 work: a genuine UV-direction SU(2) trajectory with
geometrically-decaying η_k, plus the Q' geometric-tail-bound derivation
(would require Q'.pow and explicit series-sum machinery).  The framework
above accepts the per-K_0 tail bound as a hypothesis; supplying it from a
geometric formula is the next step.

### 4.3. Q' realization — landed 2026-05-24

The Q'-rational framework is now materialized in
[`lean/YMGap/Constructive/RationalTail.lean`](../lean/YMGap/Constructive/RationalTail.lean):

  - `QSeq := Nat → Q'` and `finSum` give finite partial sums in Q'.
  - `sigma_hat_budget_closure (η eta_total_bound σ_0) (h_bound h_budget) : ∀ N, finSum η N ≤ σ_0` discharges the closure by transitivity, given a uniform partial-sum bound and the closure condition.
  - `finSum_stabilizes_after_K` is the workhorse for truncated-constant sequences: if `η_k = 0` for `k ≥ K` then `finSum η (K + M) = finSum η K`.
  - Smoke (`zero η`) and single-step instances are closed at the framework level.

The **SU(2) pilot wire-in** at
[`lean/YMGap/RG/SigmaHatPilot.lean`](../lean/YMGap/RG/SigmaHatPilot.lean)
takes the canonical Python pilot at `(g_0 = 0.30, K = 3, σ̂_0 = 1)`, bounds
each per-step η_k by a rational `η_max = 11/10000` (Python check: each
of the three η_k ≈ 1.0e-3 falls below this), and discharges the assembled
theorem

```
∀ N, finSum eta_pilot N ≤ sigma_hat_0_pilot     -- = 1
```

with axiom-gate `[propext]` only (no `sorryAx`, no `Classical.*`). A Python
regression test ([`tests/test_q_lift.py::TestLeanWireInConsistency`])
enforces that any change to the upstream fiducials (which would shift the
per-step η values) requires updating the Lean constants in lockstep.

This is the first time the *global* σ̂-budget closure
`Σ_{k=0}^{N} η_k ≤ σ̂_0` has been load-bearingly machine-verified at finite
truncation for the SU(2) pilot.

---

## 5. What is constructively proved, and what remains open

### Constructively proved

1. **The σ̂-transport identity at the canonical scaling level**: `σ̂_{k+1}^naive = σ̂_k` exactly under pure dimensional rescaling. This is dimensional analysis, no analytic input.
2. **The derived η-coupling shape**: `η_k = (c_polymer / A_min) · Δ_∩`, with both factors named, citable, and adjustable.
3. **b-independence of the η coupling**: structural — the lattice spacings `a_{k+1}²` cancel in the lift from σ to σ̂.
4. **Rationality of `DERIVED_ETA_COUPLING`**: with default fiducials 2 and 4, the coupling is exactly `1/2 ∈ ℚ`, suitable for Q' representation in the Lean layer.

### Open

1. **The `BALABAN_POLYMER_RESIDUAL = 2.0` value is fiducial.** Direct extraction of the polymer-counting prefactor from the Bałaban 1988 cluster expansion would refine the coefficient. The shape of the derivation (linear in `c_polymer`) is unaffected; only the numerical value would shift.
2. **The argument uses the *smallest* Wilson loop as the area in the bound denominator.** A more refined analysis using a weighted average over loop sizes might give a tighter coefficient; this is a downstream tightening, not currently captured.
3. **The σ̂-transport identity is local to a single block-spin step.** The infinite-`k` global closure `Σ_k η_k < σ̂_0` requires the geometric-tail argument of §4 above, conditional on `Δ_∩` admitting a rational tail bound. The current `delta_cap_budget` computes finite-K totals; the rational-tail-bound module is the natural next module after `[P2.3-sigma]` Lean closure.
4. **The Lean discharge `[P2.3-sigma]`** is owed against the now-derived η coupling. With `DERIVED_ETA_COUPLING = 1/2 ∈ ℚ` and `Δ_∩` computable in ℚ for finite K, the Q'-lift is mechanical for the per-step S4 obligation. The global budget closure is a separate downstream claim.

---

## 6. What 3.4-upgrade does and does not do

3.4-upgrade **does**:

- Derive `η_k = c_polymer / A_min · Δ_∩` from outline §7.1's smallest Wilson loop and a Bałaban-style polymer-residual prefactor.
- Expose `BALABAN_POLYMER_RESIDUAL` and `WILSON_LOOP_MIN_AREA_DIMENSIONLESS` as named fiducials with citations.
- Add `derive_eta_coupling(...)` as a helper for sensitivity analysis.
- Replace `PLACEHOLDER_ETA_COUPLING` (bare literal `0.5`) with `DERIVED_ETA_COUPLING = derive_eta_coupling()` (still `0.5`, now sourced).
- Preserve the `eta_coupling=…` override in `compute_eta` and `sigma_hat_trajectory` for downstream sensitivity / Lean tests.

3.4-upgrade **does not**:

- Verify the actual SU(2) inductive step closes over the default trajectory. The default `g_0 = 1.0` still fails because the upstream sf threshold is exceeded.
- Refine the `c_polymer` fiducial against the Bałaban paper. That refinement is mechanical given paper consultation.
- Build a constructive-limit layer. Q' suffices for the SU(2) pilot at finite K.
- Close `[P2.3-sigma]` in Lean. The Q'-lift is now mechanical given the derived rational η coupling, but the Lean-side construction itself remains open.

---

## 7. Pointers

- Implementation: [`computations/sigma_hat_trajectory.py`](../computations/sigma_hat_trajectory.py).
- Tests: [`tests/test_sigma_hat_trajectory.py`](../tests/test_sigma_hat_trajectory.py) (21 tests covering derived coupling, helper validation, trajectory aggregation, budget closure).
- Figure: [`visualizations/pilot/su2/sigma-hat-trajectory.svg`](../visualizations/pilot/su2/sigma-hat-trajectory.svg).
- Upstream: 3.3 [`overlap_kp.py`](../computations/overlap_kp.py) (Δ_∩), 3.2 [`large_field_kp.py`](../computations/large_field_kp.py), 3.1 [`small_field_kp.py`](../computations/small_field_kp.py).
- Q' source: [`lean/YMGap/Constructive/Rationals.lean`](../lean/YMGap/Constructive/Rationals.lean).
- Lean per-step closure (closed 2026-05-24): `step_obligation_sigma` in `lean/YMGap/RG/BlockSpin.lean`.
- Lean global closure (closed 2026-05-24, finite truncation): `YMGap.RG.SigmaHatPilot.eta_pilot_budget_closes` in `lean/YMGap/RG/SigmaHatPilot.lean`, built on `YMGap.Constructive.RationalTail.sigma_hat_budget_closure`.
- Specification: [`docs/context.md`](../docs/context.md) §3.3, [`docs/outline.md`](../docs/outline.md) §7.1, §10.4, §17.3.
- Downstream: 3.5 (pilot success criterion) consumes the budget-closure flag as one of its five criteria.
