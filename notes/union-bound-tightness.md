# Union-Bound Tightness — Prose Companion

> **Companion to** `computations/overlap_measure.py` (1.4) and `notes/single-plaquette-derivation.md` (1.3).
>
> **Milestone.** 1.4 of `work_plan.md`.

---

## 1. The bound

The aggregate overlap-measure bound at scale k is the **union bound** over plaquettes:

$$
\mu_k(\Omega_k^\cap) \;\le\; N_p(k) \cdot P_{\text{plaquette}}(\delta_k, g_k) \;=\; N_p(k) \cdot C(\delta_k) \cdot \exp(-\kappa / g_k^2) \cdot g_k^\beta,
$$

with the per-plaquette $(C, \kappa, \beta)$ from `computations/buffer_shell.py` (1.3) and $N_p(k)$ the plaquette count at scale $k$ (typically $\propto b^{-4k}$ in 4D block-spinning with factor $b$).

The summability question:

$$
\sum_k \mu_k(\Omega_k^\cap) \;\overset{?}{<}\; \infty.
$$

`is_summable_in_k(g_trajectory, n_p_trajectory, delta_trajectory, t_choice)` returns the partial sums + total, plus a flag indicating whether every per-step bound stays below 1 (admissibility check, since a bound above 1 on a probability is trivial).

---

## 2. Where the union bound is loose

Three quantitative sources of looseness, in order of severity:

1. **Per-plaquette looseness inherited from 1.3** (`notes/single-plaquette-derivation.md` §4). The per-plaquette bound formula $C \exp(-\kappa/g^2) g^\beta$ vanishes as $g \to 0$ but the actual probability has a Haar floor $\approx 0.21\,\delta^3$. At small $g$ the per-plaquette bound *undershoots*; multiplying by $N_p$ amplifies this only in magnitude, not in shape.

2. **Plaquette-correlation neglect.** The union bound treats every plaquette as independently in the buffer with probability $P_{\text{plaquette}}$. In reality, plaquettes share links and their being in the buffer is *correlated*. context.md §3.4 explicitly flags this:

   > "Warning. The union bound used to sum the single-plaquette tail estimate over plaquettes is doing real work and may be too loose."

   A chaining / correlated-plaquette estimate (per `docs/outline.md` §17.1) is the proper tightening. Not done here.

3. **Geometric $N_p(k)$ assumption.** This module's `standard_su2_trajectory()` uses $N_p(k) = N_p(0) \cdot b^{-4k}$ (4D coarsening). Real lattice geometries may differ at the boundary or for non-cubic boxes; the bound is `n_p`-linear so the user can supply the geometry directly.

---

## 3. The threshold $g_{\max}$

`g_max_for_validity(n_plaquettes, delta_k, t_choice, target_bound)` computes the largest $g_k$ at which the bound stays below `target_bound` (default 1). Heuristically:

- For $N_p = 100$ and $\delta = 0.2$: bound $\le 1$ for $g_k \lesssim 1.6$.
- For $N_p = 10\,000$ and $\delta = 0.2$: tighter constraint, $g_k \lesssim 1.0$.

The threshold is **N_p-dependent**: more plaquettes → tighter constraint on g. This is the standard "union bound becomes trivial at large $N$" effect.

For an RG trajectory where $N_p(k)$ decays geometrically but $g_k$ grows (confinement direction), the bound stays valid only in an *initial window* of RG steps — beyond which the union bound trivializes. The realistic question for the SU(2) pilot is whether the inductive step closes *within* that window.

---

## 4. The standard SU(2) trajectory

`standard_su2_trajectory()` is a placeholder RG flow for testing and plotting:

- One-loop SU(2) β-function: $1/g_k^2 = 1/g_0^2 - (b_0 / 16\pi^2) \cdot k \log b$, $b_0 = 22/3$.
- $N_p(k) = N_p(0) \cdot b^{-4k}$ (4D coarsening).
- $\delta_k = g_k^\alpha$ with default $\alpha = 0.5$.

It is **not** the canonical RG trajectory for the SU(2) pilot — that requires real coupling-running from 3.1 / 3.2. The trajectory here is geometrically reasonable but not derived; downstream milestones (3.4, 3.5) will supply concrete trajectories.

---

## 5. What 1.4 finds for the standard trajectory

Running `python -m computations.overlap_measure`:

```
Total Σ μ_k(Ω_k^∩) = 9.5e+03
All per-step bounds ≤ 1: False
```

The total is large (~9500) and many per-step bounds exceed 1 — the union bound is **trivial** for the standard trajectory. This is the *expected* outcome per work_plan 1.4's open question (the bound is "not quite" tight enough), and it identifies exactly the regime where the chaining argument of `docs/outline.md` §17.1 will need to take over.

For the figure `visualizations/pilot/su2/overlap-vs-rg-step.svg`: the per-step bound exhibits the per-plaquette growth in $g_k$ tempered (but not enough) by the geometric decay of $N_p(k)$.

---

## 6. What 1.4 does not do

- Does not produce a *tight* aggregate bound; only the union bound.
- Does not compute the actual SU(2) RG trajectory; that is 3.x's input.
- Does not implement the chaining estimate; that is outline §17.1, deferred analytic work.
- Does not connect to the inductive-step degradation budgets — those are 3.3, 3.4.

---

## 7. Per-plaquette bound migration (2026-05-24)

The Haar-floor audit resolution at `notes/single-plaquette-derivation.md` §4 landed a uniformly-valid replacement `BufferShellBound.uniform_value()` for the per-plaquette buffer-shell bound. The 1.4 union-bound aggregator has been migrated:

- `union_bound_overlap(...)` defaults to `use_uniform=True` and pulls the per-plaquette term from `uniform_value()` rather than the legacy `value()`.
- `is_summable_in_k(...)` and `g_max_for_validity(...)` inherit the same default.
- Pass `use_uniform=False` to fall back to the legacy work_plan-spec form for asymptotic-reference / audit-trail use.

Numerical impact on the standard SU(2) trajectory (`g_0 = 1.2, k_max = 8, canonical`):

| convention | Σ_k bound (legacy `value()`) | Σ_k bound (uniform) | ratio |
| --- | --- | --- | --- |
| canonical | 9.50e+03 | 3.58e+04 | ~3.8× |

Both totals exceed 1.0 throughout, which is the well-known union-bound looseness flagged in §5; the resolution that matters is **the bound is now an honest upper bound on the probability rather than an underestimate**. Tightening below 1 requires the chaining estimate (`docs/outline.md` §17.1), still open.

`tests/test_overlap_measure.py` enforces the migration with a default-uses-uniform regression test, a legacy-path-still-available test, a domination test (`uniform ≥ legacy` per plaquette over a δ × g grid), and parity tests for `is_summable_in_k`.

---

## 8. Pointers

- Implementation: [`computations/overlap_measure.py`](../computations/overlap_measure.py).
- Tests: [`tests/test_overlap_measure.py`](../tests/test_overlap_measure.py).
- Figure: [`visualizations/pilot/su2/overlap-vs-rg-step.svg`](../visualizations/pilot/su2/overlap-vs-rg-step.svg).
- Per-plaquette source: [`notes/single-plaquette-derivation.md`](single-plaquette-derivation.md) (1.3).
- Specification: [`docs/context.md`](../docs/context.md) §3.4 (warning), [`docs/outline.md`](../docs/outline.md) §9.2 (analytic work remaining), §17.1 (chaining tightening).
- Downstream: Milestone 3.3 (overlap KP constants) consumes this for the Δ_∩ budget.
