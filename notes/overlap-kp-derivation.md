# Overlap KP Derivation — Prose Companion

> **Companion to** `computations/overlap_kp.py` (3.3).
>
> **Milestone.** 3.3 of `work_plan.md`.
>
> **Builds on:** `small_field_kp.py` (3.1), `large_field_kp.py` (3.2), `formal/sheaf-framework.tex` Proposition 7.1 + Conjecture 7.4.

---

## 1. The buffer-glue, in code form

`formal/sheaf-framework.tex` Proposition 7.1 says: if the small-field KP and the large-field KP are both well-formed at scale $k$, then the buffer KP is

$$
\rho_\cap = \min(\rho_{sf}, \rho_{lf}), \qquad K_\cap \le K_{sf} + K_{lf}.
$$

`compute_overlap_kp(g_k)` realizes this:

```python
sf = compute_small_field_kp(g_k)
lf = compute_large_field_kp(g_k)
rho_cap = min(sf.rho_sf, lf.rho_lf)
K_cap = sf.K_sf + lf.K_lf  # saturating the upper bound
```

The result carries `proposition_7_1_satisfied: bool` as a structural check — should always be True by construction.

---

## 2. SU(2) values from the placeholder upstream

With 3.1's $\rho_{sf} = 1/2/g_k^2$ (placeholder) and 3.2's $\rho_{lf} = 3/4/g_k^2$ (derived) in the canonical convention:

$$
\rho_\cap = \min\!\left(\frac{1/2}{g_k^2}, \frac{3/4}{g_k^2}\right) = \frac{1/2}{g_k^2}.
$$

So the buffer rate equals the small-field rate (smaller). At $g_k = 1$: $\rho_\cap = 0.5$.

And $K_\cap = 1 + 1 = 2$ across all scales (placeholder K's are $g_k$-independent).

These propagate the placeholder status of $\rho_{sf}$ (3.1) but use the derived $\rho_{lf}$ (3.2); the buffer min picks whichever is smaller, which is the placeholder. When 3.1's actual derivation lands the buffer rate may flip to be set by $\rho_{lf}$ if that becomes smaller.

---

## 3. Closure of [P2.1] sorries (partial)

The Phase-3 kickoff (Decision 1 record) flagged that the 2.1 `domGlue_preserves_KP` sorry has two parts:

  **(a)** Existence of $P$ at the conjectured constants — i.e., that the buffer KP predicate holds at $(\rho_\cap, K_\cap)$.

  **(b)** Tightness of the union bound $K_\cap \le K_{sf} + K_{lf}$ — that the factor-of-2 worst-case is not realized as a fat lossy band.

This module addresses **(a)** at the SU(2)-pilot level: the analytic precondition is supplied (the buffer cert is constructed at the conjectured constants and is consistent with Proposition 7.1). It does **not** close the Lean side — that would require lifting to `Q'` (3.0) and producing a Lean term against the abstract predicate `P`. The Lean `[P2.3-cap]` sorry remains open until that lift happens.

Part **(b)** tightness is empirically testable on the standard trajectory:

```
k    g_k       rho_cap    K_cap
0   1.2000   0.347222    2.0000
1   1.2288   0.331128    2.0000
... (K_cap constant at 2.0)
```

With placeholder $K_{sf} = K_{lf} = 1$, the bound $K_\cap = K_{sf} + K_{lf}$ saturates trivially. The looseness analysis cannot be done meaningfully until 3.1 and 3.2 supply g-dependent K-values.

---

## 4. The Δ_∩ budget

The 2.3 `S3` condition is

$$
K_\cap(k+1) \le K_\cap(k) + \Delta_\cap(b, g_k).
$$

`delta_cap(g_k, g_k_next)` returns the actual per-step growth. With placeholder K-values being g-independent, **Δ_∩ ≡ 0 for the entire trajectory**. The `delta_cap_budget` aggregator returns $\sum_k \Delta_\cap = 0$ trivially.

This is a **trivial pass** of work_plan 3.3's summability check ("verify $\sum_k \Delta_\cap < \infty$"). When 3.1 / 3.2 supply $g$-dependent $K$'s, the budget will become non-trivial and the summability question genuine.

---

## 5. Per-step `delta_cap` vs aggregate `delta_cap_budget`

- `delta_cap(g_k, g_k_next)` — single-step growth at the (k, k+1) transition.
- `delta_cap_budget(g_trajectory)` — partial sums and total Σ_k Δ_∩ across the trajectory.

The figure `visualizations/pilot/su2/delta-cap-budget.svg` plots both $K_\cap(k)$ and the cumulative budget across the standard SU(2) trajectory. With placeholders, both lines are flat.

---

## 6. What 3.3 does and does not do

3.3 **does**:

- Mechanize Proposition 7.1: $\rho_\cap = \min$, $K_\cap = $ sum.
- Verify the construction with `proposition_7_1_satisfied: bool`.
- Provide the Δ_∩ per-step and the aggregate Σ_k Δ_∩.
- Generate the figure.

3.3 **does not**:

- Close the Lean `[P2.3-cap]` sorry. Requires a `Q'`-typed lift and a Lean term against the regime predicate.
- Verify Conjecture 7.4 tightness analytically. Empirical placeholder pass only.
- Compute the actual $g_k$-dependent $K_{sf}, K_{lf}$. Inherits placeholder status from 3.1, 3.2.

When 3.1 and 3.2 turn into real derivations, this module's outputs immediately become real — no code change needed.

---

## 7. Pointers

- Implementation: [`computations/overlap_kp.py`](../computations/overlap_kp.py).
- Tests: [`tests/test_overlap_kp.py`](../tests/test_overlap_kp.py).
- Figure: [`visualizations/pilot/su2/delta-cap-budget.svg`](../visualizations/pilot/su2/delta-cap-budget.svg).
- Upstream: 3.1 [`small_field_kp.py`](../computations/small_field_kp.py), 3.2 [`large_field_kp.py`](../computations/large_field_kp.py).
- Framework: [`formal/sheaf-framework.tex`](../formal/sheaf-framework.tex) Proposition 7.1, Conjecture 7.4.
- Lean hook (sorry'd, owed by 3.3): `step_obligation_cap` in `lean/YMGap/RG/BlockSpin.lean`.
- 2.1 obligations carried through this milestone: [`lean/SORRY_LEDGER.md`](../lean/SORRY_LEDGER.md) `[P2.1]` parts (a) and (b).
- Downstream: 3.4 (σ̂ 2-cell budget) consumes Δ_∩ via the polymer-expansion convergence.
