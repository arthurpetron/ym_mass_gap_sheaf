# Small-Field KP Derivation — Prose Companion

> **Companion to** `computations/small_field_kp.py` (3.1).
>
> **Milestone.** 3.1 of `work_plan.md`.
>
> **Status: FRAMEWORK + PLACEHOLDER.** The functional shape and integration with 2.3 / 3.3 are real and reusable. The specific numerical constants `(ρ_sf, K_sf)` are placeholders.

---

## 1. What the small-field KP certificate is

For the small-field region $\Omega_k^{\mathrm{sf}}$ — configurations where every plaquette is near identity ($d(U_p, 1) < \delta_k$) — Bałaban's perturbative expansion gives a polymer activity bound

$$
|a_k^{\mathrm{sf}}(X)|(u) \;\le\; \exp\!\bigl(-\rho_{sf} \cdot |X|_{\mathrm{phys}} / a_k\bigr),
$$

where $|X|_{\mathrm{phys}}/a_k$ is the polymer's physical extent in lattice units. Combined with the polymer-summability inequality

$$
\sum_{X \ni x} |a_k^{\mathrm{sf}}(X)|(u) \cdot e^{\rho_{sf} \cdot |X|_{\mathrm{phys}}/a_k} \;\le\; K_{sf}
$$

we obtain the small-field KP certificate $(\rho_{sf}, K_{sf})$ that 3.1 must produce as a function of $(g_k, \text{polymer atlas})$.

The rate $\rho_{sf}$ is set by the spectral gap of the small-field Laplacian $\Delta_k$, restricted to a Gribov-safe patch (per `docs/outline.md` §6.4). The amplitude $K_{sf}$ is the cluster-expansion residual: a constant of order unity depending on lattice dimension and combinatorics.

---

## 2. Status: framework, not yet derivation

`work_plan.md` Milestone 3.1's open question:

> "This milestone requires either implementing the relevant pieces of Bałaban's machinery for SU(2) or finding a sufficient citable input. The choice affects the rest of Phase 3 substantially."

This module **does not** implement Bałaban's machinery. It delivers:

1. The **typed integration** of `SmallFieldKP` with the 2.3 `Obligation_sf` hook and with the 3.3 / 3.4 downstream consumers (via `eps_sf`).
2. **Placeholder numerical values** with explicit provenance tagged ``placeholder`` so any downstream code that depends on specific magnitudes sees the placeholder status.
3. The **scaling structure** $\rho_{sf}(g_k) \propto 1/g_k^2$ that is the correct leading behavior in the canonical convention (matches the Gaussian-fluctuation expansion of the Wilson action; the prefactor is the placeholder).

The placeholder is:

$$
\rho_{sf}(g_k) \;=\; \frac{\rho_{\text{base}}}{g_k^2}, \qquad K_{sf} \;=\; K_{\text{base}},
$$

with $\rho_{\text{base}} = 1/2$ and $K_{\text{base}} = 1$. Both are flagged as placeholder.

---

## 3. What to replace this with

When the Bałaban-style derivation is supplied (or a citable explicit value is found), the replacement point is exactly the function `compute_small_field_kp` in `computations/small_field_kp.py`. The signature and the dataclass do not change; the body of the function does.

Two specific replacements are needed:

1. **$\rho_{sf}(g_k)$** should be derived from the spectral gap of $\Delta_k$, which depends on the Gribov-safe-patch atlas (work_plan 2.2's open question, still flagged abstract). For SU(2), Bałaban's bound is roughly $\rho_{sf} \approx \alpha / g_k^2$ for some structural $\alpha > 0$ depending on the lattice dimension; the placeholder $\alpha = 1/2$ is a conservative guess.

2. **$K_{sf}$** comes from the cluster-expansion combinatorics: $K_{sf} = O(1)$ with explicit dependence on the lattice dimension and the polymer-counting function. The placeholder $K_{sf} = 1$ matches the standard order-of-magnitude but is not derived.

When this happens:

- `compute_small_field_kp` returns the actual values; tests verify them.
- The Lean `[P2.3-sf]` sorry can be closed: the `eps_sf` and the cert can be lifted to `Q'` via `kappa_from_casimir_exact`, and a Lean term inhabiting `Obligation_sf` constructed.
- 3.3 (overlap KP) and 3.4 (σ̂-budget) consume the actual values without code change.

---

## 4. The per-step degradation budget `eps_sf`

The 2.3 `S1` condition requires

$$
\rho_{sf}(k+1) \;\ge\; \rho_{sf}(k) - \varepsilon_{sf}(b, g_k).
$$

`eps_sf(g_k, g_k_next, t_choice)` computes the difference $\rho_{sf}(g_k) - \rho_{sf}(g_{k+1})$ (clipped at 0). With the placeholder $\rho \propto 1/g^2$ and $g_{k+1} > g_k$ (confinement direction), $\varepsilon_{sf} > 0$ as expected.

The placeholder ε_sf is therefore consistent with S1: any term inhabiting `Obligation_sf` against the placeholder `compute_small_field_kp` will satisfy S1 by construction (the eps_sf is *defined* to make the inequality hold). The analytic test is whether the actual $\rho_{sf}$ values (when derived) admit a $\varepsilon_{sf}$ that is *also* summable across RG steps — that's 3.4's content, not 3.1's.

---

## 5. Numerical placeholder output

`python -m computations.small_field_kp` on the standard SU(2) trajectory of 1.4:

```
  k    g_k       rho_sf     K_sf
  0   0.8000   0.781250   1.0000
  1   0.9006   0.616593   1.0000
  2   0.9881   0.512197   1.0000
  ...
```

These numbers are placeholder. They are PRESENTED at four-decimal precision to be machine-comparable, but represent only the placeholder formula $\rho_{sf} = (1/2) / g^2$.

---

## 6. Pointers

- Implementation: [`computations/small_field_kp.py`](../computations/small_field_kp.py).
- Tests: [`tests/test_small_field_kp.py`](../tests/test_small_field_kp.py).
- Lean hook (sorry'd, owed by 3.1): [`lean/YMGap/RG/BlockSpin.lean`](../lean/YMGap/RG/BlockSpin.lean) `step_obligation_sf`.
- Specification: [`docs/context.md`](../docs/context.md) §3.1, [`docs/outline.md`](../docs/outline.md) §6.4.
- Downstream: 3.3 (overlap KP via buffer-glue), 3.4 (σ̂ budget accumulates ε_sf across RG steps).
- Replacement point: `compute_small_field_kp(g_k, scale_k, t_choice, rho_base, k_base)`.
