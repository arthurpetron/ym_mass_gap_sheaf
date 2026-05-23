# Large-Field KP Derivation — Prose Companion

> **Companion to** `computations/large_field_kp.py` (3.2). Mirror of `notes/small-field-derivation.md` (3.1) in structure.
>
> **Status: framework + placeholder K_lf; ρ_lf is DERIVED from 1.1/1.2.**

---

## 1. The large-field certificate

For the large-field region $\Omega_k^{\mathrm{lf}}$, the polymer activity decays at rate set by the Casimir gap of the heat-kernel character expansion (per `docs/context.md` §3.1):

$$
|a_k^{\mathrm{lf}}(X)|(u) \;\le\; \exp\!\bigl(-\rho_{lf}\,|X|_{\mathrm{plaq}}\bigr),
$$

where $|X|_{\mathrm{plaq}}$ is the plaquette count of $X$ (combinatorial, not physical extent). The exponential rate $\rho_{lf}$ comes from the smallest nonzero Casimir $C_2(\lambda_1) = C_2(1/2) = 3/4$ for SU(2), times the convention factor from 1.2:

$$
\rho_{lf}(g_k) \;=\; \frac{\kappa_{\text{conv}}(SU(2))}{g_k^2}, \qquad \kappa_{\text{canonical}} = 3/4, \quad \kappa_{\text{Wilson}} = 3.
$$

The amplitude $K_{lf}$ is the cluster-expansion residual, set by the polymer-counting / lattice combinatorics. Placeholder.

---

## 2. What's derived vs placeholder

Unlike 3.1's small-field rate (placeholder), 3.2's $\rho_{lf}$ is **derived** from 1.1 (Casimir) + 1.2 (heat-kernel convention) — it's a real number from upstream framework, computed via `heat_kernel.kappa_from_casimir`. The provenance field marks it as `DERIVED FROM 1.1/1.2`.

$K_{lf}$ remains placeholder at $K_{lf} = 1.0$. The character-expansion-residual amplitude depends on:

- The number of irreps included in the truncated character sum.
- Their relative weights (decaying with $C_2$).
- The polymer-counting combinatorial factor (lattice-dimension dependent).

Replacement happens at `compute_large_field_kp` when the character-expansion convergence analysis lands. The signature does not change.

---

## 3. Convergence radius (work_plan 3.2 open question)

work_plan 3.2's open question:

> "Whether the character-expansion convergence radius is large enough at realistic g_k, or whether resummation is needed."

The placeholder uses the truncated-to-leading-irrep value $\kappa = C_2(1/2)$. If at realistic $g_k$ the higher irreps contribute non-negligibly, the actual $\rho_{lf}$ is *smaller* (slower decay) than the placeholder, and $K_{lf}$ may need additional terms. The conservative reading: this module's $\rho_{lf}$ is an **optimistic** upper bound on the actual large-field decay rate.

Re-examination at 3.4 / 3.5: if the inductive step fails, this is one of the places to revisit.

---

## 4. Structural independence from small-field

The [P2.3-addendum] encoded-but-unverified prediction: `Obligation_lf` takes no `sf_part` input — large-field and small-field derivations are structurally independent.

The 3.2 implementation here respects this: `compute_large_field_kp` does not import or depend on `small_field_kp`. The two are constructed in parallel. **If the actual Bałaban-style derivations couple sf and lf (e.g., via a shared Gribov-patch atlas), [P2.3-addendum]'s prediction is refuted and `Obligation_lf` needs a coupling edge.** This module's structural independence is the audit hook.

---

## 5. Per-step ε_lf budget

`eps_lf(g_k, g_k_next, t_choice)` returns the per-step degradation $\rho_{lf}(g_k) - \rho_{lf}(g_{k+1})$ (clipped at 0). With $\rho_{lf} \propto 1/g_k^2$ and $g_{k+1} > g_k$ (confinement direction), $\varepsilon_{lf} > 0$. The form is **identical** to `eps_sf` modulo the rate-scale factor (canonical vs Wilson) — a structural reflection of the symmetric S1/S2 form in 2.3's `StepTypeWithBudget`.

---

## 6. Pointers

- Implementation: [`computations/large_field_kp.py`](../computations/large_field_kp.py).
- Tests: [`tests/test_large_field_kp.py`](../tests/test_large_field_kp.py).
- Lean hook (sorry'd, owed by 3.2): `step_obligation_lf` in `lean/YMGap/RG/BlockSpin.lean`.
- 1.1 Casimir source: [`computations/su2_representations.py`](../computations/su2_representations.py).
- 1.2 convention source: [`computations/heat_kernel.py`](../computations/heat_kernel.py).
- Downstream: 3.3 (overlap KP) consumes via the buffer-glue Proposition 7.1.
