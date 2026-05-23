# Small-Field KP Derivation — Literature-Grounded Synthesis

> **Companion to** `computations/small_field_kp.py` (3.1, post-upgrade).
>
> **Milestone.** 3.1 of `work_plan.md`. Replaces the original placeholder constants with a Bałaban-style literature synthesis.

---

## 1. Status: literature-grounded, NOT rigorously derived

Per the Phase-3-kickoff Decision-3 ratification, this module is **literature-grounded synthesis**, not a rigorous from-first-principles Bałaban derivation. The shape of the formula is faithful to the published Bałaban small-field machinery; the specific numerical coefficients are **fiducial values inspired by the literature** but not directly extracted from any single paper.

| Aspect | Status |
| --- | --- |
| Shape `ρ_sf = c_λ · conv_factor / g²` (Bałaban activity rate) | **Real**, faithful to [Bałaban 1985] §5 |
| Shape `K_sf = 1/(1-exp(-(ρ_sf - μ)))` (geometric cluster sum) | **Real**, [Brydges–Federbush 1978] convergence |
| Connectivity μ = log(2d·e) for d=4 | **Real**, standard polymer-counting bound |
| Specific value of `c_λ = 1/2` | **Fiducial**, refinement pending paper consultation |
| Convergence threshold `g_max = √(c_λ/μ) ≈ 0.40` | **Real consequence** of the above |

---

## 2. References

- **[Bałaban 1985]** T. Bałaban, "Renormalization group approach to non-abelian gauge field theories on a lattice," *Comm. Math. Phys.* **99** (1985), 195–211.
- **[Bałaban 1988]** T. Bałaban, "Convergent renormalization expansions for lattice gauge theories," *Comm. Math. Phys.* **119** (1988), 243–285.
- **[Brydges–Federbush 1978]** D. Brydges and P. Federbush, "A new form of the Mayer expansion in classical statistical mechanics," *J. Math. Phys.* **19** (1978), 2064–2067.
- **[Cammarota 1982]** C. Cammarota, "Decay of correlations for infinite range interactions in unbounded spin systems," *Comm. Math. Phys.* **85** (1982), 517–528.
- **[Glimm–Jaffe 1987]** J. Glimm and A. Jaffe, *Quantum Physics: A Functional Integral Point of View* (2nd ed., Springer 1987), Ch. 18.

---

## 3. The derivation in outline

**Step 1: Small-field action.** On a Gribov-safe patch $P_k$ with smallness parameter $\delta_k$, write $U_p = \exp(A_p)$ for $A_p \in \mathfrak{su}(2)$. The Wilson action expands ([Bałaban 1985] §2–3):
$$S_k(U) = \tfrac{1}{2}\langle A, \Delta_k A\rangle + V_k(A), \qquad \deg V_k \ge 3.$$

**Step 2: Activity bound.** The polymer activity satisfies ([Bałaban 1985] §5):
$$|a_k^{sf}(X)| \le \exp\left(-\frac{\alpha(g_k) \cdot |X|_{\text{phys}}}{a_k}\right), \qquad \alpha(g_k) = \frac{c_\lambda}{g_k^2},$$
where $c_\lambda$ is the spectral gap of $\Delta_k$ on $P_k$ (a structural constant depending on patch geometry, lattice dimension, and Killing-form normalization).

**Step 3: Polymer counting.** On a 4D cubic lattice ([Brydges–Federbush 1978] / [Glimm–Jaffe 1987] §18.5), the number of connected polymers of size $n$ containing a fixed plaquette is bounded by
$$N(n) \le C \cdot \mu^n, \qquad \mu = \log(2d \cdot e) = \log(8e) \approx 3.0794 \quad \text{for } d = 4.$$

**Step 4: Cluster-expansion convergence.** The Brydges–Federbush convergence theorem applied to the polymer KP sum gives:
$$\sum_{X \ni x} |a(X)| \cdot e^{\rho|X|} \;\;\text{converges} \;\;\iff\;\; \rho_{sf} > \mu.$$
When convergent:
$$K_{sf} \le \frac{1}{1 - e^{-(\rho_{sf} - \mu)}}.$$

**Step 5: The certificate.** $\rho_{sf} = \alpha(g_k) = c_\lambda / g_k^2$ (canonical convention; Wilson scales by $2N = 4$). $K_{sf}$ from the geometric series when convergent, $+\infty$ otherwise.

---

## 4. Convergence regime — the asymptotic-freedom requirement

With $c_\lambda = 1/2$ and $\mu = \log(8e) \approx 3.08$, the cluster-expansion convergence threshold is

$$g_{\max} = \sqrt{c_\lambda / \mu} \approx 0.40 \quad \text{(canonical)}, \qquad \approx 0.81 \quad \text{(Wilson)}.$$

**The small-field cluster expansion converges only for $g_k < g_{\max}$ — the asymptotic-freedom UV regime.** For larger couplings, $K_{sf} = +\infty$.

This is a real finding, not an artifact. It is the well-known limitation of Bałaban-style perturbative expansions: they require sufficiently weak coupling. The framework's structural prediction (`SmallFieldKP.convergent: bool`) flags this honestly:

```python
>>> compute_small_field_kp(g_k=0.1).convergent
True
>>> compute_small_field_kp(g_k=0.1).K_sf
1.0000  # finite, geometric series converges

>>> compute_small_field_kp(g_k=1.0).convergent
False
>>> compute_small_field_kp(g_k=1.0).K_sf
inf  # cluster expansion diverges
```

---

## 5. Downstream impact

The new formula propagates structurally through 3.3, 3.4, 3.5:

- **3.3** (`overlap_kp`): `K_∩ = K_sf + K_lf`. When K_sf is ∞, K_∩ is ∞. `delta_cap` handles inf gracefully (returns ∞ in non-convergent regime).
- **3.4** (`sigma_hat_trajectory`): η_k = coupling · Δ_∩. When Δ_∩ is ∞, η_k is ∞, σ̂_K → -∞, `budget_closure = False`.
- **3.5** (`pilot_su2`): Criteria 4 (Σ Δ_∩ summable) and 5 (σ̂ positive + budget) fail when the trajectory enters the non-convergent regime.

**Practical consequence for the SU(2) pilot**:

| g_0 (initial coupling) | Convergent? | Pilot succeeds? |
| --- | --- | --- |
| 0.1 (deep UV / asymptotic-freedom) | Yes | Yes (full σ̂ retention) |
| 0.4 (just below threshold) | Marginally | Borderline |
| 1.0 (default / strong coupling) | **No** | **No** (Σ η = ∞) |

The pilot was set up with `g_0 = 1.0` as a placeholder default; with the post-3.1-upgrade formula, the pilot only succeeds in the asymptotic-freedom regime.

This is **not a failure of the framework**. It is the framework correctly surfacing the well-known restriction of Bałaban-style small-field expansions. To close the SU(2) inductive step over the entire RG range, the framework needs either:

1. A strong-coupling expansion to handle the IR regime, or
2. A refined Bałaban analysis that extends the convergence threshold (possible with tighter polymer-counting estimates or block-decomposition tricks), or
3. Confirmation that the program only requires inductive closure within the asymptotic-freedom regime (which may be sufficient for the mass-gap claim).

These are downstream analytic questions, not framework questions.

---

## 6. Per-step ε_sf budget

`eps_sf(g_k, g_k_next, t_choice)` returns the difference $\rho_{sf}(g_k) - \rho_{sf}(g_{k+1})$, clipped at 0. The 2.3 S1 condition is automatically satisfied by construction.

For the asymptotic-freedom direction ($g_{k+1} < g_k$), ε_sf < 0 → clipped to 0. For the confinement direction ($g_{k+1} > g_k$), ε_sf > 0 and grows quadratically in the g-gap.

---

## 7. What was actually upgraded

| Aspect | Before (P3.1 placeholder) | After (P3.1 post-upgrade) |
| --- | --- | --- |
| $\rho_{sf}$ shape | `(1/2)/g²` (heuristic) | `c_λ/g²` with Bałaban interpretation |
| $K_{sf}$ shape | Constant `= 1` | Cluster-expansion geometric sum |
| $K_{sf}$ g-dependence | None | Yes; diverges above threshold |
| Convergence flag | None | `convergent: bool` field |
| Convergence threshold | Implicit (always convergent) | Explicit $g_{\max} \approx 0.40$ |
| Provenance | "PLACEHOLDER" | Bałaban 1985 + Brydges–Federbush 1978 citations |
| Pilot behavior at default g_0 | Trivially passes | Honestly fails (non-convergent regime) |

---

## 8. What still needs work

1. **Specific value of $c_\lambda$.** Currently 1/2 as a fiducial. Refining against [Bałaban 1985] §5's specific bound is the next analytic step. Different normalizations give factor-of-O(1) different values; the structural conclusion (convergence threshold) shifts accordingly.

2. **Convergence-threshold tightening.** The current threshold $g_{\max} \approx 0.40$ may be conservative. Refined polymer-counting (e.g., [Cammarota 1982]'s improved bounds) could push it up to $\sim 0.5$ or more.

3. **3.2 large-field upgrade.** 3.2's K_lf is still placeholder = 1.0. Analogous Brydges–Federbush analysis would give a g-dependent K_lf. Same shape; same downstream impact.

4. **Lean closure**. `[P2.3-sf]` sorry remains open. With the literature-grounded formulas now in Python, the Q'-lift to Lean is more substantive — but the open question of which specific rational upper bound to commit to for a Lean closure remains.

5. **Pilot regime selection.** Should the pilot succeed at `g_0 = 0.1` (asymptotic-freedom) and document the threshold? Or should the framework extend to larger g_0 via strong-coupling additions? Open design question.

---

## 9. Pointers

- Implementation: [`computations/small_field_kp.py`](../computations/small_field_kp.py).
- Tests: [`tests/test_small_field_kp.py`](../tests/test_small_field_kp.py).
- Cascade impact:
  - [`computations/overlap_kp.py`](../computations/overlap_kp.py) `delta_cap` handles inf.
  - [`computations/sigma_hat_trajectory.py`](../computations/sigma_hat_trajectory.py) propagates.
  - [`computations/pilot_su2.py`](../computations/pilot_su2.py) flags failure in non-convergent regime.
- Lean hook (sorry'd, owed by 3.1): `step_obligation_sf` in `lean/YMGap/RG/BlockSpin.lean`.
- Specification: [`docs/context.md`](../docs/context.md) §3.1, [`docs/outline.md`](../docs/outline.md) §6.4.
- Literature references: see §2 above.
