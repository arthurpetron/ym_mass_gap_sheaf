# σ̂ Trajectory and Global Budget Closure — Prose Companion

> **Companion to** `computations/sigma_hat_trajectory.py` (3.4).
>
> **Milestone.** 3.4 of `work_plan.md`. The make-or-break pilot milestone.
>
> **Status: framework + placeholders inherited from 3.1–3.3.** The budget closure is trivially satisfied in the placeholder regime; genuine verification requires the analytic derivations to land first.

---

## 1. The make-or-break claim

`docs/outline.md` §10.4 and `docs/context.md` §3.3 condition 4 state the load-bearing global claim of the entire inductive-step program:

$$
\sum_{k=0}^{\infty} \eta(b, g_k) \;<\; \widehat{\sigma}_0,
$$

where $\eta(b, g_k)$ is the per-step σ̂ degradation budget (the 2.3 S4 conjunct, the Θ_k transport budget). If this holds, the renormalized string tension survives all RG steps with a positive lower bound; if it fails, the pilot fails.

`compute_eta(g_k, g_k_next, t_choice)` returns the per-step η; `sigma_hat_trajectory(g_traj, σ̂_0)` aggregates Σ_k η_k across a finite trajectory and checks against σ̂_0; `result.budget_closure: bool` is the make-or-break flag.

---

## 2. The current placeholder regime

With 3.1 placeholder $K_{sf} = 1$, 3.2 placeholder $K_{lf} = 1$, and 3.3's $K_\cap = K_{sf} + K_{lf} = 2$ (constant in $g_k$), the per-step buffer growth $\Delta_\cap \equiv 0$. The σ̂ degradation via the coupling $\eta_k = c \cdot \Delta_\cap$ (placeholder coupling $c = 0.5$) is therefore identically 0. The total $\sum_k \eta_k = 0$ trivially satisfies $< \widehat{\sigma}_0$ for any positive σ̂_0.

**This passes the make-or-break test trivially; it tells us nothing**. Genuine verification of the global closure requires:

1. **Real $K_{sf}(g_k), K_{lf}(g_k)$** from the Bałaban derivations (3.1, 3.2 replacement points).
2. **Real $\eta(b, g_k)$ coupling** from the σ̂-transport derivation (this module's `compute_eta` placeholder).
3. **Real $\widehat{\sigma}_0$** from the input lattice gauge theory (a program-level input, not derived).

When all three land, this module's machinery becomes a real test.

---

## 3. Decision-1 re-examination: does Q' suffice for the global sum?

Recorded at the Phase-3 kickoff (Decision 1 record item for 3.4): the ℚ-only Q' representation handles per-step bounds, but the global $\sum_k \eta_k < \widehat{\sigma}_0$ is a statement about an infinite sum's convergence. Re-examining here:

### 3.1. The question, sharper

For the **SU(2) pilot at finite K** (work_plan 3.5 picks $K \ge 3$), the partial sum $\sum_{k=0}^{K} \eta_k$ is a finite sum of rationals — itself a rational. Q' suffices for finite-K verification: pick a rational $q \in $ Q' such that $\sum_{k=0}^{K} \eta_k \le q < \widehat{\sigma}_0$, with $\widehat{\sigma}_0$ also rational. This is mechanically decidable.

For the **full convergence claim** $\sum_{k=0}^{\infty} \eta_k < \widehat{\sigma}_0$, we need to bound an infinite tail. Two paths:

  **(i) Rational tail bound.** Show explicitly that for some K_0 and rational q, $\sum_{k \ge K_0} \eta_k \le q$. If $N_p(k)$ decays geometrically (4D block-spinning gives $b^{-4k}$) and the per-plaquette bound is bounded, geometric series gives a closed-form rational tail bound. Q' suffices.

  **(ii) Constructive-limit argument.** Show the partial sums $S_K = \sum_{k \le K} \eta_k$ are Cauchy with explicit modulus, and the limit is bounded. Needs a constructive-reals layer beyond Q'.

### 3.2. Verdict for the SU(2) pilot

**Q' suffices.** The standard SU(2) trajectory's $N_p(k) = N_p(0) \cdot b^{-4k}$ decays geometrically; the per-plaquette factors are bounded for the trajectory's bounded $g_k$ range. The tail $\sum_{k \ge K_0} \eta_k$ admits a rational geometric bound, and the full sum admits a rational upper estimate. The Lean closure of `[P2.3-sigma]` against Q' is mechanical once the actual $\eta(b, g_k)$ formula lands.

**For Phase 4+ (the continuum limit)**, where the trajectory extends over a continuum of scales, a constructive-reals layer might be needed. That's downstream of 3.5 and beyond Phase 3's scope.

**Recorded decision:** stay with Q' for Phase 3.  Do not build a constructive-limit layer here.  If 3.5's pilot fails because Q' bounds aren't tight enough at the geometric-series tail estimate, *that* triggers a follow-on (call it `[P3.0-extension]`) — but only then.

---

## 4. What 3.4 does and does not do

3.4 **does**:

- Define the per-step η_k as a placeholder coupling to Δ_∩.
- Aggregate Σ_k η_k across an RG trajectory.
- Provide the budget-closure bool flag.
- Generate the σ̂ trajectory + cumulative-η figure.
- **Decide the Q' boundary question** for the SU(2) pilot (see §3): Q' suffices at finite K with a geometric-series tail estimate.

3.4 **does not**:

- Verify the actual SU(2) inductive step closes. With placeholders, the test is trivial (Σ η = 0); the real test awaits 3.1–3.3 replacement.
- Build a constructive-limit layer. Q' suffices for the pilot.
- Close `[P2.3-sigma]` in Lean. Same reason as 3.1–3.3: needs the actual η formula plus the Q'-lift.

---

## 5. Pointers

- Implementation: [`computations/sigma_hat_trajectory.py`](../computations/sigma_hat_trajectory.py).
- Tests: [`tests/test_sigma_hat_trajectory.py`](../tests/test_sigma_hat_trajectory.py).
- Figure: [`visualizations/pilot/su2/sigma-hat-trajectory.svg`](../visualizations/pilot/su2/sigma-hat-trajectory.svg).
- Upstream: 3.3 [`overlap_kp.py`](../computations/overlap_kp.py) (Δ_∩), 3.2 [`large_field_kp.py`](../computations/large_field_kp.py), 3.1 [`small_field_kp.py`](../computations/small_field_kp.py).
- Q' source: [`lean/YMGap/Constructive/Rationals.lean`](../lean/YMGap/Constructive/Rationals.lean).
- Lean hook (sorry'd, owed by 3.4): `step_obligation_sigma` in `lean/YMGap/RG/BlockSpin.lean`.
- Specification: [`docs/context.md`](../docs/context.md) §3.3, [`docs/outline.md`](../docs/outline.md) §10.4, §17.
- Downstream: 3.5 (pilot success criterion) consumes the budget-closure flag as one of its five criteria.
