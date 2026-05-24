# σ̂ Trajectory and Global Budget Closure — Prose Companion

> **Companion to** `computations/sigma_hat_trajectory.py` (3.4).
>
> **Milestone.** 3.4 of `work_plan.md`. The make-or-break pilot milestone.
>
> **Status: framework + one live upstream obstruction.** The post-3.1 small-field upgrade makes $K_{sf}$ infinite outside the current Bałaban/Brydges-Federbush convergence window. In that regime this module correctly propagates $\Delta_\cap = \infty$ to $\eta = \infty$ and budget closure fails.

---

## 1. The make-or-break claim

`docs/outline.md` §10.4 and `docs/context.md` §3.3 condition 4 state the load-bearing global claim of the entire inductive-step program:

$$
\sum_{k=0}^{\infty} \eta(b, g_k) \;<\; \widehat{\sigma}_0,
$$

where $\eta(b, g_k)$ is the per-step σ̂ degradation budget (the 2.3 S4 conjunct, the Θ_k transport budget). If this holds, the renormalized string tension survives all RG steps with a positive lower bound; if it fails, the pilot fails.

`compute_eta(g_k, g_k_next, t_choice)` returns the per-step η; `sigma_hat_trajectory(g_traj, σ̂_0)` aggregates Σ_k η_k across a finite trajectory and checks against σ̂_0; `result.budget_closure: bool` is the make-or-break flag.

---

## 2. The current analytic regime

With the post-3.1 small-field upgrade, $K_{sf}$ is finite only when the small-field cluster expansion converges. With the canonical fiducial constants this requires $g_k \lesssim 0.40$. If the tested trajectory leaves that window, $K_{sf} = \infty$, hence $K_\cap = K_{sf} + K_{lf} = \infty$, $\Delta_\cap = \infty$, and the placeholder coupling $\eta_k = 0.5 \Delta_\cap$ also gives $\eta_k = \infty$.

Thus the default $g_0 = 1.0$ pilot fails the make-or-break test. A deliberately weak-coupling pilot can still pass, but that is only a finite-window framework check. Genuine verification of the global closure requires:

1. **Real $K_{lf}(g_k)$** from the large-field character-expansion residual (3.2 replacement point).
2. **A refined or directly extracted small-field $c_\lambda$** replacing the current fiducial $1/2$ if the threshold is to be treated quantitatively.
3. **Real $\eta(b, g_k)$ coupling** from the σ̂-transport derivation (this module's `compute_eta` placeholder).
4. **Real $\widehat{\sigma}_0$** from the input lattice gauge theory (a program-level input, not derived).

When these land, this module's machinery becomes a real test.

---

## 3. Decision-1 re-examination: does Q' suffice for the global sum?

Recorded at the Phase-3 kickoff (Decision 1 record item for 3.4): the ℚ-only Q' representation handles per-step bounds, but the global $\sum_k \eta_k < \widehat{\sigma}_0$ is a statement about an infinite sum's convergence. Re-examining here:

### 3.1. The question, sharper

For the **SU(2) pilot at finite K** (work_plan 3.5 picks $K \ge 3$), the partial sum $\sum_{k=0}^{K} \eta_k$ is a finite sum of rationals — itself a rational. Q' suffices for finite-K verification: pick a rational $q \in $ Q' such that $\sum_{k=0}^{K} \eta_k \le q < \widehat{\sigma}_0$, with $\widehat{\sigma}_0$ also rational. This is mechanically decidable.

For the **full convergence claim** $\sum_{k=0}^{\infty} \eta_k < \widehat{\sigma}_0$, we need to bound an infinite tail. Two paths:

  **(i) Rational tail bound.** Show explicitly that for some K_0 and rational q, $\sum_{k \ge K_0} \eta_k \le q$. If $N_p(k)$ decays geometrically (4D block-spinning gives $b^{-4k}$) and the per-plaquette bound is bounded, geometric series gives a closed-form rational tail bound. Q' suffices.

  **(ii) Constructive-limit argument.** Show the partial sums $S_K = \sum_{k \le K} \eta_k$ are Cauchy with explicit modulus, and the limit is bounded. Needs a constructive-reals layer beyond Q'.

### 3.2. Verdict for the SU(2) pilot

**Q' suffices for finite pilots and for any later proof with an explicit rational tail bound.** The previous geometric-tail argument is conditional on finite per-step factors. If $K_\cap$ or $\eta$ is infinite at any step, no Q' representation issue is involved: the analytic bound has failed before the constructive-limit layer becomes relevant.

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

- Verify the actual SU(2) inductive step closes. The default trajectory currently fails because the small-field threshold is exceeded; the remaining real test awaits 3.2 and 3.4 upgrades plus a normalization audit.
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
