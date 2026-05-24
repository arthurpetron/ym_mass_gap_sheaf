# codynamic-transfer.md

## Reference Repository

https://github.com/arthurpetron/codynamic-sensor-data

## Purpose

This note makes the transfer explicit:

\[
\text{EKF sheaf induction}
\quad\leadsto\quad
\text{Yang--Mills RG sheaf induction}.
\]

The goal is not to claim the Yang--Mills estimates are already proven. The goal is to identify the exact reusable proof technology: a local estimate, an overlap compatibility condition, a gluing certificate, and a summable degradation budget.

Resolution:

\[
\varepsilon(r,N)
=
\varepsilon_{\mathrm{local}}(r,N)
+
\varepsilon_{\mathrm{glue}}(r,N)
+
\varepsilon_{\mathrm{degrade}}(r,N).
\]

Here \(r\) is the observable support radius and \(N\) is the finite approximation datum. In EKF, \(N\) is time/sample/window data. In Yang--Mills, \(N=(a,L,k)\) is lattice spacing, volume, and RG scale.

---

## 1. Shared proof shape

The common type signature is:

```text
LocalEstimate
+ OverlapCompatibility
+ GluingCertificate
+ SummableDegradationBudget
→ GlobalStableBound
```

Categorically:

\[
\left(
s_i\in \mathcal A(U_i),
\quad
c_{ij}\in \mathcal S(U_i\cap U_j),
\quad
\sum_k d_k < B_0
\right)
\Longrightarrow
s\in\mathcal A(X)
\]

where:

- \(\mathcal A\) is a sheaf/presheaf of bound witnesses.
- \(\mathcal S\) is a presheaf of compatibility or summability certificates.
- \(d_k\) is the degradation/innovation at step \(k\).
- \(B_0\) is the initial budget.

---

## 2. EKF invariant

At estimator step \(n\), the EKF-style codynamic invariant has the form:

\[
\mathcal I_n^{\mathrm{EKF}}
=
(\hat x_n,\ P_n,\ R_n,\ Q_n,\ H_n,\ \Gamma_n,\ B_n).
\]

Meaning:

| Symbol | Meaning |
|---|---|
| \(\hat x_n\) | estimated state |
| \(P_n\) | covariance/error bound |
| \(R_n\) | measurement-noise bound |
| \(Q_n\) | process-noise bound |
| \(H_n\) | local linearization / observation map |
| \(\Gamma_n\) | gluing/compatibility certificate |
| \(B_n\) | remaining rewind/degradation budget |

The inductive claim is:

\[
P_{n+1}
\preceq
\Phi_n(P_n,Q_n,R_n,H_n)
+
D_n
\]

with degradation \(D_n\) satisfying

\[
\sum_n \|D_n\| < B_0.
\]

So the global estimator remains stable if local prediction, local observation, overlap compatibility, and degradation are all bounded.

Type signature:

```text
EKFStep:
  StateEstimate[n]
  × CovarianceBound[n]
  × ObservationSection[n]
  × OverlapCertificate[n]
  × RewindBudget[n]
  → StateEstimate[n+1]
    × CovarianceBound[n+1]
    × UpdatedBudget[n+1]
```

---

## 3. Yang--Mills invariant

At RG scale \(k\), the YM invariant has the form:

\[
\mathcal I_k^{\mathrm{YM}}
=
(
\widehat\sigma_k,\ 
\rho_{\mathrm{sf},k},K_{\mathrm{sf},k},\
\rho_{\mathrm{lf},k},K_{\mathrm{lf},k},\
\rho_{\cap,k},K_{\cap,k},\
g_k,\
\mathcal P_k,\
B_k
).
\]

Meaning:

| Symbol | Meaning |
|---|---|
| \(\widehat\sigma_k=a_k^2\sigma_k\) | renormalized string-tension lower bound |
| \((\rho_{\mathrm{sf},k},K_{\mathrm{sf},k})\) | small-field KP certificate |
| \((\rho_{\mathrm{lf},k},K_{\mathrm{lf},k})\) | large-field KP certificate |
| \((\rho_{\cap,k},K_{\cap,k})\) | overlap/buffer KP certificate |
| \(g_k\) | running coupling |
| \(\mathcal P_k\) | effective-action polymer descriptor |
| \(B_k\) | remaining RG degradation budget |

The inductive claim is:

\[
\widehat\sigma_{k+1}
\ge
\widehat\sigma_k-\eta_k,
\qquad
\sum_k \eta_k < \widehat\sigma_0,
\]

and

\[
K_{\cap,k+1}
\le
K_{\cap,k}+\Delta_{\cap}(b,g_k),
\qquad
\sum_k \Delta_{\cap}(b,g_k)<\infty.
\]

Type signature:

```text
YMRGStep:
  BoundSheaf[k]
  × SummabilityPresheaf[k]
  × EffectiveAction[k]
  × RunningCoupling[k]
  × StringTensionBound[k]
  × RGBudget[k]
  → BoundSheaf[k+1]
    × SummabilityPresheaf[k+1]
    × EffectiveAction[k+1]
    × StringTensionBound[k+1]
    × UpdatedBudget[k+1]
```

---

## 4. Line-by-line transfer

| EKF / sensor-fusion invariant | YM / RG invariant | Transferred proof role |
|---|---|---|
| local sensor section | local activity-bound witness | local estimate valid on one regime |
| sensor chart / manifold patch | gauge chart / small-field patch | local coordinates where approximation is valid |
| covariance matrix \(P_n\) | KP pair \((\rho_k,K_k)\) | quantitative uncertainty/summability bound |
| innovation residual | RG correction term | stepwise error introduced by update |
| overlap agreement | overlap domination | compatibility is weaker than equality |
| gluing failure | KP incompatibility | obstruction to global section |
| RewindEvent | RG correction/degradation event | local repair of failed compatibility |
| RewindBudget \(B_n\) | degradation budget \(B_k\) | finite resource that must not be exhausted |
| cadence/discontinuity detector | small/large/buffer detector | regime-selection logic |
| manifold-aware estimator | Lie-group gauge chart | local linearization on nonlinear space |
| covariance update | KP degradation update | bound propagation through one step |
| stable filter | uniform area-law package | global bound survives all updates |

---

## 5. Sheaf-level map

EKF side:

\[
\mathcal A^{\mathrm{EKF}}(U)
=
\{\text{state estimates on trust region }U\text{ with covariance witness}\}.
\]

YM side:

\[
\mathcal A^{\mathrm{YM}}_k(U,X)
=
\{\text{activity bounds for polymer }X\text{ on configuration region }U\}.
\]

EKF compatibility:

\[
\hat x_i|_{U_i\cap U_j}
\sim
\hat x_j|_{U_i\cap U_j}
\quad
\text{within covariance tolerance}.
\]

YM compatibility:

\[
s^\cap
=
\max(s^{\mathrm{sf}},s^{\mathrm{lf}})
\quad
\text{and}
\quad
s^\cap
\text{ has KP witness }(\rho_\cap,K_\cap).
\]

Thus EKF gluing by agreement-with-error becomes YM gluing by domination-with-summability.

---

## 6. Budget transfer

EKF budget law:

\[
B_{n+1}=B_n-\|D_n\|,
\qquad
B_n>0.
\]

YM budget law:

\[
B_{k+1}=B_k-\eta_k-\lambda\Delta_{\cap,k},
\qquad
B_k>0.
\]

Here \(\lambda\) converts overlap KP degradation into the same scalar budget scale as string-tension degradation.

The key constructive requirement is identical:

\[
\sum \text{degradations} < \text{initial margin}.
\]

EKF:

\[
\sum_n \|D_n\| < B_0.
\]

YM:

\[
\sum_k \eta_k + \lambda\sum_k\Delta_{\cap,k} < \widehat\sigma_0.
\]

---

## 7. The transferable lemma

### Lemma: Stable glued-bound induction

Given:

1. Local bound witnesses \(s_i\in\mathcal A(U_i)\).
2. Compatibility witnesses \(c_{ij}\in\mathcal S(U_i\cap U_j)\).
3. Step map \(T_k:\mathcal A_k\to\mathcal A_{k+1}\).
4. Degradation \(d_k\ge0\).
5. Initial margin \(B_0>0\).
6. Constructive summability witness:

\[
\sum_k d_k < B_0.
\]

Then the glued global bound survives all steps:

\[
B_k
=
B_0-\sum_{i<k}d_i
>
0.
\]

For EKF, \(B_k\) is remaining covariance/rewind margin.

For Yang--Mills, \(B_k\) is remaining renormalized string-tension margin:

\[
\widehat\sigma_k\ge B_k>0.
\]

This is the proof technology to port.

---

## 8. What must be rewritten for Yang--Mills

The sensor-fusion machinery gives the proof skeleton, not the YM estimates. The YM-specific work is:

1. Define the SU(2) site over \(\Omega_k=SU(2)^{E_k}\).
2. Define \(\mathcal A_k(U,X)\) as a cone of activity-bound witnesses.
3. Define \(\mathcal S_k(U,X)\) as KP summability certificates.
4. Compute overlap shell estimate:

\[
\mu_k(\Omega_k^\cap)
\le
N_p(k)C_{SU(2)}
\exp\left(-\frac{\kappa_{SU(2)}}{g_k^2}\right)
g_k^{\beta_{SU(2)}}.
\]

5. Define block-spin pushforward as a morphism of sites.
6. Encode dimensional rescaling as a 2-cell:

\[
\Theta_k:
(T_b)_*(a_k^2\sigma_k)
\Rightarrow
a_{k+1}^2\sigma_{k+1}.
\]

7. Prove the degradation terms are summable.

---

## 9. Minimal SU(2) pilot theorem

A first publishable target is not the Clay theorem. It is:

> For \(G=SU(2)\), over a finite RG range \(0\le k\le K\), the sheaf-glued bound-witness system admits explicit numerical KP certificates and a positive retained renormalized string-tension margin.

Formally:

\[
\widehat\sigma_k
\ge
\widehat\sigma_0-\sum_{i<k}\eta_i
>
0
\quad
\text{for }0\le k\le K.
\]

This would demonstrate that the codynamic sensor-fusion proof machinery transfers into a rigorous Yang--Mills proof-obligation framework.

---

## 10. Core takeaway

The transfer is:

\[
\boxed{
\text{covariance stability under glued local estimators}
}
\quad\leadsto\quad
\boxed{
\text{KP/string-tension stability under glued local RG bounds}
}.
\]

This is not a metaphor. It is the same constructive induction pattern with different local estimates.

---

## 11. Code-level realization (Milestone 4.1, landed 2026-05-25)

The §1 shared proof shape is realized concretely in
[`computations/transfer_examples/`](../computations/transfer_examples/).

  * [`protocol.py`](../computations/transfer_examples/protocol.py) —
    `InductiveBoundWitness` Protocol with members `scale_index`,
    `bound_witness`, `remaining_budget`, `degradation`, `step()`,
    `overlap_compatible()`.  Structurally typed (`@runtime_checkable`):
    any class providing these members at the right types is an
    `InductiveBoundWitness`, no inheritance required.
  * [`runner.py`](../computations/transfer_examples/runner.py) —
    `run_inductive_steps(initial, K)` iterates the Protocol's `step()`,
    accumulates per-step `degradation`, and reports a `RunResult` with
    the closure flag `closes := (all steps succeeded) ∧ (total_deg < B_0)`.
    One function, two domains.
  * [`ekf_example.py`](../computations/transfer_examples/ekf_example.py) —
    `EKFStep`: a vendored 1-D toy EKF satisfying the Protocol.  Closes
    the work_plan 4.1 open question "depend on `codynamic-sensor-data`
    or vendor?" by vendoring a minimal example with no external dep.
  * [`ym_example.py`](../computations/transfer_examples/ym_example.py) —
    `YMStep`: a thin wrapper around `sigma_hat_trajectory` exposing the
    SU(2) RG step as an `InductiveBoundWitness`.

[`tests/test_transfer_examples.py`](../tests/test_transfer_examples.py)
verifies the structural isomorphism:

  * **Protocol conformance**: `isinstance(EKFStep, InductiveBoundWitness)`
    and `isinstance(YMStep, InductiveBoundWitness)` both succeed,
    without any inheritance between them.
  * **Generic-runner polymorphism**: the same `run_inductive_steps`
    callable handles both, returning `RunResult` in each case.
  * **Member-level correspondence** with §4: scale indices advance by 1
    per `step()`; bound-witness labels reflect §4's "EKF P_n ↔ YM σ̂_k"
    mapping; cross-type overlap (EKF vs YM) is structurally decidable
    but semantically refused.
  * **Failure modes**: EKF budget exhaustion and YM trajectory
    exhaustion are reported honestly (`closes = False`,
    `n_steps_taken < K`).

This realizes the §6/§7 claim at the Python type-system level: the proof
shape is a single Protocol, and the EKF/YM instances genuinely share it.
