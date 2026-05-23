# Single-Plaquette Buffer-Shell Bound — Prose Companion

> **Companion to** `computations/buffer_shell.py` (implementation) and `tests/test_buffer_shell.py`.
>
> **Milestone.** 1.3 of `work_plan.md`. Computes the constructive bound on the single-plaquette buffer-shell probability under the SU(2) heat-kernel measure, with explicit constants and provenance.
>
> **Builds on:** Milestone 1.1 (representation theory, $C_2(1/2) = 3/4$) and 1.2 (heat-kernel-normalization conventions).

---

## 1. What the bound is

For a single plaquette $U_p$ on the SU(2) lattice, the **buffer-shell probability** under the heat-kernel measure is

$$
P\Big[\,\tfrac{\delta_k}{2} \;<\; d(U_p,\,1) \;<\; 2\,\delta_k\,\Big]
\;=\;
\frac{1}{\pi} \int_{\delta_k / 2}^{2 \delta_k} K_t(\theta)\, \sin^2(\theta/2)\, \mathrm{d}\theta,
$$

where:

- $\theta \in [0, 2\pi]$ is the maximal-torus parameter from `computations/su2_representations.py` (P1.1);
- $K_t(\theta) = \sum_{j \in \frac{1}{2}\mathbb{N}_0} (2j+1)\,\chi_j(\theta)\,e^{-t\,j(j+1)}$ is the SU(2) heat kernel at heat-kernel time $t$;
- $t$ is determined by the gauge coupling $g_k$ via the convention chosen from `computations/heat_kernel.py` (1.2);
- $(1/\pi)\sin^2(\theta/2)\, \mathrm{d}\theta$ is the Weyl measure on the maximal torus.

The **bound** we deliver in 1.3 has the work_plan-required form

$$
\boxed{\quad
P\bigl[\delta_k/2 < d(U_p, 1) < 2 \delta_k\bigr]
\;\le\;
C(\delta_k)\,\exp\!\Big(\!-\tfrac{\kappa}{g_k^2}\Big)\, g_k^{\beta}.
\quad}
$$

For SU(2) in the **canonical** convention of 1.2: $\kappa = 3/4 = C_2(1/2)$, $\beta = 3 = \dim SU(2)$, and $C(\delta_k)$ is the safety-prefactor-multiplied Weyl shell-volume.

---

## 2. The three constants and their provenance

The bound returns a triple $(C, \kappa, \beta)$ with each constant audit-able via the `BufferShellBound.provenance` dict in code.

### 2.1. $\kappa$ — the irrep-tail decay rate

$\kappa$ is set by the smallest nonzero Casimir $C_2(\lambda_1)$ through the heat-kernel time conversion:

| Convention | Heat-kernel time | $\kappa$ for SU(2) |
| --- | --- | --- |
| **Canonical** (default) | $t = 1/g^2$ | $\kappa = C_2(1/2) = 3/4$ |
| **Wilson** | $t = 2N/g^2$ | $\kappa = 2N \cdot C_2(1/2) = 3$ |
| **Manton** | $t = g^2 / (2N)$ | rejected: bound shape is $\exp(-c\,g^2)$, not $\exp(-\kappa/g^2)$ |

Canonical matches `docs/outline.md` §18.5 verbatim and is the default.

Source: `computations.heat_kernel.kappa_from_casimir(C_2_min=3/4, N=2, t_choice)`.

### 2.2. $\beta$ — the shell-volume exponent

$\beta = 3 = \dim SU(2)$. Two equivalent readings:

- **Geometric**: the buffer shell $\{ U : \delta/2 < d(U, 1) < 2\delta \}$ in the 3-dimensional SU(2) group manifold has volume scaling like $\delta^3$ (radial extent times solid-angle).
- **Asymptotic**: in the small-$\delta$ / small-$g$ Gaussian regime of the heat kernel, the width of the kernel scales like $g$, and the leading buffer probability gets one factor of $g$ per group dimension — three for SU(2).

The value matches `docs/context.md` §7's quoted $\beta(SU(2)) = 3$.

### 2.3. $C(\delta_k)$ — the prefactor

$C(\delta_k)$ is the product of two factors:

$$
C(\delta_k) \;=\; \texttt{BUFFER\_BOUND\_PREFACTOR} \;\cdot\; \frac{1}{\pi} \int_{\delta_k/2}^{2 \delta_k} \sin^2(\theta/2)\, \mathrm{d}\theta.
$$

- **Weyl shell volume.** The integral $\frac{1}{\pi}\int_{\delta/2}^{2\delta} \sin^2(\theta/2)\,\mathrm{d}\theta$ is computed exactly in `shell_weyl_volume()` via the antiderivative $\int \sin^2(\theta/2)\,\mathrm{d}\theta = (\theta - \sin\theta)/2$. For small $\delta$ this is $\approx \frac{1}{2\pi}\bigl(\frac{4}{3} - \frac{1}{48}\bigr)\delta^3 \approx 0.21\,\delta^3$.
- **Safety prefactor.** `BUFFER_BOUND_PREFACTOR = 4.0`, an empirically calibrated upper-bound multiplier (see §3 below for what it does and §4 for what it can't fix).

---

## 3. Derivation sketch

The bound is a Bishop-style estimate of the irrep-expansion tail contribution to the buffer probability, with the leading-irrep $j = 1/2$ decay rate $\exp(-t \cdot C_2(1/2)) = \exp(-(3/4)/g^2)$ in canonical convention, the Weyl shell volume, and the geometric $g^\beta$ scaling from the 3D group manifold.

### 3.1. Irrep-expansion tail

The heat kernel decomposes as

$$
K_t(\theta) \;=\; \underbrace{1}_{j=0\text{ (Haar)}} \;+\; \underbrace{\sum_{j \ge 1/2} (2j+1)\,\chi_j(\theta)\,e^{-t\,j(j+1)}}_{\text{irrep tail}}.
$$

The $j = 0$ term is the constant 1 (Haar measure contribution); the $j \ge 1/2$ terms decay exponentially in $t$, with the slowest decay from $j = 1/2$ at rate $\exp(-(3/4)\,t)$.

For the buffer probability:

$$
P[\text{buffer}] \;=\; \underbrace{\frac{1}{\pi}\int_{\delta/2}^{2\delta} \sin^2(\theta/2)\,\mathrm{d}\theta}_{\text{Haar floor}} \;+\; \underbrace{\frac{1}{\pi}\int_{\delta/2}^{2\delta} \text{(irrep tail)}\,\sin^2(\theta/2)\,\mathrm{d}\theta}_{\text{tail contribution}}.
$$

### 3.2. The bound captures the *tail contribution*

The work_plan-required form $C \cdot \exp(-\kappa/g^2) \cdot g^\beta$ vanishes as $g \to 0$ (since $\kappa > 0$). This vanishing form bounds the **irrep-tail contribution** with the leading $j = 1/2$ decay rate.

In canonical convention with $\kappa = 3/4, \beta = 3$, the bound captures the Gaussian-asymptotic regime of the heat kernel where the buffer probability is dominated by the small-$j$ irrep contributions and behaves like $\delta^3 \exp(-3/(4g^2))\,g^3$.

The **Haar floor** is not captured by the $\exp(-\kappa/g^2)\,g^\beta$ form — it is a $g$-independent constant of order $0.21\,\delta^3$. See §4.

---

## 4. Looseness — the Haar-floor limitation

The work_plan-required bound form $C \cdot \exp(-\kappa/g^2) \cdot g^\beta$ with $\kappa > 0$ **vanishes as $g \to 0$**. The actual canonical-convention buffer probability **does not**: as $g \to 0$, the heat-kernel time $t = 1/g^2 \to \infty$, the kernel $K_t \to $ uniform Haar, and the buffer probability approaches the Haar shell volume $\approx 0.21\,\delta^3$ — a $g$-independent floor.

**Consequence.** The bound formula is **not a uniform upper bound** on the full buffer probability at small $g$. At large enough $g$ (numerically: $g \gtrsim 1$), the bound and the direct heat-kernel integral agree in shape and order of magnitude; at smaller $g$, the bound underestimates the actual probability.

`tests/test_buffer_shell.py` verifies:

- monotonicity in $\delta_k$ (formula);
- the bound formula vanishes as $g_k \to 0$ (formula);
- order-of-magnitude consistency with the direct numerical heat-kernel integral at $g = 1.5$ (`test_bound_consistent_with_numerical_at_moderate_g`).

It does **not** verify the bound is an upper bound at $g \to 0$, because it isn't — that's what the canonical-vs-Wilson-vs-Manton convention table of 1.2 already flagged as a regime-dependent question, and the issue surfaces concretely here.

`work_plan.md` 1.3 anticipates this:

> "Whether the bound is tight enough to survive the union bound in Milestone 1.4. The expected answer is 'not quite' — that is what motivates the chaining argument in Phase 3."

The looseness at small $g$ is the *quantitative* version of that warning. Milestone 1.4 (union bound) and Milestone 3.3 (overlap KP constants) will need to handle this. Two paths to tightening:

1. **Add the Haar floor.** Replace $C\,\exp(-\kappa/g^2)\,g^\beta$ with $C_1 \,\delta^3 + C_2\,\exp(-\kappa/g^2)\,g^\beta$ — explicit two-part bound. Loses the single-triple shape work_plan asks for but is a uniform upper bound.
2. **Chaining estimate.** Per `docs/context.md` §3.4, replace the per-plaquette union bound with a chaining / correlated-plaquette argument. This may produce a tighter aggregate bound on $\Omega_k^\cap$ even when the per-plaquette bound has the looseness documented here.

Both are 1.4 / 3.3 decisions; for 1.3 we deliver the work_plan-required triple and document its limitation honestly.

---

## 5. The figure

`visualizations/pilot/su2/single-plaquette-tail.svg` plots the bound (solid) and the direct numerical heat-kernel integral (dashed) versus $g_k$ for $\delta_k \in \{0.1, 0.2, 0.3, 0.5\}$, in canonical convention with $\kappa = 3/4, \beta = 3$. Generated by

```bash
python -m computations.buffer_shell
```

The plot makes the looseness visible: at moderate $g$ (say $g \ge 1$), bound and numerical track in shape; at small $g$ the numerical approaches its $g$-independent Haar floor while the bound continues to decay exponentially, producing the curves crossing on log scale.

---

## 6. What 1.3 does and does not do

1.3 **does**:

- Deliver the $(C, \kappa, \beta)$ triple with provenance per constant.
- Document the bound's shape and the convention dependence.
- Provide direct numerical heat-kernel integration as a reference.
- Generate the comparison figure.

1.3 **does not**:

- Establish a uniform upper bound on the buffer probability for all $g$. The Haar floor at small $g$ means no finite safety prefactor makes this work for the chosen bound shape (see §4).
- Choose a chaining estimate or two-part bound; that's for 1.4.
- Apply the union bound over plaquettes; that's 1.4.
- Convert the bound to a Kotecký–Preiss certificate via Hölder; that's 3.3.

---

## 7. Pointers

- Implementation: [`computations/buffer_shell.py`](../computations/buffer_shell.py).
- Tests: [`tests/test_buffer_shell.py`](../tests/test_buffer_shell.py).
- Figure: [`visualizations/pilot/su2/single-plaquette-tail.svg`](../visualizations/pilot/su2/single-plaquette-tail.svg).
- Heat-kernel conventions: [`computations/heat_kernel.py`](../computations/heat_kernel.py) (1.2) and [`notes/heat-kernel-normalization.md`](heat-kernel-normalization.md).
- SU(2) representation data: [`computations/su2_representations.py`](../computations/su2_representations.py) (1.1) and [`notes/su2-representations.md`](su2-representations.md).
- Specification: [`docs/context.md`](../docs/context.md) §3.4 (the overlap measure bound), §7 ($\beta(SU(2)) = 3$); [`docs/outline.md`](../docs/outline.md) §18.5 (the explicit SU(2) bound form).
- Downstream consumers: Milestone 1.4 (union bound over plaquettes) and 3.3 (overlap KP constants).
