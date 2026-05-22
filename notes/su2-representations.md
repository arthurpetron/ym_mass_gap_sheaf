# SU(2) Representations: Dimensions, Casimirs, Characters

> **Companion to** `computations/su2_representations.py`.
> **Milestone.** 1.1 of `work_plan.md` (Phase 1 pilot).

## What this note establishes

For each spin $j \in \tfrac{1}{2}\mathbb{N}_0$ the SU(2) irreducible representation has

- dimension $d_j = 2j + 1$;
- quadratic Casimir $C_2(j) = j(j+1)$ in the physics-spin convention (§1 below);
- character $\chi_j(\theta) = \sin\!\big((2j+1)\theta/2\big)/\sin(\theta/2)$ on the maximal torus.

The smallest *nonzero* Casimir is

$$
  C_2(\tfrac{1}{2}) = \tfrac{3}{4}.
$$

This is the quantity quoted in `docs/outline.md` §18.1 as $\kappa_{SU(2)} \sim 3/4$ (up to heat-kernel normalization, closed in Milestone 1.2). It is the heat-kernel spectral gap that drives the overlap-measure bound $\mu_k(\Omega_k^{\cap}) \le \cdots \exp(-\kappa(G)/g_k^2)$.

The companion Python module returns each datum as a sympy expression *and* as a `float`. The verification routines return their **witnessing objects** (the simplified symbolic expression; the Gram matrix and its sup-norm deviation), not booleans — this is the constructive-law discipline of `docs/outline.md` §0.2.

---

## 1. Killing-form normalization

A factor-of-$2N$ ambiguity in the literature makes "the SU(2) Casimir" ill-defined without fixing a convention. The companion module commits to the **physics-spin convention** (call it **convention A**):

- Generators $T_a = \sigma_a/2$, where $\sigma_a$ are the Pauli matrices. They satisfy
  $$
    [T_a, T_b] = i\,\epsilon_{abc} T_c,
    \qquad
    \operatorname{tr}_{\mathrm{fund}}(T_a T_b) = \tfrac{1}{2}\,\delta_{ab}.
  $$
- The Casimir operator $C_2 = T_a T_a$ acts on the spin-$j$ irrep as the scalar
  $$
    C_2(j) = j(j+1).
  $$
- Equivalently: the bi-invariant metric on $\mathfrak{su}(2)$ used to lift indices is $-\operatorname{tr}_{\mathrm{fund}}(\cdot,\cdot)$, and the associated Laplace–Beltrami operator on $SU(2)$ has eigenvalue $C_2(j)$ on the spin-$j$ block.

In particular,
$$
  C_2(0) = 0,\quad
  C_2(\tfrac{1}{2}) = \tfrac{3}{4},\quad
  C_2(1) = 2,\quad
  C_2(\tfrac{3}{2}) = \tfrac{15}{4},\quad
  C_2(2) = 6.
$$

### 1.1. Why convention A

- It is the convention quoted verbatim in `docs/outline.md` §18.1 ($C_2(1/2) = 3/4$, $\kappa_{SU(2)} \sim 3/4$) and `docs/context.md` §7. Picking anything else would force a rescaling in every downstream comparison with the spec.
- The heat-kernel formula
  $$
    K_t(g) = \sum_\lambda d_\lambda\,\chi_\lambda(g)\,e^{-t\,C_2(\lambda)}
  $$
  uses $C_2$ on the diffusion side. The coupling-to-heat-kernel-time conversion $t = t(g)$ absorbs the convention; that conversion is the topic of Milestone 1.2.
- It is the convention under which $J^2 = T_a T_a$ has its textbook eigenvalue $j(j+1)$, i.e., the one in which "spin" means what it means in quantum mechanics.

### 1.2. Relation to other conventions

The factor-of-$2N$ relationships are tabulated for SU(2) ($N = 2$, $h^\vee = 2$):

| Convention | Description                                                              | $C_2(\tfrac{1}{2})$ | Ratio to A |
| ---------- | ------------------------------------------------------------------------ | ------------------- | ---------- |
| **A**      | physics-spin (ours)                                                       | $3/4$               | $1$        |
| B          | Killing form $B(X,Y) = -\operatorname{tr}_{\mathrm{adj}}(\operatorname{ad}_X \operatorname{ad}_Y)$ | $3/16$              | $1/4$      |
| C          | mathematician's compact normalization on the trace form of the fundamental | $3/4$               | $1$ (coincides with A for SU(2)) |
| D          | dual-Coxeter normalization, $C_2(\mathrm{adj}) = 2N$                     | $3/8$               | $1/2$      |

The relation for SU(2): $B(X, Y) = 4 \operatorname{tr}_{\mathrm{fund}}(XY)$ (because $\operatorname{ad}\colon \mathfrak{su}(2) \to \mathfrak{so}(3)$ doubles each Pauli trace and there are three generators). Conventions C and A coincide here but diverge for general $N$, so the convention tag survives.

The named constant `KILLING_FORM_CONVENTION = "physics_spin"` is exported so downstream modules (Milestone 1.2 onward) can sanity-check that they are reading $C_2$ from the same source of truth.

### 1.3. Follow-up handled in Milestone 1.2

Milestone 1.2 commits the coupling–time relation. The choices $t = 2N/g^2$ (Wilson) and the Manton/heat-kernel choice differ by a finite multiplicative factor, which propagates into $\kappa(G)$ in $\exp(-\kappa(G)/g^2)$. Carrying the convention tag explicitly is what protects against a silent rescaling between modules.

---

## 2. Dimensions and Casimirs

### 2.1. Dimensions

The spin-$j$ irrep has weights $j, j-1, \ldots, -j$, each of multiplicity one, so
$$
  d_j = 2j + 1.
$$
The companion module returns this as both `sympy.Integer(2j + 1)` and the `float` $2j + 1$ on every `Irrep`.

### 2.2. Casimirs

The Casimir $C_2 = T_a T_a$ commutes with every $T_a$, so it acts on each irrep by a scalar. Evaluating on the highest-weight state $|j, j\rangle$ via $J^2 = J_z^2 + J_z + J_- J_+$:
$$
  J^2\,|j,j\rangle = (j^2 + j + 0)\,|j,j\rangle = j(j+1)\,|j,j\rangle.
$$
By Schur the same scalar acts on the whole irrep:
$$
  C_2(j) = j(j+1).
$$

### 2.3. Constructive witness for $C_2(1/2) = 3/4$

The verification function
```python
verify_casimir_one_half() -> SymExpr
```
returns the simplified expression $C_2(1/2) - 3/4$. By construction this is `sympy.S.Zero`. The *witness* is the sympy object itself, not a boolean. This is the constructive-law discipline: an existence claim returns the witnessing object together with a computable modulus (here: the symbolic zero, modulus zero).

---

## 3. Characters and orthogonality

### 3.1. Maximal-torus parametrization

A conjugacy class in $SU(2)$ has a unique representative
$$
  t(\theta)
  =
  \begin{pmatrix}
    e^{i\theta/2} & 0 \\
    0 & e^{-i\theta/2}
  \end{pmatrix},
  \qquad
  \theta \in [0, 2\pi].
$$
As $\theta$ runs over $[0, 2\pi]$, $\operatorname{tr} t(\theta) = 2\cos(\theta/2)$ runs over $[-2, 2]$, hitting each class once. (Note: $t(\theta = 2\pi) = -I$ is the nontrivial center element.)

### 3.2. Character formula

On $t(\theta)$ the spin-$j$ irrep acts diagonally with eigenvalues $e^{i m \theta / 2}$ for $m \in \{-2j, -2j+2, \ldots, 2j\}$. Summing the geometric series:
$$
  \chi_j(\theta)
  = \sum_{m = -2j, -2j+2, \ldots}^{2j} e^{i m \theta / 2}
  = \frac{\sin\!\big((2j+1)\theta/2\big)}{\sin(\theta/2)}.
$$
At $\theta = 0$ both numerator and denominator vanish; L'Hôpital gives the dimension:
$$
  \chi_j(0) = 2j + 1 = d_j.
$$
The numerical evaluator handles `theta == 0` (and the equivalent boundary at $2\pi$) explicitly so that no floating-point division by zero occurs.

### 3.3. Weyl integration formula

For class functions $f \colon SU(2) \to \mathbb{C}$,
$$
  \int_{SU(2)} f(g)\, dg
  \;=\;
  \frac{1}{\pi} \int_0^{2\pi} f(\theta)\,\sin^2(\theta/2)\, d\theta.
$$
The Weyl factor $\sin^2(\theta/2)$ is the Jacobian of the maximal-torus parametrization together with the Weyl-group volume $1/|W| = 1/2$.

### 3.4. Orthogonality

Schur orthogonality reads
$$
  \int_{SU(2)} \chi_{j_1}(g)\,\overline{\chi_{j_2}(g)}\, dg
  = \delta_{j_1 j_2}.
$$
Substituting the character formula and the Weyl measure, the $\sin(\theta/2)$ in each character denominator cancels one factor of $\sin^2(\theta/2)$ in the measure:
$$
  \langle \chi_{j_1}, \chi_{j_2}\rangle
  = \frac{1}{\pi}\int_0^{2\pi}
        \sin\!\big((2j_1+1)\theta/2\big)\,
        \sin\!\big((2j_2+1)\theta/2\big)\, d\theta.
$$
Using $\sin A \sin B = \tfrac{1}{2}[\cos(A-B) - \cos(A+B)]$ with $A - B = (j_1 - j_2)\theta$ and $A + B = (j_1 + j_2 + 1)\theta$:

- If $j_1 = j_2$, the first cosine is $1$, giving $\tfrac{1}{2}\cdot 2\pi/\pi = 1$. The second is $\cos\!\big((2j_1 + 1)\theta\big)$ with $2j_1 + 1$ a positive integer, contributing $0$.
- If $j_1 \neq j_2$, both $(j_1 - j_2)$ and $(j_1 + j_2 + 1)$ are nonzero half-integers, and
  $$
    \int_0^{2\pi} \cos(n\theta)\, d\theta
    = \left[\tfrac{1}{n}\sin(n\theta)\right]_0^{2\pi}
    = 0
    \qquad
    \big(n \in \tfrac{1}{2}\mathbb{Z}_{\neq 0}\big),
  $$
  since $\sin(2\pi n) = 0$ whenever $2n \in \mathbb{Z}$.

Hence $\langle \chi_{j_1}, \chi_{j_2}\rangle = \delta_{j_1 j_2}$.

### 3.5. Numerical methodology

The cancellation above means the integrand
$\sin((2j_1 + 1)\theta/2)\,\sin((2j_2 + 1)\theta/2)$
is **smooth** (no removable singularity), so adaptive Gauss–Kronrod quadrature (via `scipy.integrate.quad`) converges at machine precision. The companion module requests `epsabs = 1e-14`.

### 3.6. Constructive witness for orthogonality

The function `character_orthogonality_matrix(irreps)` returns the pair
$$
  (M, \ \|M - I\|_\infty),
  \qquad
  M_{ij} = \langle \chi_i, \chi_j\rangle,
$$
where the second component is the **explicit modulus** of the verification. The test asserts that the modulus is below $10^{-10}$ for $j \le 5$; in practice it is at the quadrature-error floor.

---

## 4. The figure

`visualizations/pilot/su2/casimir-spectrum.svg` plots $C_2(j)$ for $j \in \{0, 1/2, 1, \ldots, 5\}$ with the $C_2(1/2) = 3/4$ point highlighted in red and annotated as the smallest nonzero Casimir.

The figure is produced by `plot_casimir_spectrum` in the companion module. Running
```bash
python -m computations.su2_representations
```
regenerates it from a clean tree (and also prints a textual summary including the orthogonality deviation).

---

## 5. Downstream consumers

These constants feed:

- **Milestone 1.2** — `t = t(g)` conversion uses $C_2(1/2) = 3/4$ to fix $\kappa_{SU(2)}$ in $\exp(-\kappa/g^2)$.
- **Milestone 1.3** — `single_plaquette_buffer_measure` uses $\beta(SU(2)) = \dim SU(2) = 3$ as the shell-volume exponent (the dimension fact is currently in this module's docstring; if it migrates it will move to a dedicated module).
- **Milestone 3.2** — large-field KP constants come from the heat-kernel character expansion, where the Casimir gap $C_2(1/2) - C_2(0) = 3/4$ controls $\rho_{\mathrm{lf}}$.

If any later module needs an SU(2) Casimir, it must import from this module rather than re-deriving — the `KILLING_FORM_CONVENTION` tag exists so that a mismatch is detectable at import time.
