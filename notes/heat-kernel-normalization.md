# Heat-Kernel Normalization — Prose Companion

> **Companion to** `computations/heat_kernel.py` (implementation) and `tests/test_heat_kernel.py`.
>
> **Milestone.** 1.2 of `work_plan.md`.
>
> Fixes and documents the conversion between the heat-kernel time `t` and the gauge coupling `g`, so the overlap-measure bound of `docs/context.md` §3.4 / `docs/outline.md` §18.5 has unambiguous constants when Milestones 3.1–3.4 plug in SU(2) inputs.

---

## 1. Why three conventions?

The lattice gauge measure on a single plaquette can be written in two physically equivalent but parametrically different ways:

- **Wilson action**: $\exp(-S_W(U)) = \exp\!\bigl(\tfrac{\beta}{N}\,\mathrm{Re\,tr}(U)\bigr)$ with $\beta = 2N/g^2$.
- **Heat-kernel (Manton) action**: $\exp(-S_{HK}(U)) = K_t(U) = \sum_\lambda d_\lambda \chi_\lambda(U)\, e^{-t\,C_2(\lambda)}$ for a heat-kernel time $t$.

The two reproduce the same continuum limit and agree to leading order in the Gaussian regime, but they identify the *time parameter* with the *coupling* differently:

| Convention | Identification | Meaning of small $t$ |
| --- | --- | --- |
| **Wilson** ↔ $t_W = 2N/g^2$ | $t$ is the inverse coupling $\beta$ | $t$ small ↔ $g$ large ↔ strong coupling |
| **Manton** ↔ $t_M = g^2/(2N)$ | $t$ is the heat-kernel diffusion time | $t$ small ↔ $g$ small ↔ weak coupling |

The two are exact reciprocals: $t_W \cdot t_M = 1$ for every choice of $g$ and $N$. Picking one or the other determines whether you treat $t$ as inverse coupling or as diffusion time, but the physics is identical.

The **third** convention is more subtle. `docs/outline.md` §18.5 quotes the SU(2) overlap-measure bound as
$$
\mu_k(\Omega_k^\cap) \;\le\; N_p(k)\;C_{SU(2)}\;\exp\!\Big(\!-\!\tfrac{3}{4 g_k^2}\Big)\;g_k^3.
$$
The exponent coefficient $\kappa_{SU(2)} = 3/4$ here is exactly $C_2(1/2)$, the smallest nonzero Casimir (P1.1). This is the **canonical-κ** convention: write the overlap exponent in $\exp(-\kappa(G)/g^2)$ form with $\kappa(G) := C_2(\lambda_{\min})$ directly, and absorb the rest of the normalization into the *other* constants $C(G), \beta(G)$ of the bound. It is the cleanest reading representation-theoretically and matches outline.md verbatim.

`computations/heat_kernel.py` carries all three as named `HeatKernelConvention` values, with explicit conversion formulas and the SU(2) spot values as `Fraction` constants for downstream Lean / `Q'` interop.

> **Audit resolved (2026-05-24, in 3.2-upgrade).** The Phase-3 code
> uses the canonical and Wilson choices as **inverse-coupling activity-
> exponent normalizations**, *not* literal heat-kernel diffusion times.
> Concretely: in `CANONICAL` (`t = 1/g²`) and `WILSON` (`t = 2N/g²`),
> large `t` corresponds to small `g` and to strong exponential
> suppression of non-trivial irrep contributions in the character
> weights `exp(-t · C_2(j))`. This is the OPPOSITE of the literal-
> diffusion-time reading of $K_t$ (where small `t` ↔ concentration at
> the identity, large `t` ↔ Haar).
>
> For the large-field activity bound, the inverse-coupling reading is
> what we need: the bound `|a^lf(X)| ≤ Z_t^{|X|}` is one-sided and
> shrinks as `g` shrinks, matching the spec form `exp(-ρ_lf · |X|_plaq)`
> of `docs/outline.md` §6.5. The Haar-floor issue documented in
> `notes/single-plaquette-derivation.md` §4 is a property of the
> two-sided buffer-shell *probability* bound; it does not arise for the
> one-sided polymer-activity upper bound used in the large-field KP
> certificate. See `notes/large-field-derivation.md` §3, §5 for the
> derivation in this convention.

---

## 2. Wilson convention, derived

The Wilson plaquette weight is $\exp(\beta \cdot \mathrm{Re\,tr}(U)/N - \beta)$. Expanding around the identity $U = \exp(A)$ in the small-field regime, $\mathrm{Re\,tr}(U)/N \approx 1 - \tfrac{1}{2N}\|A\|^2 + \ldots$, so the action becomes
$$
S_W(U) \;\approx\; \frac{\beta}{2N}\,\|A\|^2 \;=\; \frac{1}{g^2}\,\|A\|^2.
$$

In the heat-kernel form, $K_t(\exp(A)) \approx \exp(-t \cdot \tfrac{1}{2}\,\|A\|^2)$ for small $A$. Matching the small-field expansions: $\tfrac{t}{2} = \tfrac{1}{g^2}$, i.e., $t = 2/g^2$. For general $N$ the matching gives
$$
\boxed{\quad t_W \;=\; \frac{2N}{g^2}. \quad}
$$

The overlap bound's exponent in this convention: the activity of an irrep $\lambda$ is $\exp(-t \cdot C_2(\lambda))$; substituting $t = 2N/g^2$ gives
$$
\exp\!\Big(\!-\tfrac{2N\,C_2(\lambda)}{g^2}\Big).
$$
The smallest nonzero Casimir gives the slowest-decaying contribution: $\kappa_W(G) = 2N \cdot C_2(\lambda_{\min})$.

For SU(2): $\kappa_W = 4 \cdot \tfrac{3}{4} = 3$. The overlap exponent in Wilson is $\exp(-3/g_k^2)$.

---

## 3. Manton convention, derived

The Manton (heat-kernel) action takes $t$ as the genuine diffusion time on the group. In the strong-coupling expansion, $K_t(U) \approx 1 + t\,\mathrm{Re\,tr}(U) + \ldots$, so small $t$ corresponds to nearly-Dirac kernel (no diffusion, i.e., the integral measure is concentrated near identity in the small-fluctuation sense).

Matching to Wilson at the small-field level *with t in the role of diffusion time* gives
$$
\boxed{\quad t_M \;=\; \frac{g^2}{2N}. \quad}
$$
This is the reciprocal of Wilson.

The overlap bound's exponent in Manton: $\exp(-t \cdot C_2(\lambda)) = \exp\!\bigl(-\tfrac{C_2(\lambda)\,g^2}{2N}\bigr)$. **The $g$-dependence is flipped**: instead of $\exp(-\kappa/g^2)$, the bound is $\exp(-c \cdot g^2)$. The coefficient
$$
c \;=\; \frac{C_2(\lambda_{\min})}{2N} \;=\; \frac{3/4}{4} \;=\; \frac{3}{16} \quad\text{(SU(2))}
$$
multiplies $g^2$, not $1/g^2$. `computations.heat_kernel.kappa_from_casimir` refuses to give a Manton "κ" because the bound shape does not match the $\exp(-\kappa/g^2)$ template; use `manton_exponent_coefficient` instead.

In the weak-coupling regime ($g \to 0$), the Manton bound $\exp(-c \cdot g^2) \to 1$ — Manton does not give suppression in the weak-coupling limit, in contrast to Wilson where $\exp(-\kappa/g^2) \to 0$. This is not a contradiction (the underlying physics is the same) — it reflects which *quantity* the convention is bounding. For the buffer-shell measure of context.md §3.4, the Wilson / canonical reading is the natural one.

---

## 4. Canonical-κ convention: matching outline.md §18.5

`outline.md` §18.5 quotes the SU(2) overlap-measure bound as
$$
\mu_k(\Omega_k^\cap) \;\le\; N_p(k)\;C_{SU(2)}\;\exp\!\Big(\!-\!\tfrac{3}{4 g_k^2}\Big)\;g_k^3,
$$
with $\kappa_{SU(2)} = 3/4 = C_2(1/2)$. To match this exponent, write the overlap bound with $\kappa(G) := C_2(\lambda_{\min})$ directly — i.e., absorb the factor $2N$ from the Wilson derivation into the prefactor $C(G)$. This is not a different physics, only a different *placement* of the dimensional constants:

| | Wilson exponent | Wilson prefactor | Canonical exponent | Canonical prefactor |
| --- | --- | --- | --- | --- |
| SU(2) | $\exp(-3/g^2)$ | $C_W(G)$ | $\exp(-(3/4)/g^2)$ | $C_W(G) \cdot \exp(-9/(4 g^2))$ |

Wait — that's not right. The two conventions cannot differ by an exponent rescaling at fixed $g$; they would give different physical bounds. Let me restate.

The canonical convention identifies $\kappa = C_2(\lambda_{\min})$ because it rescales the *heat-kernel time* (or equivalently the coupling $g$) before extracting the exponent. Specifically, a convention where $t = 1/g^2$ (no factor of $2N$) gives $\exp(-t \cdot C_2) = \exp(-C_2/g^2)$, matching outline. The implicit assumption is that the $2N$ factor is absorbed into the *definition of the coupling* (an SU(2) coupling vs an SU(N) coupling), or alternatively that outline is using a unit system where $2N$ is normalized to 1.

The honest reading: **outline.md's $\kappa_{SU(2)} = 3/4$ is the value in a normalization where the $2N$ factor has been absorbed**. To use this value downstream:

- All Phase-3 calculations that quote "$\kappa$" must be in the canonical convention.
- All Wilson-convention calculations (e.g., directly from $t = 2N/g^2$) must convert to canonical before quoting κ.
- The conversion is a known factor: $\kappa_{\text{canonical}} = \kappa_{\text{Wilson}} / (2N)$.

We carry both conventions in code so the conversion is explicit and audit-able. Downstream Phase-3 milestones declare which they use; the same SU(2) physics is recovered either way.

---

## 5. The SU(2) spot values

`computations.heat_kernel` exposes these as `Fraction` constants (exact rational, for Lean `Q'` interop in 3.0+):

```
C_2_SU2_FUNDAMENTAL = 3/4         # the smallest nonzero Casimir
N_SU2 = 2

KAPPA_SU2_CANONICAL = 3/4         # outline §18.5
KAPPA_SU2_WILSON    = 3           # 2N · 3/4 = 3
MANTON_COEFF_SU2    = 3/16        # 3/4 / (2·2) = 3/16
```

The relationship `KAPPA_SU2_WILSON / (2 · N_SU2) = KAPPA_SU2_CANONICAL` is asserted by a unit test.

---

## 6. What 1.2 does NOT do

- It does **not** make the final convention choice for the SU(2) pilot. Milestone 3.x picks one (likely canonical, to match outline.md) and uses it consistently.
- It does **not** compute the prefactor $C(G)$ or the shell-volume exponent $\beta(G)$ — those are in Milestone 1.3 (single-plaquette tail) and 1.4 (union-bound overlap).
- It does **not** establish that any specific κ value is "the right one" — it just makes the conversion explicit so downstream choices are auditable.

---

## 7. Pointers

- The implementation: [`computations/heat_kernel.py`](../computations/heat_kernel.py).
- The tests: [`tests/test_heat_kernel.py`](../tests/test_heat_kernel.py).
- The SU(2) representation data this consumes: [`computations/su2_representations.py`](../computations/su2_representations.py).
- Outline reference: [`docs/outline.md`](outline.md) §18.5.
- Context reference: [`docs/context.md`](context.md) §3.4 (the overlap measure bound).
- Future consumer: Milestone 3.3 (`computations/overlap_kp.py`) consumes the chosen convention to compute Δ_∩.
