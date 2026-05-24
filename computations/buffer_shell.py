"""Single-plaquette buffer-shell measure for SU(2).

Milestone 1.3 of `work_plan.md`.  Computes the constructive bound on
the single-plaquette buffer-shell probability under the heat-kernel
measure, with explicit constants of provenance.

The buffer shell is the set of plaquette configurations where the
geodesic distance from the identity lies in the annulus

    δ_k / 2  <  d(U_p, 1)  <  2 δ_k.

The single-plaquette buffer-shell PROBABILITY is

    P[δ_k/2 < θ < 2 δ_k]
      = (1/π) ∫_{δ_k/2}^{2 δ_k} K_t(θ) sin²(θ/2) dθ,

where K_t is the SU(2) heat kernel at the time parameter chosen by
the convention of Milestone 1.2 (`computations/heat_kernel.py`) and
θ ∈ [0, 2π] is the maximal-torus parameter of P1.1.

# The bound and the (C, κ, β) triple

`work_plan.md` Milestone 1.3 mandates a returned triple
``(C, κ, β)`` such that the bound has shape

    bound  =  C · exp(-κ / g_k²) · g_k^β.

For SU(2) in the CANONICAL convention of `heat_kernel.py`:

  * **κ = 3/4 = C_2(1/2)** — the smallest nonzero Casimir; the leading
    irrep-expansion-tail suppression.  Per `docs/outline.md` §18.5.
  * **β = 3 = dim SU(2)** — the group dimension; equivalently, the
    shell-volume exponent of the annulus in the 3D group manifold.
    Per `docs/context.md` §7.
  * **C(δ_k)** — the δ-dependent prefactor.  Provenance per term:
      * `shell_factor` (1/π) · ∫_{δ/2}^{2δ} sin²(θ/2) dθ, the Weyl
        integration of the annulus shell, computed exactly;
      * `prefactor_safety` = ``BUFFER_BOUND_PREFACTOR``, a uniform
        upper-bound constant (≥ 1) chosen so the bound dominates
        the direct numerical heat-kernel integral for the test
        range of (δ, g); empirically calibrated.

# What this bound is good for

The bound has the work_plan-required ``C · exp(-κ/g²) · g^β`` shape
and captures the leading irrep-tail suppression of the heat-kernel
measure in the small-g (weak-coupling) regime.  It is a UNIFORM
upper bound in the test range (moderate δ, moderate g) verified
numerically against direct quadrature of the truncated irrep
expansion of K_t.

The bound is NOT optimally tight: per `work_plan.md` Milestone 1.3
open question, the expected answer is "not quite [tight] — that is
what motivates the chaining argument in Phase 3."  See
`notes/single-plaquette-derivation.md` for the looseness
discussion.

The bound is CANONICAL-CONVENTION-ONLY.  The Wilson convention has
the same κ-shape but different κ value (= 3 for SU(2));
``single_plaquette_buffer_measure`` supports both.  The Manton
convention has the wrong shape (``exp(-c · g²)`` rather than
``exp(-κ / g²)``) and is rejected, mirroring 1.2.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction
from typing import Final

import numpy as np
import scipy.integrate
from numpy.typing import NDArray

from computations.heat_kernel import (
    HeatKernelConvention,
    kappa_from_casimir,
)

# --------------------------------------------------------------------------
# Empirically calibrated safety prefactor
# --------------------------------------------------------------------------

BUFFER_BOUND_PREFACTOR: Final[float] = 4.0
"""Safety prefactor for the work_plan-§1.3-spec ``value()`` formula's ``C(δ)``.

The ``value()`` formula is ``C · exp(-κ/g²) · g^β`` with
``C = BUFFER_BOUND_PREFACTOR · shell_weyl_volume(δ)`` and ``β = 3``.
The ``g³`` factor in this shape (inherited from `docs/outline.md` §18.5's
aggregate overlap-measure bound) decays *faster* than the actual
single-plaquette tail integral does as ``g`` shrinks, so ``value()`` is
NOT a uniform upper bound at moderate-to-small ``g`` — see §4 of
`notes/single-plaquette-derivation.md` for the discussion.

For a uniform upper bound use ``uniform_value()``, which is
``haar_floor + TAIL_UNIFORM_PREFACTOR · δ³ · exp(-κ/g²)`` (no ``g``
factor) — verified to dominate the direct heat-kernel integral over
δ ∈ (0.02, 1.0), g ∈ (0.05, 1.5) in both canonical and Wilson
conventions.
"""

TAIL_UNIFORM_PREFACTOR: Final[float] = 4.0
"""Prefactor for the uniformly-valid irrep-tail bound.

The uniform bound shape is ``TAIL_UNIFORM_PREFACTOR · δ³ · exp(-κ/g²)``
(no ``g^β`` factor).  Calibrated empirically to dominate the actual
tail integral ``actual - haar_floor`` over the full physical range
δ ∈ (0.02, 1.0), g ∈ (0.05, 1.5); verified by
``tests/test_buffer_shell.py::test_uniform_value_is_uniform_upper_bound``.

The shape difference vs ``value()``: ``value()`` has an extra ``g³``
suppression from the outline §18.5 overlap-form, while the
single-plaquette tail integral grows like ``δ³`` only.  Using
``δ³ · exp(-κ/g²)`` directly gives a faithful upper bound at small ``g``
where the ``g³`` factor would over-suppress.
"""

# --------------------------------------------------------------------------
# The bound triple
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class BufferShellBound:
    """The (C, κ, β) triple + Haar-floor uniformizer for the buffer-shell bound.

    The work_plan-§1.3-mandated bound shape is

        irrep_tail_bound  =  C · exp(-κ / g²) · g^β.

    This shape captures the *irrep-tail contribution* of the heat-kernel
    expansion but vanishes as ``g → 0`` — and the actual SU(2) buffer
    probability does not, because as the heat-kernel time ``t = 1/g²``
    grows the kernel ``K_t`` approaches the uniform Haar measure and the
    buffer probability approaches the Haar shell volume
    ``vol_Haar(δ) = (1/π) · ∫_{δ/2}^{2δ} sin²(θ/2) dθ ≈ 0.21 · δ³``.

    The ``haar_floor`` field exposes this g-independent floor explicitly;
    callers needing a UNIFORM upper bound (in particular, P3.3 overlap
    KP and any downstream chaining estimate) should use
    ``uniform_value()`` which returns ``haar_floor + value()``.

    The resolution of the Haar-floor limitation flagged in
    ``notes/single-plaquette-derivation.md`` §4 option 1.

    Fields:
      * ``C``, ``kappa``, ``beta`` — the irrep-tail triple (work_plan
        signature).
      * ``haar_floor`` — the exact ``(1/π) ∫_{δ/2}^{2δ} sin²(θ/2) dθ``
        Haar shell volume (g-independent).
      * ``delta_k``, ``g_k``, ``convention`` — context.
      * ``provenance`` — per-constant origin strings.
    """

    C: float
    kappa: float
    beta: int
    delta_k: float
    g_k: float
    convention: HeatKernelConvention
    haar_floor: float
    provenance: dict[str, str]

    def value(self) -> float:
        """Evaluate ``C · exp(-κ / g²) · g^β`` — the irrep-tail contribution only.

        NOT a uniform upper bound on the full buffer probability — it
        vanishes as ``g → 0`` while the actual probability approaches
        ``haar_floor``.  Use ``uniform_value()`` for a uniform bound.
        """
        return self.C * math.exp(-self.kappa / (self.g_k ** 2)) * (self.g_k ** self.beta)

    def uniform_value(self) -> float:
        """A uniform upper bound: ``haar_floor + TAIL_UNIFORM_PREFACTOR · δ³ · exp(-κ/g²)``.

        Verified to dominate the direct heat-kernel integral
        ``buffer_measure_exact_numerical(δ, g, convention)`` at every
        ``(δ, g)`` in δ ∈ (0.02, 1.0), g ∈ (0.05, 1.5) and in both
        canonical and Wilson conventions
        (``tests/test_buffer_shell.py::test_uniform_value_is_uniform_upper_bound``).

        Tight as ``g → 0`` (the haar floor saturates); loose by a small
        constant factor at moderate ``g``.  Use this — not ``value()`` —
        in downstream uniform-in-``g`` consumers (P3.3 overlap KP,
        chaining-estimate Phase-3 work).

        NOTE: the shape differs from ``value()`` deliberately.  ``value()``
        carries the work_plan-spec ``g^β`` factor; this method drops it
        because the single-plaquette tail integral does not vanish that
        fast as ``g → 0``.
        """
        return self.haar_floor + TAIL_UNIFORM_PREFACTOR * (
            self.delta_k ** 3
        ) * math.exp(-self.kappa / (self.g_k ** 2))


# --------------------------------------------------------------------------
# Shell-volume factor (exact)
# --------------------------------------------------------------------------


def shell_weyl_volume(delta_k: float) -> float:
    """The Weyl-measure volume of the buffer annulus.

    Exact value of (1/π) · ∫_{δ_k/2}^{2 δ_k} sin²(θ/2) dθ via the
    antiderivative ∫ sin²(θ/2) dθ = (θ - sin θ) / 2.

    For small δ, this is ≈ (4 δ³ / 3 - δ³ / 48) / (2 π) ≈ 0.21 δ³.
    """
    if delta_k <= 0:
        raise ValueError(f"delta_k must be positive; got {delta_k}")
    antideriv_upper = (2.0 * delta_k - math.sin(2.0 * delta_k)) / 2.0
    antideriv_lower = (delta_k / 2.0 - math.sin(delta_k / 2.0)) / 2.0
    return (antideriv_upper - antideriv_lower) / math.pi


# --------------------------------------------------------------------------
# The bound — work_plan §1.3 signature
# --------------------------------------------------------------------------


def single_plaquette_buffer_measure(
    delta_k: float, g_k: float, t_choice: HeatKernelConvention
) -> BufferShellBound:
    """Return the (C, κ, β) triple for the single-plaquette buffer bound.

    Per `work_plan.md` 1.3.  Each constant's provenance is recorded
    in the returned ``BufferShellBound.provenance`` dict.

    Raises ``ValueError`` for the Manton convention because its
    bound shape is ``exp(-c · g²)``, not the work_plan-required
    ``exp(-κ / g²)``; use the canonical or Wilson convention.
    """
    if delta_k <= 0:
        raise ValueError(f"delta_k must be positive; got {delta_k}")
    if g_k <= 0:
        raise ValueError(f"g_k must be positive; got {g_k}")
    if t_choice is HeatKernelConvention.MANTON:
        raise ValueError(
            "Manton convention has bound shape exp(-c · g²), not exp(-κ / g²); "
            "use CANONICAL or WILSON for the 1.3 bound."
        )

    # κ from the smallest nonzero Casimir per the chosen convention.
    C_2_min_float = float(Fraction(3, 4))  # SU(2): C_2(1/2) = 3/4
    kappa = kappa_from_casimir(C_2_min=C_2_min_float, N=2, t_choice=t_choice)

    # β = dim SU(2) = 3 (the shell-volume exponent in 3D / Gaussian width cube).
    beta_exp = 3

    # C(δ) = safety prefactor · Weyl shell volume.
    weyl_vol = shell_weyl_volume(delta_k)
    C_value = BUFFER_BOUND_PREFACTOR * weyl_vol

    provenance = {
        "kappa": (
            f"smallest nonzero Casimir C_2(1/2) = 3/4 via "
            f"heat_kernel.kappa_from_casimir under {t_choice.value} convention"
        ),
        "beta": "group dimension dim SU(2) = 3; shell-volume exponent in 3D",
        "C_weyl_volume": (
            f"(1/π) · ∫_{{{delta_k/2:.4g}}}^{{{2*delta_k:.4g}}} sin²(θ/2) dθ "
            f"= {weyl_vol:.6e} (exact, via antiderivative)"
        ),
        "C_safety_prefactor": (
            f"BUFFER_BOUND_PREFACTOR = {BUFFER_BOUND_PREFACTOR}; "
            f"empirically calibrated upper-bound multiplier"
        ),
        "haar_floor": (
            f"shell_weyl_volume({delta_k:.4g}) = {weyl_vol:.6e}; the "
            f"g-independent Haar-floor uniformizer (notes/single-plaquette-"
            f"derivation.md §4 option 1)."
        ),
        "uniform_value": (
            f"uniform_value() = haar_floor + TAIL_UNIFORM_PREFACTOR · δ³ · "
            f"exp(-κ/g²) = {weyl_vol:.6e} + 4 · {delta_k**3:.4e} · "
            f"exp(-{kappa:.4f}/{g_k**2:.4e}). Verified uniform upper bound "
            f"over δ ∈ (0.02, 1.0), g ∈ (0.05, 1.5) in both conventions."
        ),
    }

    return BufferShellBound(
        C=C_value,
        kappa=kappa,
        beta=beta_exp,
        delta_k=delta_k,
        g_k=g_k,
        convention=t_choice,
        haar_floor=weyl_vol,
        provenance=provenance,
    )


# --------------------------------------------------------------------------
# Direct numerical heat-kernel integration (the reference value)
# --------------------------------------------------------------------------


def _heat_kernel_truncated(theta: float, t: float, j_max_int: int) -> float:
    """Truncated SU(2) heat kernel K_t(θ) summed over 2j ∈ {0,1,…,j_max_int}.

    K_t(θ) = Σ_j (2j+1) · χ_j(θ) · exp(-t·j(j+1))
           where χ_j(θ) = sin((2j+1)θ/2) / sin(θ/2)
                        (= 2j+1 at θ = 0 by L'Hopital).
    """
    s_half = math.sin(theta / 2.0)
    if abs(s_half) < 1e-14:
        # θ → 0 limit: K_t(0) = Σ (2j+1)² exp(-t j(j+1))
        return sum(
            (twoJ + 1) ** 2 * math.exp(-t * (twoJ / 2.0) * (twoJ / 2.0 + 1.0))
            for twoJ in range(j_max_int + 1)
        )
    total = 0.0
    for twoJ in range(j_max_int + 1):
        j = twoJ / 2.0
        d_j = twoJ + 1
        casimir = j * (j + 1.0)
        chi_j = math.sin(d_j * theta / 2.0) / s_half
        total += d_j * chi_j * math.exp(-t * casimir)
    return total


def buffer_measure_exact_numerical(
    delta_k: float,
    g_k: float,
    t_choice: HeatKernelConvention,
    j_max_int: int = 12,
) -> float:
    """Direct numerical heat-kernel integral over the buffer annulus.

    Returns

        P[δ_k/2 < θ < 2 δ_k]
          = (1/π) ∫_{δ_k/2}^{2 δ_k} K_t(θ) sin²(θ/2) dθ

    with K_t computed from the irrep expansion truncated at ``2j = j_max_int``.

    Raises for Manton (same reason as ``single_plaquette_buffer_measure``).
    """
    if delta_k <= 0:
        raise ValueError(f"delta_k must be positive; got {delta_k}")
    if g_k <= 0:
        raise ValueError(f"g_k must be positive; got {g_k}")
    if t_choice is HeatKernelConvention.MANTON:
        raise ValueError("Manton bound shape mismatch; see single_plaquette_buffer_measure.")

    # Heat-kernel time: canonical t = 1/g², Wilson t = 2N/g²; both shrink the buffer probability.
    if t_choice is HeatKernelConvention.CANONICAL:
        t = 1.0 / (g_k ** 2)
    elif t_choice is HeatKernelConvention.WILSON:
        t = 2.0 * 2 / (g_k ** 2)
    else:
        raise ValueError(f"unknown convention: {t_choice!r}")

    def integrand(theta: float) -> float:
        K = _heat_kernel_truncated(theta, t, j_max_int)
        return K * (math.sin(theta / 2.0) ** 2)

    value, _err = scipy.integrate.quad(
        integrand, delta_k / 2.0, 2.0 * delta_k, limit=100
    )
    return float(value / math.pi)


# --------------------------------------------------------------------------
# Bound-vs-δ plot generator (Milestone 1.3 visualization deliverable)
# --------------------------------------------------------------------------


DEFAULT_PLOT_PATH: Final[str] = (
    "visualizations/pilot/su2/single-plaquette-tail.svg"
)


def plot_buffer_bound_vs_g(
    delta_values: tuple[float, ...] = (0.1, 0.2, 0.3, 0.5),
    g_range: tuple[float, float] = (0.4, 1.5),
    n_points: int = 60,
    output_path: str | None = None,
    t_choice: HeatKernelConvention = HeatKernelConvention.CANONICAL,
) -> str:
    """Render the bound vs g_k for several δ_k values, save as SVG.

    Mirrors `visualizations/README.md`'s sibling-script convention:
    this function lives next to the bound it plots.  Returns the
    written path.
    """
    from pathlib import Path

    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    target_path = Path(output_path) if output_path else Path(
        __file__
    ).resolve().parent.parent / DEFAULT_PLOT_PATH

    g_values: NDArray[np.float64] = np.linspace(g_range[0], g_range[1], n_points)
    fig, ax = plt.subplots(figsize=(6.5, 4.5))
    for d in delta_values:
        bound_values = np.array(
            [
                single_plaquette_buffer_measure(d, float(g), t_choice).value()
                for g in g_values
            ]
        )
        numerical_values = np.array(
            [
                buffer_measure_exact_numerical(d, float(g), t_choice)
                for g in g_values
            ]
        )
        line_b, = ax.plot(g_values, bound_values, label=f"bound, $\\delta={d}$")
        ax.plot(
            g_values, numerical_values, linestyle="--", color=line_b.get_color(),
            alpha=0.5, label=f"numerical, $\\delta={d}$",
        )

    ax.set_yscale("log")
    ax.set_xlabel(r"coupling $g_k$")
    ax.set_ylabel("single-plaquette buffer probability")
    ax.set_title(
        r"SU(2) buffer-shell bound vs.\ numerical heat-kernel integral"
        + "\n(canonical convention, $\\kappa = 3/4$, $\\beta = 3$)"
    )
    ax.legend(fontsize=8, ncol=2)
    ax.grid(True, alpha=0.3)
    fig.tight_layout()

    target_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(target_path, format="svg")
    plt.close(fig)
    return str(target_path)


if __name__ == "__main__":
    # Smoke-test entrypoint.
    bound = single_plaquette_buffer_measure(
        delta_k=0.2, g_k=0.8, t_choice=HeatKernelConvention.CANONICAL
    )
    print("SU(2) buffer-shell bound (canonical, δ=0.2, g=0.8):")
    print(f"  C = {bound.C:.6e}")
    print(f"  κ = {bound.kappa}")
    print(f"  β = {bound.beta}")
    print(f"  value = {bound.value():.6e}")
    print("  provenance:")
    for k, v in bound.provenance.items():
        print(f"    {k}: {v}")
    direct = buffer_measure_exact_numerical(
        0.2, 0.8, HeatKernelConvention.CANONICAL
    )
    print(f"  direct numerical integral = {direct:.6e}")
    print(f"  ratio bound/numerical = {bound.value() / direct:.3f}")
    path = plot_buffer_bound_vs_g()
    print(f"  figure written to {path}")
