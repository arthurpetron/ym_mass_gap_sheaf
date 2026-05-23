"""Heat-kernel normalization conventions for the lattice gauge measure.

Milestone 1.2 of `work_plan.md`.  Fixes and documents the conversion
between the heat-kernel time parameter ``t`` and the gauge coupling
``g``, so that the overlap-measure bound of `docs/context.md` §3.4 /
`docs/outline.md` §18.5 has unambiguous constants when SU(2) inputs
are plugged in (Milestone 3.x).

Two conventions are carried side-by-side, per the open-question
recommendation in `work_plan.md` Milestone 1.2:

* The **Wilson** convention: ``t_W = 2 N / g²`` for ``SU(N)``.
  Here ``t`` is identified with the Wilson inverse coupling
  ``β = 2N / g²``; large ``t`` corresponds to weak coupling.

* The **Manton** (heat-kernel) convention: ``t_M = g² / (2N)``.
  Here ``t`` is the heat-kernel diffusion time; small ``t``
  corresponds to weak (narrow-fluctuation) coupling.

The conventions are related by ``t_W · t_M = 1`` — they are
reciprocals.  Which to use depends on how the polymer activity is
written downstream; both produce valid bounds with different
explicit constants.

Outline / context references to ``κ_{SU(2)} ~ 3/4``
================================================

`docs/outline.md` §18.5 quotes the SU(2) overlap-measure bound

    μ_k(Ω_k^∩) ≤ N_p(k) · C_{SU(2)} · exp(-3 / (4 g_k²)) · g_k^3,

i.e. the exponent has coefficient ``κ_{SU(2)} = 3/4 = C_2(1/2)``
(the smallest nonzero Casimir, P1.1).  This identification — κ
equal to ``C_2(λ_min)`` directly, with no factor of ``2N`` — is
what we call the **canonical-κ** convention here.  It is the
identification that makes the LaTeX exponent read cleanly as a
representation-theoretic constant and matches `outline.md` and
`context.md` verbatim.

It is NOT the Wilson identification.  In Wilson, the overlap
exponent picks up the factor ``2N``:

    Wilson κ for SU(2):  2N · C_2(1/2) = 4 · 3/4 = 3.

And it is not the Manton identification, because in Manton the
bound has shape ``exp(-c · g²)``, not ``exp(-κ / g²)`` — the
g-dependence is flipped.  The canonical-κ reading is a *third*
normalization: write the overlap exponent as ``-κ(G) / g²`` and
adopt the value of κ that makes this match ``C_2(λ_min)``.  See
`notes/heat-kernel-normalization.md` §3 for the derivation.

Status: each convention is documented here as a separate
function; downstream milestones (3.1 onwards) consume the
convention they need with the name explicit.  Conventions are
NOT silently mixed.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from enum import Enum
from fractions import Fraction
from typing import Final


class HeatKernelConvention(Enum):
    """The three heat-kernel-normalization conventions carried by 1.2."""

    WILSON = "wilson"
    """``t = 2 N / g²``; bound exponent picks up the factor ``2N``.

    Effective overlap-bound exponent coefficient (in ``exp(-κ / g²)``
    form): ``2 N · C_2(λ_min)``.  For SU(2): ``2·2·(3/4) = 3``.
    """

    MANTON = "manton"
    """``t = g² / (2 N)``; bound has shape ``exp(-c · g²)``, NOT ``exp(-κ / g²)``.

    The Manton diffusion-time convention flips the g-dependence: the
    polymer activity is ``exp(-t · C_2)`` with ``t ∝ g²``, so the
    coefficient ``c = C_2(λ_min) / (2N)`` multiplies ``g²``, not
    ``1/g²``.  ``kappa_from_casimir`` therefore does NOT apply
    cleanly to Manton at the ``exp(-κ / g²)`` form; use
    ``manton_exponent_coefficient`` instead.
    """

    CANONICAL = "canonical"
    """``κ = C_2(λ_min)`` directly; the normalization of
    `outline.md` §18.5 and `context.md` §3.4 / §18.1.

    No factor of ``2N``.  For SU(2): ``κ = C_2(1/2) = 3/4``.  This
    is a *choice of identification*, not a derivation: it picks
    the rescaling of ``t`` that makes the overlap exponent read
    as a pure representation-theoretic constant.  Matches outline
    verbatim and is the recommended convention for Phase-3
    Lean / Python interoperation.
    """


# --------------------------------------------------------------------------
# t ↔ g conversion
# --------------------------------------------------------------------------


def wilson_t_from_g(g: float, N: int) -> float:
    """The Wilson identification of heat-kernel time with coupling.

    ``t_W = 2 N / g²``: large t ↔ weak coupling, matching the
    Wilson β = 2N/g².  Requires ``g > 0`` and ``N ≥ 1``.
    """
    if g <= 0:
        raise ValueError(f"coupling g must be positive; got {g}")
    if N < 1:
        raise ValueError(f"gauge-group rank N must be ≥ 1; got {N}")
    return 2.0 * N / (g * g)


def wilson_g_from_t(t: float, N: int) -> float:
    """Invert ``wilson_t_from_g``: ``g = sqrt(2N / t)``."""
    if t <= 0:
        raise ValueError(f"heat-kernel time t must be positive; got {t}")
    if N < 1:
        raise ValueError(f"gauge-group rank N must be ≥ 1; got {N}")
    return math.sqrt(2.0 * N / t)


def manton_t_from_g(g: float, N: int) -> float:
    """The Manton diffusion-time identification.

    ``t_M = g² / (2 N)``: small t ↔ weak (narrow-fluctuation)
    coupling, the natural reading of the heat kernel as a
    diffusion process on the group.  Reciprocal of Wilson.
    """
    if g <= 0:
        raise ValueError(f"coupling g must be positive; got {g}")
    if N < 1:
        raise ValueError(f"gauge-group rank N must be ≥ 1; got {N}")
    return (g * g) / (2.0 * N)


def manton_g_from_t(t: float, N: int) -> float:
    """Invert ``manton_t_from_g``: ``g = sqrt(2N · t)``."""
    if t <= 0:
        raise ValueError(f"heat-kernel time t must be positive; got {t}")
    if N < 1:
        raise ValueError(f"gauge-group rank N must be ≥ 1; got {N}")
    return math.sqrt(2.0 * N * t)


# --------------------------------------------------------------------------
# κ-from-Casimir, per work_plan §1.2's required signature
# --------------------------------------------------------------------------


def kappa_from_casimir(
    C_2_min: float, N: int, t_choice: HeatKernelConvention
) -> float:
    """Effective ``κ(G)`` in the overlap bound ``μ ≤ ... · exp(-κ / g²) ...``.

    Per the convention chosen via ``t_choice``:

    * ``WILSON`` — returns ``2 N · C_2_min`` (the bound exponent
      coefficient in ``exp(-κ / g²)`` form).
    * ``MANTON`` — raises ``ValueError`` because Manton's bound is
      in ``exp(-c · g²)`` form, not ``exp(-κ / g²)``; the user
      should call ``manton_exponent_coefficient`` instead.  The
      function refuses rather than silently returning a misleading
      value.
    * ``CANONICAL`` — returns ``C_2_min`` directly, matching
      `outline.md` §18.5's ``κ_{SU(2)} = 3/4``.
    """
    if C_2_min <= 0:
        raise ValueError(f"C_2_min must be positive; got {C_2_min}")
    if N < 1:
        raise ValueError(f"gauge-group rank N must be ≥ 1; got {N}")
    if t_choice is HeatKernelConvention.WILSON:
        return 2.0 * N * C_2_min
    if t_choice is HeatKernelConvention.MANTON:
        raise ValueError(
            "Manton convention has bound shape exp(-c · g²), not exp(-κ / g²); "
            "call `manton_exponent_coefficient` instead."
        )
    if t_choice is HeatKernelConvention.CANONICAL:
        return float(C_2_min)
    raise ValueError(f"unknown convention: {t_choice!r}")


def manton_exponent_coefficient(C_2_min: float, N: int) -> float:
    """The Manton-convention coefficient ``c`` in ``exp(-c · g²)``.

    In Manton, ``t = g²/(2N)`` and the activity ``exp(-t · C_2)``
    becomes ``exp(-(C_2/(2N)) · g²)``.  So ``c = C_2_min / (2N)``.
    For SU(2) with ``C_2(1/2) = 3/4``: ``c = 3/16``.
    """
    if C_2_min <= 0:
        raise ValueError(f"C_2_min must be positive; got {C_2_min}")
    if N < 1:
        raise ValueError(f"gauge-group rank N must be ≥ 1; got {N}")
    return C_2_min / (2.0 * N)


# --------------------------------------------------------------------------
# Exact rational form, for downstream Lean-Q' interop (Milestone 3.0 hook)
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class KappaExactRational:
    """The κ value as an exact rational (Fraction), per convention.

    For canonical: κ = C_2_min (exact ℚ).
    For Wilson: κ = 2N · C_2_min (exact ℚ).
    For Manton: ``None`` (different bound shape, no κ in this form).

    Used by 3.0+ to feed exact constants into the Lean ``Q'`` value
    type, avoiding floating-point drift.
    """

    convention: HeatKernelConvention
    kappa: Fraction | None
    """The κ value, or ``None`` if Manton (no exp(-κ/g²) shape)."""


def kappa_from_casimir_exact(
    C_2_min: Fraction, N: int, t_choice: HeatKernelConvention
) -> KappaExactRational:
    """Exact-rational version of `kappa_from_casimir` for Lean interop.

    Operates on ``Fraction`` rather than ``float``; output κ is also
    ``Fraction`` (or ``None`` for Manton).
    """
    if C_2_min <= 0:
        raise ValueError(f"C_2_min must be positive; got {C_2_min}")
    if N < 1:
        raise ValueError(f"gauge-group rank N must be ≥ 1; got {N}")
    if t_choice is HeatKernelConvention.WILSON:
        return KappaExactRational(t_choice, 2 * N * C_2_min)
    if t_choice is HeatKernelConvention.MANTON:
        return KappaExactRational(t_choice, None)
    if t_choice is HeatKernelConvention.CANONICAL:
        return KappaExactRational(t_choice, C_2_min)
    raise ValueError(f"unknown convention: {t_choice!r}")


# --------------------------------------------------------------------------
# SU(2)-specific spot values (consumed by Milestones 3.1+)
# --------------------------------------------------------------------------

C_2_SU2_FUNDAMENTAL: Final[Fraction] = Fraction(3, 4)
"""``C_2(1/2) = 3/4`` for SU(2), the smallest nonzero Casimir.

Mirror of `computations.su2_representations.Irrep.from_spin(Fraction(1,2)).casimir_symbolic`,
exposed here as a ``Fraction`` for exact downstream conversions.
"""

N_SU2: Final[int] = 2

KAPPA_SU2_WILSON: Final[Fraction] = Fraction(2 * N_SU2) * C_2_SU2_FUNDAMENTAL
"""SU(2) κ in the Wilson convention: ``2 N · C_2(1/2) = 3``."""

KAPPA_SU2_CANONICAL: Final[Fraction] = C_2_SU2_FUNDAMENTAL
"""SU(2) κ in the canonical convention: ``C_2(1/2) = 3/4``.

This is the value `outline.md` §18.5 quotes verbatim:
``μ ≤ ... · exp(-3 / (4 g²)) · g³``.
"""

MANTON_COEFF_SU2: Final[Fraction] = C_2_SU2_FUNDAMENTAL / (2 * N_SU2)
"""SU(2) Manton coefficient ``c`` in ``exp(-c · g²)``: ``C_2(1/2) / (2N) = 3/16``."""
