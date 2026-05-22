"""SU(2) irreducible representations: dimensions, Casimirs, characters.

This module is the implementation half of Milestone 1.1 of
`work_plan.md`. The argument is in `notes/su2-representations.md`.

The deliverables required by the work plan are:

- Irrep enumeration by half-integer spin up to a cutoff ``j_max``.
- Dimension ``d_j = 2j + 1`` and quadratic Casimir ``C_2(j) = j(j + 1)``
  returned both as ``sympy`` expressions and as floating-point values.
- A symbolic verification of ``C_2(1/2) = 3/4``.
- The character ``chi_j(theta) = sin((2j+1) theta / 2) / sin(theta / 2)``
  on the maximal torus.
- A numerical verification of character orthogonality.
- The figure ``visualizations/pilot/su2/casimir-spectrum.svg``.

Killing-form / Casimir normalization
------------------------------------

The SU(2) Casimir spectrum depends on the normalization of the
Killing form. There is a factor-of-2N ambiguity in the literature
between the *trace form on the fundamental* and the genuine *Killing
form* ``B(X, Y) = -tr_adj(ad_X ad_Y)``. This module commits to the
**physics-spin convention** (convention "A" in the companion note):

- Generators ``T_a = sigma_a / 2`` (Pauli matrices), satisfying
  ``[T_a, T_b] = i epsilon_{abc} T_c`` and
  ``tr(T_a T_b) = (1/2) delta_{ab}`` on the fundamental.
- The Laplace-Beltrami operator on SU(2) (with respect to the
  bi-invariant metric induced by ``-tr(. .)`` on ``su(2)``) acts on
  the spin-j irrep by ``C_2(j) = j(j + 1)``.

In particular:

    C_2(0)   = 0
    C_2(1/2) = 3/4   <-- the smallest nonzero Casimir
    C_2(1)   = 2
    C_2(3/2) = 15/4
    C_2(2)   = 6

This is the convention quoted in ``docs/outline.md`` §18.1 and
``docs/context.md`` §7. Other conventions (full Killing form;
dual-Coxeter normalization) differ by an overall factor of ``2N = 4``
or ``2``; see ``notes/su2-representations.md`` §1 for the table.

When wiring this Casimir into the heat-kernel formula

    K_t(g) = sum_lambda d_lambda chi_lambda(g) exp(-t C_2(lambda)),

the choice ``t = t(g)`` absorbs the convention. Milestone 1.2 closes
that conversion explicitly.

Maximal-torus convention
------------------------

A conjugacy class in SU(2) has a unique representative

    t(theta) = diag(exp(i theta / 2), exp(-i theta / 2)),
    theta in [0, 2 pi],

so that ``tr t(theta) = 2 cos(theta / 2)`` runs over ``[-2, 2]``.
The Weyl integration formula is

    int_SU(2) f(g) dg = (1 / pi) int_0^{2 pi} f(theta) sin^2(theta / 2) d theta,

and the character of the spin-j irrep is

    chi_j(theta) = sin((2j + 1) theta / 2) / sin(theta / 2).

For ``j = 0`` this is the constant 1. The apparent singularity at
``theta = 0`` removes by L'Hopital: ``chi_j(0) = d_j = 2j + 1``.

Constructive law
----------------

Verification routines return the witnessing object, never a bare
boolean. For ``C_2(1/2) = 3/4`` the witness is the simplified sympy
expression ``C_2(1/2) - 3/4``, which is ``sympy.S.Zero`` by
construction; for orthogonality the witness is the Gram matrix and
its sup-norm deviation from the identity.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any

import numpy as np
import scipy.integrate
import sympy
from numpy.typing import NDArray

# sympy ships no type stubs; treat its expressions as Any with a named alias
# so that signatures read clearly.
SymExpr = Any

# Convention tag for downstream sanity checks.
KILLING_FORM_CONVENTION: str = "physics_spin"

DEFAULT_J_MAX: Fraction = Fraction(5)
DEFAULT_FIGURE_PATH: Path = (
    Path(__file__).resolve().parent.parent
    / "visualizations"
    / "pilot"
    / "su2"
    / "casimir-spectrum.svg"
)


@dataclass(frozen=True)
class Irrep:
    """One SU(2) irreducible representation, indexed by spin ``j``.

    All four numerical/symbolic witnesses are stored on construction
    so the dataclass is the object returned by an existence claim
    ("there is a spin-j irrep with these data"), not a flag.
    """

    j: Fraction
    dimension_symbolic: SymExpr
    dimension_float: float
    casimir_symbolic: SymExpr
    casimir_float: float

    @classmethod
    def from_spin(cls, j: Fraction) -> Irrep:
        """Construct the spin-``j`` irrep, populating all witness fields."""
        if j < 0:
            raise ValueError(f"spin must be non-negative; got j = {j}")
        if (2 * j).denominator != 1:
            raise ValueError(
                f"spin must be a half-integer (2j in Z); got 2j = {2 * j}"
            )
        j_sym = sympy.Rational(j.numerator, j.denominator)
        d_sym = 2 * j_sym + 1
        c_sym = j_sym * (j_sym + 1)
        return cls(
            j=j,
            dimension_symbolic=d_sym,
            dimension_float=float(d_sym),
            casimir_symbolic=c_sym,
            casimir_float=float(c_sym),
        )

    def character_symbolic(self, theta: SymExpr) -> SymExpr:
        """Return chi_j(theta) = sin((2j+1) theta / 2) / sin(theta / 2)."""
        d = self.dimension_symbolic
        return sympy.sin(d * theta / 2) / sympy.sin(theta / 2)

    def character(self, theta: float) -> float:
        """Numerical chi_j(theta), using ``chi_j(0) = d_j`` (L'Hopital).

        The apparent singularities at ``theta`` in ``{0, 2*pi}`` are
        removable. The float branch handles them explicitly so we
        never divide a numerical zero.
        """
        d = self.dimension_float
        s_half = float(np.sin(theta / 2.0))
        if abs(s_half) < 1e-14:
            # sin(d theta / 2) / sin(theta / 2) -> d as theta -> 0 (mod 4 pi).
            return d
        return float(np.sin(d * theta / 2.0) / s_half)


def enumerate_irreps(j_max: Fraction = DEFAULT_J_MAX) -> list[Irrep]:
    """Enumerate spin-``j`` irreps for ``j in {0, 1/2, 1, ..., j_max}``."""
    if j_max < 0:
        raise ValueError(f"j_max must be non-negative; got {j_max}")
    two_j_max = 2 * j_max
    if two_j_max.denominator != 1:
        raise ValueError(
            f"j_max must be a half-integer; got 2*j_max = {two_j_max}"
        )
    n = int(two_j_max.numerator)
    return [Irrep.from_spin(Fraction(k, 2)) for k in range(n + 1)]


def verify_casimir_one_half() -> SymExpr:
    """Return the sympy witness for ``C_2(1/2) = 3/4``.

    The witness is the simplified expression ``C_2(1/2) - 3/4``, which
    is ``sympy.S.Zero`` by construction. We never return ``True`` or
    ``1`` from a verification call (constructive-law policy).
    """
    half = Irrep.from_spin(Fraction(1, 2))
    return sympy.simplify(half.casimir_symbolic - sympy.Rational(3, 4))


def _orthogonality_integrand(
    theta: float, irrep_i: Irrep, irrep_j: Irrep
) -> float:
    """Integrand of ``pi * <chi_i, chi_j>``.

    The Weyl factor ``sin^2(theta / 2)`` cancels the ``sin(theta / 2)``
    in each character denominator, leaving the smooth function
    ``sin(d_i theta / 2) * sin(d_j theta / 2)`` (no removable
    singularity). Quadrature is thereby conditioned only by its own
    floating-point error.
    """
    d_i = irrep_i.dimension_float
    d_j = irrep_j.dimension_float
    return float(np.sin(d_i * theta / 2.0) * np.sin(d_j * theta / 2.0))


def character_inner_product(
    irrep_i: Irrep, irrep_j: Irrep
) -> tuple[float, float]:
    """Compute ``<chi_i, chi_j>`` together with the quadrature error.

    The inner product is

        <chi_i, chi_j>
            = (1 / pi) * int_0^{2 pi} sin(d_i theta / 2) sin(d_j theta / 2) d theta

    after cancelling the ``sin(theta / 2)`` factors. The return value
    is ``(value, estimated_error)``: both are witnesses, not flags.
    """
    value, error = scipy.integrate.quad(
        _orthogonality_integrand,
        0.0,
        2.0 * np.pi,
        args=(irrep_i, irrep_j),
        epsabs=1e-12,
        epsrel=1e-12,
        limit=200,
    )
    return float(value / np.pi), float(error / np.pi)


def character_orthogonality_matrix(
    irreps: list[Irrep],
) -> tuple[NDArray[np.float64], float]:
    """Build the Gram matrix ``M_{ij} = <chi_i, chi_j>`` and its deviation.

    By Schur orthogonality ``M`` must be the identity. The witness is
    the pair ``(M, ||M - I||_inf)``; the second component is the
    explicit modulus of constructive verification.
    """
    n = len(irreps)
    matrix: NDArray[np.float64] = np.zeros((n, n), dtype=np.float64)
    for i, irrep_i in enumerate(irreps):
        for k, irrep_k in enumerate(irreps):
            value, _ = character_inner_product(irrep_i, irrep_k)
            matrix[i, k] = value
    deviation = float(np.max(np.abs(matrix - np.eye(n))))
    return matrix, deviation


def _format_spin_label(j: Fraction) -> str:
    if j.denominator == 1:
        return str(j.numerator)
    return f"{j.numerator}/{j.denominator}"


def plot_casimir_spectrum(
    j_max: Fraction = DEFAULT_J_MAX,
    output_path: Path = DEFAULT_FIGURE_PATH,
) -> Path:
    """Render the Milestone 1.1 figure to ``output_path`` and return it.

    The figure shows ``C_2(j) = j(j + 1)`` as discrete markers for
    ``j in {0, 1/2, 1, ..., j_max}``, highlighting ``C_2(1/2) = 3/4``
    as the smallest nonzero Casimir (the "spectral gap" referenced in
    ``docs/outline.md`` §18.1).
    """
    import matplotlib

    matplotlib.use("Agg")  # ensure headless rendering in CI / scripts
    import matplotlib.pyplot as plt

    irreps = enumerate_irreps(j_max)
    js = np.array([float(r.j) for r in irreps], dtype=np.float64)
    cs = np.array([r.casimir_float for r in irreps], dtype=np.float64)

    fig, ax = plt.subplots(figsize=(6.0, 4.0))
    ax.plot(
        js,
        cs,
        "o-",
        color="tab:blue",
        markersize=6,
        linewidth=1.0,
        label=r"$C_2(j) = j(j+1)$",
    )

    # Highlight C_2(1/2) = 3/4 as the smallest nonzero Casimir.
    half_idx = next(i for i, r in enumerate(irreps) if r.j == Fraction(1, 2))
    ax.plot(
        [js[half_idx]],
        [cs[half_idx]],
        "o",
        color="tab:red",
        markersize=12,
        zorder=5,
        label=r"$C_2(1/2) = 3/4$  (smallest nonzero)",
    )
    ax.annotate(
        r"gap $= 3/4$",
        xy=(js[half_idx], cs[half_idx]),
        xytext=(1.2, 4.5),
        arrowprops={"arrowstyle": "->", "color": "tab:red", "lw": 1.0},
        fontsize=11,
        color="tab:red",
    )

    ax.set_xticks(js)
    ax.set_xticklabels([_format_spin_label(r.j) for r in irreps])
    ax.set_xlabel(r"spin $j$")
    ax.set_ylabel(r"quadratic Casimir $C_2(j)$")
    ax.set_title(r"SU(2) Casimir spectrum")
    ax.grid(True, alpha=0.3)
    ax.legend(loc="upper left")
    fig.tight_layout()

    output_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output_path, format="svg")
    plt.close(fig)
    return output_path


def _print_summary() -> None:
    irreps = enumerate_irreps()
    print(
        f"Enumerated {len(irreps)} SU(2) irreps "
        f"(j = 0 .. {DEFAULT_J_MAX}, convention: {KILLING_FORM_CONVENTION})"
    )
    for r in irreps:
        label = _format_spin_label(r.j)
        print(
            f"  j = {label:>6}   d_j = {int(r.dimension_float):>3}   "
            f"C_2 = {r.casimir_symbolic}"
        )
    witness = verify_casimir_one_half()
    print(f"\nC_2(1/2) - 3/4 = {witness}   (sympy.S.Zero)")
    _, deviation = character_orthogonality_matrix(irreps)
    print(f"||<chi_i, chi_j> - I||_inf = {deviation:.3e}")
    out = plot_casimir_spectrum()
    print(f"Figure written to {out}")


if __name__ == "__main__":
    _print_summary()
