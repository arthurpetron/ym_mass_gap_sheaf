"""SU(3) irreducible representations: dimensions and quadratic Casimirs.

Seed of Milestone 10.2 (`docs/su3-campaign-plan.md`), providing the SU(3)
representation data that Milestone 10.4 (the rigorous large-field character-tail
bound, `computations/su3_character_sum.py`) consumes.  This module is the SU(3)
counterpart of `computations/su2_representations.py`; it is deliberately minimal
(dimension + Casimir + spot values) and will be fleshed out under 10.2 with
characters, Weyl-formula orthogonality, and the Casimir-spectrum figure.

An SU(3) irrep is labelled by a highest weight ``(p, q)`` with ``p, q ≥ 0``
(``p`` = number of fundamental boxes, ``q`` = number of anti-fundamental boxes in
the Young-diagram convention).  In the standard quadratic-Casimir normalization
— the one that matches the SU(2) code, where ``C_2(fund) = j(j+1) = 3/4`` — the
SU(3) values are:

    dim(p, q)  =  (p+1)(q+1)(p+q+2) / 2,
    C_2(p, q)  =  (p² + q² + p q + 3p + 3q) / 3,

so that the fundamental ``(1, 0)`` has ``dim = 3``, ``C_2 = 4/3`` (the smallest
nonzero Casimir — the SU(3) analogue of ``C_2(1/2) = 3/4``), and the adjoint
``(1, 1)`` has ``dim = 8``, ``C_2 = 3 = N`` (so the one-loop coefficient is
``b_0 = (11/3) · C_2(adj) = 11``).

Dimensions are exact ``int``; Casimirs are exact ``Fraction`` — both are
ℚ′-encodable for the downstream Lean wire-in (Milestone 10.5), exactly as the
SU(2) values are.

## References

- [FultonHarris1991] W. Fulton and J. Harris, *Representation Theory: A First
  Course*, GTM 129, Springer 1991.  §13 (SU(3) irreps, Young diagrams,
  dimension formula) and §25.1 (Weyl dimension / Casimir).
- [Georgi1999] H. Georgi, *Lie Algebras in Particle Physics* (2nd ed.,
  Westview 1999), Ch. 8.  SU(3) quadratic Casimir ``C_2(p,q)`` and the
  index/Casimir normalization used here (``C_2(adj) = N``).
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction


@dataclass(frozen=True)
class Su3Irrep:
    """An SU(3) irrep by highest weight ``(p, q)`` (Dynkin labels, ``p, q ≥ 0``).

    Fields are the two non-negative Dynkin labels.  ``dimension`` and
    ``casimir`` are exact (``int`` / ``Fraction``).
    """

    p: int
    q: int

    def __post_init__(self) -> None:
        if self.p < 0 or self.q < 0:
            raise ValueError(f"SU(3) Dynkin labels must be ≥ 0; got ({self.p}, {self.q})")

    @property
    def dimension(self) -> int:
        """``dim(p, q) = (p+1)(q+1)(p+q+2) / 2`` (always an integer)."""
        return (self.p + 1) * (self.q + 1) * (self.p + self.q + 2) // 2

    @property
    def casimir(self) -> Fraction:
        """``C_2(p, q) = (p² + q² + p q + 3p + 3q) / 3`` (standard normalization)."""
        p, q = self.p, self.q
        return Fraction(p * p + q * q + p * q + 3 * p + 3 * q, 3)

    @property
    def is_trivial(self) -> bool:
        """True for the trivial irrep ``(0, 0)`` (``dim = 1``, ``C_2 = 0``)."""
        return self.p == 0 and self.q == 0

    @property
    def conjugate(self) -> Su3Irrep:
        """The complex-conjugate irrep ``(q, p)`` (same dimension and Casimir)."""
        return Su3Irrep(self.q, self.p)


# --------------------------------------------------------------------------
# Spot values (consumed by Milestones 10.4 / 10.5)
# --------------------------------------------------------------------------

FUNDAMENTAL: Su3Irrep = Su3Irrep(1, 0)
ANTIFUNDAMENTAL: Su3Irrep = Su3Irrep(0, 1)
ADJOINT: Su3Irrep = Su3Irrep(1, 1)

C_2_SU3_FUNDAMENTAL: Fraction = Fraction(4, 3)
"""``C_2(1, 0) = 4/3`` — the smallest nonzero SU(3) Casimir.

The SU(3) analogue of ``C_2_SU2_FUNDAMENTAL = 3/4`` and the small-field
spectral-gap coefficient ``c_λ`` for the SU(3) pilot.
"""

C_2_SU3_ADJOINT: Fraction = Fraction(3, 1)
"""``C_2(1, 1) = 3 = N`` — the adjoint Casimir; one-loop ``b_0 = (11/3)·3 = 11``."""

N_SU3: int = 3
"""Number of colours."""

SMALLEST_NONZERO_CASIMIR_SU3: Fraction = C_2_SU3_FUNDAMENTAL
"""The smallest nonzero SU(3) Casimir, ``4/3`` (attained by ``(1,0)`` / ``(0,1)``).

Mirror of P1.1's ``C_2(1/2) = 3/4`` for SU(2); the input that fixes the
small-field activity rate (Milestone 10.3 pilot).
"""


def irreps_in_box(p_max: int, q_max: int, *, include_trivial: bool = True) -> list[Su3Irrep]:
    """All irreps ``(p, q)`` with ``0 ≤ p ≤ p_max`` and ``0 ≤ q ≤ q_max``.

    ``include_trivial=False`` drops ``(0, 0)`` (the trivial irrep), as needed by
    the nontrivial-irrep character sum ``Z_t`` in `su3_character_sum`.
    """
    if p_max < 0 or q_max < 0:
        raise ValueError(f"p_max, q_max must be ≥ 0; got ({p_max}, {q_max})")
    out: list[Su3Irrep] = []
    for p in range(p_max + 1):
        for q in range(q_max + 1):
            if not include_trivial and p == 0 and q == 0:
                continue
            out.append(Su3Irrep(p, q))
    return out


if __name__ == "__main__":
    print("SU(3) irreps: dimension and quadratic Casimir")
    print("=" * 52)
    print(f"  {'(p,q)':>7} {'dim':>5} {'C_2':>8}")
    for irr in irreps_in_box(3, 3):
        print(f"  {f'({irr.p},{irr.q})':>7} {irr.dimension:>5} {str(irr.casimir):>8}")
    print()
    print(f"  fundamental (1,0): dim {FUNDAMENTAL.dimension}, C_2 {FUNDAMENTAL.casimir}")
    print(f"  adjoint     (1,1): dim {ADJOINT.dimension}, C_2 {ADJOINT.casimir}")
    print(f"  smallest nonzero Casimir: {SMALLEST_NONZERO_CASIMIR_SU3}")
