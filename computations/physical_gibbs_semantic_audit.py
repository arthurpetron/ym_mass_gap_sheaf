"""Exact semantic audit of the multiplicity-product slab law.

The Lean corrected-slab term

    face coefficients * product(link invariant multiplicities)

is nonnegative by construction.  A genuine Haar-network coefficient also
contracts the invariant projectors through the vertices of the two-complex.
The resulting recoupling symbols need not have positive sign.

This module pins a closed four-cube assignment for which every edge
invariant multiplicity is one while the exact Haar amplitude is
``-1/196608``.  Therefore a product of invariant-space dimensions cannot, by
itself, be identified with the physical intertwiner-summed dual amplitude.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from computations.exact_haar_network import invariant_multiplicity
from computations.hypercube4d_survey import (
    AdmissibleEncoding,
    decode_assignment,
    evaluate_assignment,
    exact_constant,
    hypercube,
    vertex_sixj_product,
)


@dataclass(frozen=True)
class PhysicalGibbsSemanticMismatch:
    """One exact mismatch between local multiplicity counts and Haar value."""

    encoding: AdmissibleEncoding
    spins: tuple[int, ...]
    edge_multiplicities: tuple[int, ...]
    multiplicity_product: int
    exact_haar_amplitude: Fraction

    def validates(self) -> bool:
        complex_, faces, meta = hypercube()
        if self.spins != decode_assignment(self.encoding):
            return False
        observed_multiplicities = tuple(
            invariant_multiplicity(
                tuple(
                    self.spins[face_index]
                    for face_index, face in enumerate(faces)
                    if any(face_edge == edge for face_edge, _orientation in face)
                )
            )
            for edge in range(len(complex_.edges))
        )
        if observed_multiplicities != self.edge_multiplicities:
            return False
        product = 1
        for multiplicity in observed_multiplicities:
            product *= multiplicity
        if product != self.multiplicity_product:
            return False
        haar = exact_constant(evaluate_assignment(complex_, faces, self.spins))
        return (
            haar == self.exact_haar_amplitude
            and vertex_sixj_product(meta, self.spins) == haar
            and self.multiplicity_product > 0
            and self.exact_haar_amplitude < 0
        )


def smallest_four_cube_semantic_mismatch() -> PhysicalGibbsSemanticMismatch:
    """Return the pinned smallest-total-spin negative cutoff-two orbit."""

    encoding: AdmissibleEncoding = (0x6F6D9E, 0x21)
    spins = decode_assignment(encoding)
    complex_, faces, _meta = hypercube()
    multiplicities = tuple(
        invariant_multiplicity(
            tuple(
                spins[face_index]
                for face_index, face in enumerate(faces)
                if any(face_edge == edge for face_edge, _orientation in face)
            )
        )
        for edge in range(len(complex_.edges))
    )
    product = 1
    for multiplicity in multiplicities:
        product *= multiplicity
    mismatch = PhysicalGibbsSemanticMismatch(
        encoding=encoding,
        spins=spins,
        edge_multiplicities=multiplicities,
        multiplicity_product=product,
        exact_haar_amplitude=Fraction(-1, 196608),
    )
    if not mismatch.validates():
        raise AssertionError("the physical Gibbs semantic witness drifted")
    return mismatch


if __name__ == "__main__":
    print(smallest_four_cube_semantic_mismatch())
