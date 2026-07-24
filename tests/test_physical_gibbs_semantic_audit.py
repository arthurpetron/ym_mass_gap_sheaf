"""Regression pin for the physical Gibbs semantic mismatch."""

from fractions import Fraction

from computations.physical_gibbs_semantic_audit import (
    smallest_four_cube_semantic_mismatch,
)


def test_multiplicity_product_is_not_the_exact_haar_amplitude() -> None:
    mismatch = smallest_four_cube_semantic_mismatch()
    assert mismatch.validates()
    assert mismatch.encoding == (0x6F6D9E, 0x21)
    assert len(mismatch.edge_multiplicities) == 32
    assert set(mismatch.edge_multiplicities) == {1}
    assert mismatch.multiplicity_product == 1
    assert mismatch.exact_haar_amplitude == Fraction(-1, 196608)
