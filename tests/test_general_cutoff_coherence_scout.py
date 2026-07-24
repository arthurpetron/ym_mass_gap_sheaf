"""Regression pins for the all-cutoff stretched-channel obstruction."""

from computations.general_cutoff_coherence_scout import (
    minimal_stretched_coherence_counterexample,
)


def test_single_cube_stretched_target_is_not_link_coherent() -> None:
    witness = minimal_stretched_coherence_counterexample()
    assert witness.validates()
    assert witness.coarse_extent == 1
    assert witness.fine_extent == 3
    assert witness.fine_cutoff == 1
    assert witness.coarse_cutoff == 4
    assert witness.cube_base == (0, 0, 1, 1)
    assert witness.cube_directions == (0, 2, 3)
    assert witness.coarse_nonzero_faces == (
        (((0, 0, 0, 0), (2, 3)), 2),
    )
    assert witness.bad_coarse_links == (
        ((0, 0, 0, 0), 2),
        ((0, 0, 0, 0), 3),
        ((0, 0, 0, 1), 2),
        ((0, 0, 1, 0), 3),
    )
