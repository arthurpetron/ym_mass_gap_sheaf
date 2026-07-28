"""Regression pins for the formal BF4 multicover no-go and carrier pivot."""

from computations.bf4_binary_multicover_cocircuit_scout import (
    PINNED_DISTINGUISHED_FACE,
    PINNED_NONZERO_FACES,
    gf2_rank,
    link_star_masks,
    pinned_normality_counterexample,
)
from computations.bf4_binary_multicover_normality import slab_incidence
from computations.bf4_joint_carrier_counterexample import (
    find_joint_carrier_certificate,
)


def test_pinned_positive_row_has_exact_cocircuit_obstruction() -> None:
    witness = pinned_normality_counterexample()
    incidence = slab_incidence(witness.extent)
    stars = link_star_masks(witness.support, incidence)

    assert witness.validates()
    assert len(witness.support) == 72
    assert gf2_rank(stars) == 65
    assert len(witness.sheet_masks) == 127
    assert sum(label > 0 for label in witness.labels) == 17
    assert tuple(
        face
        for face, label in zip(
            witness.support, witness.labels, strict=True
        )
        if label
    ) == PINNED_NONZERO_FACES
    assert (
        witness.support[witness.distinguished_face]
        == PINNED_DISTINGUISHED_FACE
    )
    assert witness.cut_defect() == 2


def test_joint_carrier_strictly_contains_the_no_go_row() -> None:
    certificate = find_joint_carrier_certificate()

    assert certificate.validates()
    assert all(label == 0 for _, label in certificate.coarse_labels)
    assert all(
        channel == ((0, 0), 0)
        for _, channel in certificate.face_channels
    )
    assert len(certificate.link_multiplicities) == 116
    assert all(
        multiplicity == 1
        for _, multiplicity in certificate.link_multiplicities
    )
