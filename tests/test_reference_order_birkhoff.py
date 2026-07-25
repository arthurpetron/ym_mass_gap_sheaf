"""Exact regression gates for the corrected BF4 reference-order cone."""

from fractions import Fraction

from computations.reference_order_birkhoff import (
    RationalMatrix,
    ReferenceOrderEnvelope,
    bf4_reference_cone_frontier,
    centered_reference_remainder,
    heat_trace_cone_interior_collapse,
    reference_order_envelope,
    trace_small_order_large_witness,
)


def _alternating_envelope(dimension: int) -> ReferenceOrderEnvelope:
    reference = tuple(
        tuple(
            Fraction(int(row == column), dimension)
            for column in range(dimension)
        )
        for row in range(dimension)
    )
    first_diagonal = tuple(
        Fraction(1, 2) if index % 2 == 0 else Fraction(3, 2)
        for index in range(dimension)
    )
    second_diagonal = tuple(reversed(first_diagonal))

    def diagonal(values: tuple[Fraction, ...]) -> RationalMatrix:
        return tuple(
            tuple(
                values[row] / dimension if row == column else Fraction(0)
                for column in range(dimension)
            )
            for row in range(dimension)
        )

    return reference_order_envelope(
        reference,
        (diagonal(first_diagonal), diagonal(second_diagonal)),
        Fraction(1, 2),
        Fraction(3, 2),
    )


def test_reference_order_envelope_gives_exact_dimension_free_rate() -> None:
    certificate = reference_order_envelope(
        (
            (Fraction(1, 2), 0),
            (0, Fraction(1, 2)),
        ),
        (
            (
                (Fraction(2, 3), 0),
                (0, Fraction(1, 3)),
            ),
            (
                (Fraction(1, 3), 0),
                (0, Fraction(2, 3)),
            ),
        ),
        Fraction(2, 3),
        Fraction(4, 3),
    )

    assert certificate.validates()
    assert certificate.projective_spread == 2
    assert certificate.birkhoff_rate_bound == Fraction(1, 3)
    assert certificate.dimension_free_formula


def test_the_same_formula_is_independent_of_matrix_dimension() -> None:
    certificates = tuple(_alternating_envelope(size) for size in (2, 4, 10))

    assert all(certificate.validates() for certificate in certificates)
    assert {
        certificate.birkhoff_rate_bound for certificate in certificates
    } == {Fraction(1, 2)}


def test_heat_reference_trace_cone_interior_radius_collapses() -> None:
    witnesses = tuple(
        heat_trace_cone_interior_collapse(Fraction(1, 2), cutoff)
        for cutoff in range(1, 8)
    )

    assert all(witness.validates() for witness in witnesses)
    distances = tuple(
        witness.trace_distance_to_nonpositive for witness in witnesses
    )
    assert distances == tuple(sorted(distances, reverse=True))
    assert len(set(distances)) == len(distances)
    assert all(witness.perturbed_eigenvalue < 0 for witness in witnesses)


def test_centered_relative_order_remainder_is_the_birkhoff_rate() -> None:
    certificate = centered_reference_remainder(
        (
            (Fraction(1, 2), 0),
            (0, Fraction(1, 2)),
        ),
        (
            (
                (Fraction(2, 3), 0),
                (0, Fraction(1, 3)),
            ),
            (
                (Fraction(1, 3), 0),
                (0, Fraction(2, 3)),
            ),
        ),
        Fraction(1, 3),
    )

    assert certificate.validates()
    assert certificate.mass_preserving
    assert certificate.relative_order_bound == Fraction(1, 3)
    assert certificate.envelope.lower == Fraction(2, 3)
    assert certificate.envelope.upper == Fraction(4, 3)
    assert certificate.envelope.birkhoff_rate_bound == Fraction(1, 3)
    assert not certificate.universal_physical_input_bound


def test_trace_norm_can_vanish_while_relative_order_stays_one() -> None:
    witnesses = tuple(
        trace_small_order_large_witness(Fraction(1, 2), cutoff)
        for cutoff in range(1, 8)
    )

    assert all(witness.validates() for witness in witnesses)
    assert {
        witness.relative_order_norm for witness in witnesses
    } == {Fraction(1)}
    trace_norms = tuple(witness.trace_norm for witness in witnesses)
    assert trace_norms == tuple(sorted(trace_norms, reverse=True))
    assert len(set(trace_norms)) == len(trace_norms)


def test_bf4_is_reformulated_but_not_opened_by_the_abstract_engine() -> None:
    frontier = bf4_reference_cone_frontier()

    assert frontier.validates()
    assert frontier.reference_order_cone_required
    assert frontier.dimension_free_envelope_theorem
    assert not frontier.full_trace_cone_has_trace_norm_interior
    assert not frontier.bf31_map_positive_improving
    assert not frontier.all_label_reference_minorization_proved
    assert not frontier.fixed_distance_grouped_diameter_proved
    assert not frontier.trace_tail_implies_relative_order_tail
    assert not frontier.physical_relative_order_remainder_proved
    assert not frontier.bf32_ready_for_handoff
    assert not frontier.bf4_ready
    assert frontier.first_open_obligation == (
        "bound-physical-centered-remainder-in-relative-heat-order"
    )
