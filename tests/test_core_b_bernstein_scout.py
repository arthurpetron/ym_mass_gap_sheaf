import sympy as sp

from computations.core_b_bernstein_scout import (
    bernstein_certificate,
    bernstein_reconstruction,
    canonical_cell_quotient,
    canonical_cumulative_quotient,
    canonical_high_degree,
    cleared_unnormalized_bernstein_row,
    direct_cleared_unnormalized_bernstein_row,
    pascal_degree_elevate,
    power_to_bernstein,
    predicted_cell_zero_order,
    predicted_pascal_step_direction,
    signed_pascal_step_difference,
    u_symbol,
    verify_cellwise_bernstein,
    verify_direct_integer_rows,
    verify_pascal_step_unimodality,
)


def test_power_to_bernstein_exact_reconstruction() -> None:
    polynomial = sp.Poly(
        3 + 2 * u_symbol + 5 * u_symbol**2 + 7 * u_symbol**4,
        u_symbol,
        domain=sp.QQ,
    )
    coefficients = power_to_bernstein(polynomial)
    assert bernstein_reconstruction(coefficients) == polynomial


def test_first_cell_matches_exact_known_positive_factor() -> None:
    quotient = canonical_cell_quotient(1, 0)
    expected = sp.Poly(
        sp.Rational(3, 2**28)
        * (u_symbol / 4) ** 11
        * (
            83540 * (u_symbol / 4) ** 4
            + 50832 * (u_symbol / 4) ** 3
            + 12708 * (u_symbol / 4) ** 2
            + 22540 * (u_symbol / 4)
            + 254283
        ),
        u_symbol,
        domain=sp.QQ,
    )
    assert quotient == expected
    certificate = bernstein_certificate(quotient)
    assert certificate.zero_order == 11
    assert certificate.reconstruction_exact
    assert certificate.strictly_positive


def test_cellwise_exact_bernstein_grid() -> None:
    assert verify_cellwise_bernstein(8)
    for length in range(1, 9):
        cumulative = bernstein_certificate(
            canonical_cumulative_quotient(length)
        )
        assert cumulative.reconstruction_exact
        assert cumulative.strictly_positive
        assert canonical_high_degree(length) == (length + 2) * (length + 4)
        for step in range(length):
            assert (
                bernstein_certificate(
                    canonical_cell_quotient(length, step)
                ).zero_order
                == predicted_cell_zero_order(length, step)
            )
            converted_row = cleared_unnormalized_bernstein_row(
                length, step
            )
            assert (
                direct_cleared_unnormalized_bernstein_row(length, step)
                == converted_row
            )
            assert all(
                coefficient > 0
                for coefficient in converted_row
            )


def test_direct_actual_atom_integer_row_extended_grid() -> None:
    assert verify_direct_integer_rows(12)


def test_pascal_degree_elevation_exact_identity() -> None:
    row = (3, -2, 5)
    elevated = pascal_degree_elevate(row, 4)
    original_degree = len(row) - 1
    elevated_degree = len(elevated) - 1
    original = sp.Poly(
        sp.expand(
            sum(
                coefficient
                * u_symbol**index
                * (1 - u_symbol) ** (original_degree - index)
                for index, coefficient in enumerate(row)
            )
        ),
        u_symbol,
        domain=sp.QQ,
    )
    reconstructed = sp.Poly(
        sp.expand(
            sum(
                coefficient
                * u_symbol**index
                * (1 - u_symbol) ** (elevated_degree - index)
                for index, coefficient in enumerate(elevated)
            )
        ),
        u_symbol,
        domain=sp.QQ,
    )
    assert reconstructed == original


def test_actual_rows_are_pascal_unimodal_on_exact_grid() -> None:
    assert verify_pascal_step_unimodality(10)
    for length in range(2, 11):
        center, parity = divmod(length, 2)
        for step in range(length - 1):
            expected_direction = (
                1
                if (
                    (parity == 0 and step < center - 1)
                    or (parity == 1 and step < center)
                )
                else -1
            )
            assert (
                predicted_pascal_step_direction(length, step)
                == expected_direction
            )
            assert all(
                coefficient > 0
                for coefficient in signed_pascal_step_difference(
                    length, step
                )
            )
