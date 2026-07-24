from fractions import Fraction

import sympy as sp

from computations.core_b_atomwise_tail_scout import (
    cubic_even_tail,
    empirical_cubic_tail_report,
    envelope_sum,
    exact_low_gap_masses,
    k_symbol,
    low_gap_certificates,
    verify_exact_low_gap_classification,
    verify_distance_formulas,
)


def test_exact_symbolic_low_gap_classification() -> None:
    k = k_symbol
    b = 2 * (k + 2) ** 3 * (k + 4) - (2 * k + 5)
    expected_even = {
        4: 16 * (k + 1) ** 3 * (k + 2) ** 2 * (k + 3) ** 3,
        8: 48 * k * (k + 1) * (k + 2) ** 4 * (k + 3) * (k + 4),
        10: 128 * k * (k + 1) ** 2 * (k + 2) ** 2 * (k + 3) ** 2 * (k + 4),
        12: 32 * k * (k + 2) ** 4 * (k + 4) * (k**2 + 4 * k + 1),
        14: (
            128
            * k
            * (k + 1)
            * (k + 2) ** 2
            * (k + 3)
            * (k + 4)
            * (k**2 + 4 * k + 1)
        ),
        16: 112 * k**2 * (k + 1) * (k + 2) ** 2 * (k + 3) * (k + 4) ** 2,
        18: 128 * (k - 1) * (k + 1) * (k + 2) ** 4 * (k + 3) * (k + 5),
        20: (
            32
            * (k + 2) ** 2
            * (
                14 * k**6
                + 168 * k**5
                + 686 * k**4
                + 1008 * k**3
                + 35 * k**2
                - 756 * k
                - 405
            )
        ),
    }
    expected_odd = {
        2: 16 * (k + 1) * (k + 2) ** 3 * (k + 3) ** 3 * (k + 4),
        4: 16 * (k + 1) * (k + 2) * (k + 3) * (k + 4) * b,
        6: 16 * (k + 1) ** 2 * (k + 2) ** 2 * (k + 3) ** 2 * (k + 4) ** 2,
        8: 24 * (k + 1) ** 2 * (k + 4) ** 2 * b,
        10: (
            16
            * (k + 2)
            * (k + 3)
            * (
                5 * k**6
                + 75 * k**5
                + 435 * k**4
                + 1225 * k**3
                + 1704 * k**2
                + 1020 * k
                + 128
            )
        ),
        12: 80 * k * (k + 2) * (k + 3) * (k + 5) * b,
        14: (
            192
            * k
            * (k + 1)
            * (k + 2) ** 2
            * (k + 3) ** 2
            * (k + 4)
            * (k + 5)
        ),
        16: 112 * k * (k + 1) * (k + 4) * (k + 5) * b,
        18: (
            128
            * k
            * (k + 2)
            * (k + 3)
            * (k + 5)
            * (2 * k**4 + 20 * k**3 + 66 * k**2 + 80 * k + 29)
        ),
        20: (
            32
            * k
            * (k + 2)
            * (k + 3)
            * (k + 5)
            * (2 * k**4 + 20 * k**3 + 64 * k**2 + 70 * k + 15)
        ),
    }
    for parity, expected in ((0, expected_even), (1, expected_odd)):
        observed = exact_low_gap_masses(parity)
        assert observed.keys() == expected.keys()
        assert all(
            sp.expand(observed[gap] - polynomial) == 0
            for gap, polynomial in expected.items()
        )
    assert verify_exact_low_gap_classification(6)


def test_exact_finite_distance_and_low_gap_candidate_checks() -> None:
    assert verify_distance_formulas(12)
    expected = {
        0: Fraction(21803, 65536),
        1: Fraction(107657, 262144),
    }
    for parity in (0, 1):
        certificates = low_gap_certificates(
            parity, maximum_gap=20, stable_start=4, validation_stop=16
        )
        assert all(certificate.validation_exact for certificate in certificates)
        assert all(certificate.prefix_overestimate for certificate in certificates)
        assert all(
            certificate.candidate_polynomial_envelope_proved
            for certificate in certificates
        )
        assert envelope_sum(certificates) == expected[parity]


def test_conditional_cubic_tail_budget_and_falsification_grid() -> None:
    assert cubic_even_tail(20) == Fraction(10061, 884736)
    assert cubic_even_tail(22) == Fraction(3311, 884736)
    low = {
        0: Fraction(21803, 65536),
        1: Fraction(107657, 262144),
    }
    for parity in (0, 1):
        report = empirical_cubic_tail_report(parity, max_k=12, first_gap=22)
        assert report.cubic_envelope_passes_checked_range
        assert low[parity] + cubic_even_tail(22) < Fraction(1, 2)
