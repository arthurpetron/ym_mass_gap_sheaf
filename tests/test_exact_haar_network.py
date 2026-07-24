"""Independent exact-arithmetic gates for the SU(2) Haar-network core."""

import itertools
from fractions import Fraction

from computations.exact_haar_network import (
    GaugeFixedComplex,
    Quat,
    admissible,
    casimir4,
    chi,
    contract,
    dimension,
    fusion_labels,
    haar_s3_moment,
    heat_activity,
    integrate_link,
    integrate_link_linear_factors,
    invariant_multiplicity,
    p_equal_on_group,
    p_mul,
    p_scale_s,
    q_conj,
    q_link,
    q_mul,
    scalar,
    sign_on_unit_interval,
    sp_add,
    sp_eval,
    sp_mul,
    sp_pow,
)


def _constant_value(p: dict[int, Fraction]) -> Fraction:
    assert set(p).issubset({0})
    return p.get(0, Fraction(0))


def test_sparse_polynomial_arithmetic_is_exact() -> None:
    p = {0: Fraction(1, 2), 2: Fraction(3, 5)}
    q = {1: Fraction(-2, 3), 2: Fraction(1, 5)}
    assert sp_add(p, q) == {
        0: Fraction(1, 2),
        1: Fraction(-2, 3),
        2: Fraction(4, 5),
    }
    assert sp_mul(p, q) == {
        1: Fraction(-1, 3),
        2: Fraction(1, 10),
        3: Fraction(-2, 5),
        4: Fraction(3, 25),
    }
    assert sp_pow({0: Fraction(1), 1: Fraction(1)}, 3) == {
        0: Fraction(1),
        1: Fraction(3),
        2: Fraction(3),
        3: Fraction(1),
    }
    assert sp_eval(p, Fraction(1, 2)) == Fraction(13, 20)


def test_normalized_s3_moments_and_odd_vanishing() -> None:
    assert haar_s3_moment((0, 0, 0, 0)) == 1
    assert haar_s3_moment((1, 0, 0, 0)) == 0
    assert haar_s3_moment((2, 0, 0, 0)) == Fraction(1, 4)
    assert haar_s3_moment((4, 0, 0, 0)) == Fraction(1, 8)
    assert haar_s3_moment((2, 2, 0, 0)) == Fraction(1, 24)
    coordinate_squares = (
        (2, 0, 0, 0),
        (0, 2, 0, 0),
        (0, 0, 2, 0),
        (0, 0, 0, 2),
    )
    assert (
        sum(
            (haar_s3_moment(exponents) for exponents in coordinate_squares),
            start=Fraction(0),
        )
        == 1
    )


def test_link_linear_pairing_contraction_matches_generic_haar_integration() -> None:
    selected = q_link(0)
    left = q_mul(q_link(1), selected)
    right = q_mul(selected, q_link(2))
    factors = (
        left[0],
        right[0],
        left[1],
        right[1],
        left[2],
        right[2],
    )

    product = factors[0]
    for factor in factors[1:]:
        product = p_mul(product, factor)
    generic = integrate_link(product, 0)
    paired = integrate_link_linear_factors(factors, 0)
    assert p_equal_on_group(paired, generic)

    # Odd products vanish, but their link-linearity is still validated.
    assert integrate_link_linear_factors(factors[:5], 0) == {}


def test_doubled_label_fusion_conventions() -> None:
    assert dimension(3) == 4
    assert casimir4(3) == 15
    assert fusion_labels(2, 3) == (1, 3, 5)
    assert admissible(2, 3, 5)
    assert not admissible(2, 3, 4)
    assert invariant_multiplicity((1, 1, 1, 1)) == 2


def test_character_orthogonality_through_label_three() -> None:
    group = q_link(0)
    for left in range(4):
        for right in range(4):
            value = scalar(contract([p_mul(chi(left, group), chi(right, group))], [0]))
            assert _constant_value(value) == int(left == right)


def test_convolution_identity_as_group_polynomial() -> None:
    a, integrated, b = q_link(0), q_link(1), q_link(2)
    for left_label in range(3):
        for right_label in range(3):
            left = chi(left_label, q_mul(a, integrated))
            right = chi(right_label, q_mul(q_conj(integrated), b))
            actual = contract([left, right], [1])
            if left_label != right_label:
                assert p_equal_on_group(actual, {})
            else:
                expected = p_scale_s(
                    chi(left_label, q_mul(a, b)),
                    0,
                    Fraction(1, dimension(left_label)),
                )
                assert p_equal_on_group(actual, expected)


def test_heat_activity_character_projection() -> None:
    group = q_link(0)
    activity = heat_activity(group, 3)
    for label in range(4):
        projection = scalar(contract([activity, chi(label, group)], [0]))
        assert projection == {casimir4(label): Fraction(dimension(label))}


def test_honest_two_by_two_disk_heat_semigroup() -> None:
    """Four plaquette activities glue to the exact coarse-boundary heat mode."""

    def vertex(i: int, j: int) -> int:
        return 3 * i + j

    edges: list[tuple[int, int]] = []
    edge_ids: dict[tuple[int, int], int] = {}

    def edge(tail: int, head: int) -> int:
        key = tail, head
        if key not in edge_ids:
            edge_ids[key] = len(edges)
            edges.append(key)
        return edge_ids[key]

    for i in range(2):
        for j in range(3):
            edge(vertex(i, j), vertex(i + 1, j))
    for i in range(3):
        for j in range(2):
            edge(vertex(i, j), vertex(i, j + 1))
    complex_ = GaugeFixedComplex(9, edges)

    def plaquette(i: int, j: int) -> Quat:
        return complex_.holonomy_of(
            (
                (edge(vertex(i, j), vertex(i + 1, j)), 1),
                (edge(vertex(i + 1, j), vertex(i + 1, j + 1)), 1),
                (edge(vertex(i, j + 1), vertex(i + 1, j + 1)), -1),
                (edge(vertex(i, j), vertex(i, j + 1)), -1),
            )
        )

    coarse_boundary = complex_.holonomy_of(
        (
            (edge(vertex(0, 0), vertex(1, 0)), 1),
            (edge(vertex(1, 0), vertex(2, 0)), 1),
            (edge(vertex(2, 0), vertex(2, 1)), 1),
            (edge(vertex(2, 1), vertex(2, 2)), 1),
            (edge(vertex(1, 2), vertex(2, 2)), -1),
            (edge(vertex(0, 2), vertex(1, 2)), -1),
            (edge(vertex(0, 1), vertex(0, 2)), -1),
            (edge(vertex(0, 0), vertex(0, 1)), -1),
        )
    )
    cutoff = 2
    for label in range(cutoff + 1):
        factors = [heat_activity(plaquette(i, j), cutoff) for i in range(2) for j in range(2)]
        factors.append(chi(label, coarse_boundary))
        actual = complex_.contract_invariant(factors)
        expected = {4 * casimir4(label): Fraction(dimension(label))} if label else {0: Fraction(1)}
        assert actual == expected


def test_k3_character_network_collapses_exactly() -> None:
    """The triangular character network is delta_ab delta_ac / dim(a)."""

    groups = [q_link(i) for i in range(3)]
    for a, b, c in itertools.product(range(3), repeat=3):
        factors = [
            chi(a, q_mul(groups[0], q_conj(groups[1]))),
            chi(b, q_mul(groups[1], q_conj(groups[2]))),
            chi(c, q_mul(groups[2], q_conj(groups[0]))),
        ]
        actual = _constant_value(scalar(contract(factors, range(3))))
        expected = Fraction(1, dimension(a)) if a == b == c else Fraction(0)
        assert actual == expected


def test_k4_cutoff_two_is_sum_of_squares_nonnegative() -> None:
    """Falsify negativity on all 3^6 edge labels of the K4 spin model."""

    groups = [q_link(i) for i in range(4)]
    graph_edges = ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3))
    negatives: list[tuple[tuple[int, ...], Fraction]] = []
    for labels in itertools.product(range(3), repeat=len(graph_edges)):
        factors = [
            chi(
                label,
                q_mul(groups[tail], q_conj(groups[head])),
            )
            for label, (tail, head) in zip(labels, graph_edges, strict=True)
        ]
        actual = _constant_value(scalar(contract(factors, range(4))))
        if actual < 0:
            negatives.append((labels, actual))
    assert negatives == []


def test_exact_sign_classification_counts_odd_roots_only() -> None:
    assert sign_on_unit_interval({0: Fraction(1), 3: Fraction(2)}) == "positive"
    assert sign_on_unit_interval({1: Fraction(-1)}) == "negative"
    assert sign_on_unit_interval({}) == "zero"
    assert sign_on_unit_interval({0: Fraction(1), 1: Fraction(-3), 2: Fraction(1)}) == "mixed"
    # An even-multiplicity zero at s=1/2 touches zero but does not change sign.
    assert sign_on_unit_interval({0: Fraction(1), 1: Fraction(-4), 2: Fraction(4)}) == "positive"
