"""Pins for the DP.6-U1 abelian discriminator on the DP.2 slab."""

from fractions import Fraction

from computations.dp6_u1_slab_blocking import (
    build_kernel,
    certify_kernel_basis,
    kernel_entry_2d_gate_u1,
    kernel_entry_frozen_u1,
    kernel_entry_u1,
    kernel_entry_u1_tiles,
    measure,
)

Fr = Fraction


def test_lattice_certificate():
    # rank-16 free-edge constraints; cube-flip basis saturated (Smith 1,1,1,1)
    assert certify_kernel_basis()


def test_2d_open_disk_gate():
    # top tiles + loop only: c'_n = s^{4 n^2} = c_n^4 exactly (d = 1)
    assert kernel_entry_2d_gate_u1(0, 3) == {0: Fr(1)}
    assert kernel_entry_2d_gate_u1(1, 3) == {4: Fr(1)}
    assert kernel_entry_2d_gate_u1(2, 3) == {16: Fr(1)}


def test_frozen_side_univalence_exact_2d():
    # perimeter walls frozen -> every cube flip dies -> exact 2D rule
    assert kernel_entry_frozen_u1(1, 1, 4) == {8: Fr(1)}
    assert kernel_entry_frozen_u1(0, 2, 4) == {16: Fr(1)}
    assert kernel_entry_frozen_u1(2, 2, 4) == {32: Fr(1)}


def test_owned_boundary_entries_M1():
    # abelian owned-boundary kernel at truncation 1 (exact counts)
    assert kernel_entry_u1(1, 1, 1) == {8: Fr(1)}
    assert kernel_entry_u1(1, -1, 1) == {8: Fr(2), 10: Fr(12), 12: Fr(2)}
    assert kernel_entry_u1(0, 0, 1) == {
        0: Fr(1), 6: Fr(8), 10: Fr(8), 12: Fr(8), 14: Fr(8), 16: Fr(2)}
    # abelian rigidity: charge-2 loops unreachable at |k| <= 1 (no fusion
    # freedom: SU(2)'s (1,1,2) triad has no abelian counterpart)
    assert kernel_entry_u1(2, 2, 1) == {}


def test_owned_boundary_T22_M2():
    # the pure 2D term is the ONLY charge-2/2 config at truncation 2
    assert kernel_entry_u1(2, 2, 2) == {32: Fr(1)}


def test_independent_tile_sweep_cross_check():
    # c-lattice enumeration == direct tile sweep with full 33-edge
    # charge conservation (independent parametrization + constraint)
    for n in (-2, -1, 0, 1, 2):
        for m in (-1, 0, 2):
            assert kernel_entry_u1(n, m, 2) == kernel_entry_u1_tiles(n, m, 2)


def test_symmetries():
    T = build_kernel(2, 2)
    for n in range(-2, 3):
        for m in range(-2, 3):
            assert T[(n, m)] == T[(-n, -m)]  # charge conjugation
            assert T[(n, m)] == T[(m, n)]    # z-flip


def test_headline_deviation_exact():
    # the discriminator headline: owned-boundary U(1) does NOT track the
    # 2D rule; exact witness at M = 2, s = 1/2
    T = build_kernel(2, 2)
    r = measure(T, 2, Fr(1, 2))
    assert r["sector"] == [-2, -1, 0, 1, 2]
    assert r["v"][0] == Fr(11258810062447479809, 9223372036854775808)
    assert r["v"][1] == Fr(437335326546529, 4503599627370496)
    assert r["ratios"][1] == Fr(14330603980276662272, 11258810062447479809)
    assert r["ratios"][1] > 1  # ANTI-renormalization: s' > s^4
    assert r["ratios"][2] == Fr(148520413760355041280, 11258810062447479809)


def test_truncation_min_degree_gap():
    from computations.dp6_u1_slab_blocking import truncation_min_degree_gap

    # all monomials of degree < (M+1)^2 exactly stable under M -> M+1
    assert truncation_min_degree_gap(2, 1) == 12  # >= 4
    assert truncation_min_degree_gap(2, 2) == 26  # >= 9
