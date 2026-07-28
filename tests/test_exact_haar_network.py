"""Certification gates for the exact SU(2) Haar network integrator.

Every test here is an *exact identity* — no tolerances anywhere.  The
gates are chosen so that together they certify all wiring the probes
rely on: single-link moments, multi-link convolution, conjugation
(fusion), disk gluing (2D semigroup), and multi-vertex spin-model
contraction (K3 collapse, K4 sum-of-squares positivity).
"""

from fractions import Fraction

from computations.exact_haar_network import (
    P_ONE,
    chi,
    contract,
    dim,
    heat_activity,
    holonomy,
    p_mul,
    q_conj,
    q_link,
    q_mul,
    scalar,
    sign_on_unit_interval,
    sp_str,
)


def frac(sp):
    """SPoly that must be a pure rational (no s): return it as Fraction."""
    assert all(k == 0 for k in sp), f"unexpected s-dependence: {sp_str(sp)}"
    return sp.get(0, Fraction(0))


# -- Gate 1: Catalan trace moments  ∫ (tr U)^{2k} = C_k --------------------


def test_catalan_trace_moments():
    catalan = {0: 1, 1: 1, 2: 2, 3: 5, 4: 14}
    U = q_link(0)
    tr = chi(1, U)  # tr U = 2w
    for k, ck in catalan.items():
        m = dict(P_ONE)
        for _ in range(2 * k):
            m = p_mul(m, tr)
        val = frac(scalar(contract([m], [0])))
        assert val == ck, (k, val)


def test_odd_trace_moments_vanish():
    U = q_link(0)
    tr = chi(1, U)
    m = dict(P_ONE)
    for k in range(1, 6, 2):
        m = p_mul(p_mul(m, tr), tr) if k > 1 else m
        odd = p_mul(m, tr) if k == 1 else p_mul(m, tr)
    # direct: (tr U)^k for odd k
    for k in (1, 3, 5):
        m = dict(P_ONE)
        for _ in range(k):
            m = p_mul(m, tr)
        assert frac(scalar(contract([m], [0]))) == 0


# -- Gate 2: character orthogonality  ∫ chi_m chi_n = delta ----------------


def test_character_orthogonality():
    U = q_link(0)
    for m in range(0, 4):
        for n in range(0, 4):
            val = frac(scalar(contract([p_mul(chi(m, U), chi(n, U))], [0])))
            assert val == (1 if m == n else 0), (m, n, val)


# -- Gate 3: convolution  ∫ dU chi_n(AU) chi_m(U^-1 B) = δ chi_n(AB)/d_n ---


def test_convolution_identity():
    A, U, B = 0, 1, 2
    for n in range(0, 3):
        for m in range(0, 3):
            lhs = contract(
                [
                    chi(n, q_mul(q_link(A), q_link(U))),
                    chi(m, q_mul(q_conj(q_link(U)), q_link(B))),
                ],
                [U],
            )
            from computations.exact_haar_network import p_equal_on_group, p_scale_s

            if n != m:
                assert p_equal_on_group(lhs, {}), (n, m)
            else:
                rhs = p_scale_s(chi(n, q_mul(q_link(A), q_link(B))), 0, Fraction(1, dim(n)))
                assert p_equal_on_group(lhs, rhs), (n, m)


# -- Gate 4: fusion  ∫ dU chi_n(A U B U^-1) = chi_n(A) chi_n(B) / d_n ------


def test_fusion_identity():
    A, U, B = 0, 1, 2
    for n in range(0, 3):
        hol = q_mul(q_mul(q_link(A), q_link(U)), q_mul(q_link(B), q_conj(q_link(U))))
        lhs = contract([chi(n, hol)], [U])
        from computations.exact_haar_network import p_equal_on_group, p_scale_s

        rhs = p_scale_s(p_mul(chi(n, q_link(A)), chi(n, q_link(B))), 0, Fraction(1, dim(n)))
        assert p_equal_on_group(lhs, rhs), n


# -- Gate 5: 2D heat-kernel semigroup on the honest 2x2 block --------------
#
# Honest geometry (9 vertices, 12 links, 4 plaquettes), maximal-tree
# gauge.  Exact prediction for a disk of 4 plaquettes:
#     ∫ W chi_n(coarse boundary) = d_n s^{4 n(n+2)}.


def test_2d_block_semigroup():
    from computations.exact_haar_network import GaugeFixedComplex

    # vertices (i,j) -> 3*i + j, 0<=i,j<=2
    def V(i, j):
        return 3 * i + j

    edges = []
    eidx = {}

    def E(a, b):
        if (a, b) not in eidx:
            eidx[(a, b)] = len(edges)
            edges.append((a, b))
        return eidx[(a, b)]

    for i in range(2):
        for j in range(3):
            E(V(i, j), V(i + 1, j))  # horizontal
    for i in range(3):
        for j in range(2):
            E(V(i, j), V(i, j + 1))  # vertical
    cx = GaugeFixedComplex(9, edges)

    def plaq(i, j):
        return cx.holonomy_of(
            [
                (E(V(i, j), V(i + 1, j)), 1),
                (E(V(i + 1, j), V(i + 1, j + 1)), 1),
                (E(V(i, j + 1), V(i + 1, j + 1)), -1),
                (E(V(i, j), V(i, j + 1)), -1),
            ]
        )

    coarse = cx.holonomy_of(
        [
            (E(V(0, 0), V(1, 0)), 1),
            (E(V(1, 0), V(2, 0)), 1),
            (E(V(2, 0), V(2, 1)), 1),
            (E(V(2, 1), V(2, 2)), 1),
            (E(V(1, 2), V(2, 2)), -1),
            (E(V(0, 2), V(1, 2)), -1),
            (E(V(0, 1), V(0, 2)), -1),
            (E(V(0, 0), V(0, 1)), -1),
        ]
    )
    nmax = 2
    for n in range(0, nmax + 1):
        factors = [heat_activity(plaq(i, j), nmax) for i in range(2) for j in range(2)]
        factors.append(chi(n, coarse))
        val = cx.contract_invariant(factors)
        expected = {4 * n * (n + 2): Fraction(dim(n))} if n else {0: Fraction(1)}
        assert val == expected, (n, sp_str(val))


# -- Gate 6: K3 spin-model collapse and K4 positivity ----------------------
#
# K3:  ∫ dg1 dg2 dg3 chi_a(g1 g2^-1) chi_b(g2 g3^-1) chi_c(g3 g1^-1)
#      = delta_ab delta_ac / d_a
# K4:  every value is a sum of squares of (normalized) trivalent networks,
#      hence >= 0.  We check nonnegativity for spins <= 2.


def test_k3_collapse():
    g = [q_link(i) for i in range(3)]
    for a in range(0, 3):
        for b in range(0, 3):
            for c in range(0, 3):
                fac = [
                    chi(a, q_mul(g[0], q_conj(g[1]))),
                    chi(b, q_mul(g[1], q_conj(g[2]))),
                    chi(c, q_mul(g[2], q_conj(g[0]))),
                ]
                val = frac(scalar(contract(fac, [0, 1, 2])))
                expect = Fraction(1, dim(a)) if (a == b == c) else Fraction(0)
                assert val == expect, (a, b, c, val)


def test_k4_sum_of_squares_nonnegative():
    g = [q_link(i) for i in range(4)]
    edges = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    import itertools

    negatives = []
    for spins in itertools.product(range(0, 3), repeat=6):
        fac = [chi(s, q_mul(g[u], q_conj(g[v]))) for s, (u, v) in zip(spins, edges)]
        val = frac(scalar(contract(fac, [0, 1, 2, 3])))
        if val < 0:
            negatives.append((spins, val))
    assert negatives == [], negatives[:5]


# -- Gate 7: sign analysis sanity ------------------------------------------


def test_sign_analysis():
    assert sign_on_unit_interval({0: Fraction(1), 3: Fraction(2)}) == "positive"
    assert sign_on_unit_interval({1: Fraction(-1)}) == "negative"
    # 1 - 3s + s^2 has a root ~0.38 in (0,1): mixed
    assert (
        sign_on_unit_interval({0: Fraction(1), 1: Fraction(-3), 2: Fraction(1)})
        == "mixed"
    )
    # (2s - 1)^2 touches zero but never changes sign
    assert (
        sign_on_unit_interval({0: Fraction(1), 1: Fraction(-4), 2: Fraction(4)})
        == "positive"
    )
