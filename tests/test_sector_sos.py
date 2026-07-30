"""Pins for the sector-SOS positivity certificate (work_plan §17g).

Every assertion is exact-rational.  The certificate itself is a
coefficient-sign statement, so the pins are integer comparisons.
"""
from fractions import Fraction as Frac

import pytest

from computations.sector_sos import (
    ENTRIES,
    assemble,
    det_poly,
    gate_banked_census,
    gate_exactness,
    gate_identity,
    gate_psd,
    gate_s1_multiplicity,
    gate_x11_banked,
    half_config_gram,
    moebius_reciprocal,
    as_coeff_list,
    pev,
    positivity_certificate,
    psd_exact,
    sector_kernels,
    sector_weight,
)

CAP, TILE_M = 1, 2


@pytest.fixture(scope="module")
def fam():
    return sector_kernels(CAP, TILE_M)


def test_family_size_and_kernels(fam):
    assert len(fam) == 16
    T = assemble(fam)
    # The exact integer kernels of the certificate family.
    assert T[(0, 0)] == {0: Frac(1), 18: Frac(16), 30: Frac(16),
                         36: Frac(32), 42: Frac(16), 48: Frac(4)}
    assert T[(0, 1)][12] == Frac(2)
    assert T[(1, 1)][24] == Frac(5)
    assert all(c.denominator == 1 for k in ENTRIES for c in T[k].values())


def test_certificate_is_a_coefficient_sign_statement(fam):
    cert = positivity_certificate(det_poly(assemble(fam)))
    assert cert["s_power"] == 24
    assert cert["deg_P"] == 106
    assert cert["t_power"] == 4
    assert cert["n_coeffs"] == 103
    assert cert["n_negative"] == 0          # THE certificate
    assert cert["Rhat0"] == Frac(15972864)
    assert cert["certified"] is True
    # non-vacuity: P itself is NOT coefficientwise positive
    assert sum(1 for c in cert["P"] if c < 0) == 16


def test_moebius_soundness_on_a_known_negative():
    # (s - 1/2) is negative near 0 on (0,1): the transform must expose it.
    P = [Frac(-1, 2), Frac(1)]
    R = moebius_reciprocal(P)
    assert any(c < 0 for c in R)
    # and a genuinely positive polynomial must pass
    P2 = [Frac(1), Frac(1)]
    assert all(c >= 0 for c in moebius_reciprocal(P2))


def test_psd_exact_selftest():
    assert psd_exact([[Frac(2), Frac(1)], [Frac(1), Frac(2)]])
    assert psd_exact([[Frac(0), Frac(0)], [Frac(0), Frac(1)]])
    assert not psd_exact([[Frac(0), Frac(1)], [Frac(1), Frac(0)]])
    assert not psd_exact([[Frac(1), Frac(2)], [Frac(2), Frac(1)]])


def test_gate_exactness():
    ok, _ = gate_exactness(CAP, TILE_M)
    assert ok


def test_gate_psd():
    ok, msgs = gate_psd(CAP, TILE_M)
    assert ok, "\n".join(msgs)


def test_gate_pair_expansion_identity():
    ok, msgs = gate_identity(CAP, TILE_M)
    assert ok, "\n".join(msgs)


def test_gate_banked_census():
    ok, msgs = gate_banked_census(CAP, TILE_M)
    assert ok, "\n".join(msgs)


def test_gate_banked_cert_grid():
    ok, msgs = gate_x11_banked(CAP, TILE_M)
    assert ok, "\n".join(msgs)


def test_s1_degeneracy_is_order_four(fam):
    mult, lead = gate_s1_multiplicity(CAP, TILE_M)
    assert mult == 4
    assert lead == Frac(15972864)


def test_positivity_at_probe_couplings_including_the_middle_regime(fam):
    """Spot checks of det_S > 0, including PAST the anchor edge 2^(-1/3)
    where no prior certified statement existed."""
    det = det_poly(assemble(fam))
    for a, b in [(1, 10), (1, 2), (5, 8), (4, 5), (9, 10), (99, 100),
                 (999, 1000), (99999, 100000)]:
        assert pev(det, Frac(a, b)) > 0, f"s={a}/{b}"


def test_trivial_sector_is_exactly_rank_one(fam):
    """The rank-one collapse: the dominant sector contributes ZERO
    determinant, so the certificate is entirely interference-driven."""
    rows = fam[((0, 0, 0, 0), (0, 0, 0, 0))]
    s = Frac(1, 2)
    A, C, B = (pev(rows[(0, 0)], s), pev(rows[(0, 1)], s), pev(rows[(1, 1)], s))
    assert A * B - C * C == 0
    assert sector_weight((0, 0, 0, 0), (0, 0, 0, 0)) == (Frac(1), 0)


def test_half_config_gram_is_symmetric(fam):
    for (q, w) in list(fam)[:4]:
        idx, H = half_config_gram(q, w, TILE_M)
        assert len(idx) == len(H)
        for i in range(len(H)):
            for j in range(len(H)):
                assert H[i][j] == H[j][i]
