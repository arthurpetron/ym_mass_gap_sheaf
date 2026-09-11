"""Pins for the stage-three majorant-series envelope (work_plan §17c)."""

from fractions import Fraction as F

from computations.su2_envelope2 import SlabData, envelope_theorem2
from computations.su2_envelope3 import (
    Majorants,
    MirrorStage3,
    Stage3,
    face_fold_majorants,
    gate_dynkin_numeric,
    gate_fold,
    gate_moments,
    gate_series,
    goldberg_series,
    mu_chi,
)


def test_goldberg_series_low_orders():
    """f(z) = -log(2 - e^z) = z + z^2 + z^3 + 7/6 z^4 + ..."""
    f = goldberg_series(8)
    assert f[1] == 1 and f[2] == 1 and f[3] == 1
    assert f[4] == F(13, 12)
    assert all(x > 0 for x in f[1:])


def test_chi3_moments():
    """Even chi_3 moments exact; odd uppers dominate (mpmath-gated)."""
    assert mu_chi(2) == 3 and mu_chi(4) == 15 and mu_chi(8) == 945
    assert gate_moments()


def test_face_fold_vanishing_structure():
    """p_f counts only distinct-link pairs: a 2-letter same-link word
    has p = 0; distinct-link words have p > 0."""
    c = [F(1)] * 4
    p_same, _ = face_fold_majorants([(0, 1), (0, -1)], c)
    assert p_same == 0
    p_dist, d3 = face_fold_majorants([(0, 1), (1, -1)], c)
    assert p_dist == F(1, 2) and d3 > 0


def test_stage_three_theorem():
    st = Stage3()
    best = st.theorem()
    tau = best["tau_star"]
    # banked stage-three constants (regenerate ledger if these move)
    assert tau == F(1, 2 ** 44)
    assert best["N"] == 12
    rx = best["R_X_at_tau"]
    assert rx <= 3 * tau * tau
    # dominates repaired stage two
    t2, _, _, _ = envelope_theorem2()
    assert tau > t2 == F(1, 2 ** 61)


def test_gates_and_mirror():
    data = SlabData()
    maj = Majorants(data)
    assert gate_fold(data, maj)
    assert gate_series(maj)
    assert gate_dynkin_numeric(data)
    mir = MirrorStage3(data)
    assert mir.exact_coeff_gate()
    # separation at the stage-three tau*
    tau = F(1, 2 ** 44)
    assert mir.x_bound(tau, 12) < 8 * tau


def test_majorant_scale_pins():
    """Order-of-magnitude pins on the frontier majorants (loose, to
    catch silent regressions without freezing exact values)."""
    st = Stage3()
    assert F(10) ** 21 < st.maj.m[8] < F(10) ** 23
    assert st.lam[8] >= st.maj.m[8]
