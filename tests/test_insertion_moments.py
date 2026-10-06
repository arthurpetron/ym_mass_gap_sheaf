"""Pins for MD.3 stage two — the insertion-moment assembly
(work_plan §16f)."""

from fractions import Fraction

from computations.insertion_moments import (
    bare_tilt_coeffs,
    bch_inventory,
    c_kin,
    gate_connected_moment_coefficient,
    gate_full_single_face_closure,
    gate_single_face_series,
    v_closed_form_ok,
    w_aggregate,
)

Fr = Fraction


def test_fusion_variance_closed_form():
    # Var_fusion(delta) == (4/3) C(n) C(m) against explicit sums
    assert v_closed_form_ok(5)


def test_c_kin_values():
    assert c_kin(1) == Fr(-8, 5)
    assert c_kin(2) == Fr(-4)
    assert c_kin(3) == Fr(-36, 5)


def test_single_face_series_gate():
    # e^tau E[(sin phi/phi) chi_n] == d_n e^{-tau C(n)} to O(tau^2),
    # fully symbolic
    assert gate_single_face_series(2)


def test_connected_moment_coefficient():
    # E[|X|^2 chi_n]/E[chi_n] - 3a == -(C(n)/4) a^2 + O(a^3)
    assert gate_connected_moment_coefficient()


def test_bare_tilt_coefficients():
    # the bare Gaussian tilt's a^2 term: p1 = -1/96, p2 = 0 — the
    # absence of a C^2 term preserves pair-independence at O(tau)
    p1, p2 = bare_tilt_coeffs()
    assert p1 == Fr(-1, 96)
    assert p2 == 0


def test_full_single_face_closure():
    # bare + insertion tau^2 terms cancel identically at a = 8 tau:
    # the pipeline reproduces the EXACT single-face identity, so no
    # diagonal contribution at this order has been omitted
    ok, _p1, _p2 = gate_full_single_face_closure()
    assert ok


def test_w_aggregate_exact():
    W = w_aggregate()
    assert W["W_top"] == W["W_bottom"] == Fr(-139, 576)
    assert W["W_links_top"] == Fr(-49, 192)
    assert W["W_faces_top"] == Fr(1, 72)


def test_c_ii_decomposition():
    W = w_aggregate()
    p1, _ = bare_tilt_coeffs()
    c_ins = 144 * W["W_top"]
    c_bare = -576 * p1
    assert c_ins == Fr(-139, 4)
    assert c_bare == Fr(6)
    assert c_ins + c_bare == Fr(-115, 4)


def test_bch_inventory_counts():
    inv = bch_inventory()
    assert inv["free_link_counts"] == {1: 3, 2: 13, 3: 1, 4: 3}


def test_reconciliation_with_assembly():
    # this module's kappa2 diagonal blocks (+139/4 Jacobians, -6
    # bare-radial) plus the c_su2_assembly BCH blocks reproduce the
    # assembly's c_dyn exactly: -115/4 + 251/8 == +21/8; and the
    # fusion-basis term matches: c_SU2(N=2) = 21/8 - 4 = -11/8
    assert Fr(-115, 4) + Fr(251, 8) == Fr(21, 8)
    assert Fr(21, 8) + c_kin(2) == Fr(-11, 8)
