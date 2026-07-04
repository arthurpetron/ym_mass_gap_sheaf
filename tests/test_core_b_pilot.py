"""Tests for the Core-B saddle local-CLT pilot (computations/core_b_pilot.py).

These mirror the Lean satisfiability/honesty facts:
* p=1 fusionEig == eigA exactly, literal shift == 0 (saddleLocalCLT_p1);
* fusion_ind reproduces the SU(2) character-product decomposition;
* the estimate side (eta) is under the 1/12 budget with wide margin;
* the LITERAL bulkShiftBound fails for p>=2 at every w (honesty gap);
* the rebased shift is under budget;
* the Tier-0 mirror: Delta^2 C4 == 2, d2x <= 1, the two <= 1/2 half-splits.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

import mpmath as mp
import pytest

from computations import core_b_pilot as cb
from computations import su2_representations as su2

Q112 = float(Fraction(1, 12))


def setup_module(module):  # noqa: D103
    mp.mp.dps = 40


# --------------------------------------------------------------------------
# p = 1 anchors (exact Fraction).
# --------------------------------------------------------------------------
def test_p1_exact_eig_equals_heat_kernel():
    w = Fraction(2, 3)
    n = 14
    for s in (1, 2, 3):
        assert cb.fusion_eig(n, w, 1, s) == cb.eig_a(w, s)
    assert cb.fusion_eig(n, w, 1, 1) == Fraction(8, 27)
    assert cb.fusion_eig(n, w, 1, 2) == w ** 8
    assert cb.fusion_eig(n, w, 1, 3) == w ** 15


def test_p1_shift_is_zero():
    n = 14
    for w in (Fraction(1, 2), Fraction(2, 3), Fraction(7, 9)):
        assert cb.literal_shift(n, w, 1, 6) == Fraction(0)


# --------------------------------------------------------------------------
# Clebsch-Gordan cross-check against su2_representations.
# --------------------------------------------------------------------------
def test_fusion_ind_matches_cg():
    # chi_1 * chi_1 = chi_0 + chi_2  (spin 1/2 (x) spin 1/2 = 0 (+) 1), s-labels.
    assert [s for s in range(0, 4) if cb.fusion_ind(1, 1, s)] == [0, 2]
    # chi_2 * chi_2 = chi_0 + chi_2 + chi_4  (spin 1 (x) spin 1).
    assert [s for s in range(0, 6) if cb.fusion_ind(2, 2, s)] == [0, 2, 4]
    # Character-product identity: sum_s fusion_ind(a,b,s) chi_s = chi_a chi_b.
    thetas = [0.37, 1.1, 2.3, 2.9]
    for a in range(0, 4):
        for b in range(0, 4):
            chi_a = su2.Irrep.from_spin(Fraction(a, 2))
            chi_b = su2.Irrep.from_spin(Fraction(b, 2))
            for theta in thetas:
                lhs = sum(
                    cb.fusion_ind(a, b, s)
                    * su2.Irrep.from_spin(Fraction(s, 2)).character(theta)
                    for s in range(0, a + b + 1)
                )
                rhs = chi_a.character(theta) * chi_b.character(theta)
                assert lhs == pytest.approx(rhs, abs=1e-9)


# --------------------------------------------------------------------------
# General-p structural facts.
# --------------------------------------------------------------------------
def test_bmc_zero_pos():
    n = 12
    for w in (Fraction(1, 2), Fraction(7, 9), Fraction(95, 96)):
        for p in (1, 2, 3, 4):
            assert cb.bond_moved_coeff(n, w, p, 0) >= 1


def test_s1_dominance_p1():
    n = 12
    for w in (Fraction(1, 2), Fraction(2, 3), Fraction(7, 9)):
        b1 = cb.bond_moved_coeff(n, w, 1, 1)
        for s in range(1, n + 1):
            assert cb.bond_moved_coeff(n, w, 1, s) <= b1


# --------------------------------------------------------------------------
# The estimate side (eta) vs the 1/12 budget.
# --------------------------------------------------------------------------
def test_eta_under_budget():
    n = 20
    for w in cb.DEFAULT_W_VALUES:
        for p in (2, 3, 4, 8):
            mod = cb.saddle_fit(n, w, p, 8)
            assert float(mod.eta) < Q112
    # worst corner (smallest w, p=2) is small.
    worst = cb.saddle_fit(n, Fraction(1, 2), 2, 8)
    assert float(worst.eta) <= 0.0025


def test_eta_worst_corner_is_smallest_w_p2():
    n = 20
    result = cb.run_sweep(cb.DEFAULT_W_VALUES, [2, 3, 4], 8, n)
    worst_cell = max(result.eta, key=lambda k: result.eta[k])
    assert worst_cell == ("1/2", 2)


# --------------------------------------------------------------------------
# The literal bulkShiftBound honesty gap (fails p>=2 for every w).
# --------------------------------------------------------------------------
def test_literal_bulkshift_fails_p2():
    n = 20
    for w in cb.DEFAULT_W_VALUES:
        for p in (2, 3, 4):
            shift = float(cb.literal_shift(n, w, p, 8, arr=cb._mpf_bmc_array(n, w, p)))
            assert shift > Q112


def test_rebased_shift_under_budget():
    n = 20
    for w in cb.DEFAULT_W_VALUES:
        for p in (2, 3, 4, 8):
            arr = cb._mpf_bmc_array(n, w, p)
            mod = cb.saddle_fit(n, w, p, 8, arr=arr)
            reb = float(cb.rebased_shift(n, w, p, 8, mod.w_eff, arr=arr))
            assert reb < Q112


def test_eta_monotone_in_bulk_window():
    # eta is non-increasing in p on the character/bulk window (w <= 11/12);
    # the w -> 1 corner (95/96) is a ~1e-6 subleading anomaly (measured, honest).
    n = 20
    bulk = [Fraction(1, 2), Fraction(2, 3), Fraction(7, 9), Fraction(11, 12)]
    ps = [2, 3, 4, 8]
    result = cb.run_sweep(bulk, ps, 8, n)
    for w in bulk:
        wl = f"{w.numerator}/{w.denominator}"
        seq = [result.eta[(wl, p)] for p in ps]
        assert all(seq[i + 1] <= seq[i] + 1e-12 for i in range(len(seq) - 1))
    # non-increasing in w at fixed p.
    for p in ps:
        seq = [result.eta[(f"{w.numerator}/{w.denominator}", p)] for w in bulk]
        assert all(seq[i + 1] <= seq[i] + 1e-12 for i in range(len(seq) - 1))


# --------------------------------------------------------------------------
# Tier-0 mirror.
# --------------------------------------------------------------------------
def test_casimir_second_diff_two():
    for s in range(0, 20):
        assert cb.casimir_second_diff(s) == 2


def test_xmean_second_diff_le_one():
    for w in cb.DEFAULT_W_VALUES:
        for s in range(0, 7):
            assert cb.d2x(w, s) <= 1


def test_mean_shift_halves_le_half():
    half = Fraction(1, 2)
    for w in cb.DEFAULT_W_VALUES:
        for s in range(0, 7):
            assert cb.mean_shift_half(w, s) <= half
            assert cb.mean_shift_complement_half(w, s) <= half


def test_pfmom_identity():
    an, fd = cb.pfmom_check(Fraction(2, 3), 4)
    assert abs(an - fd) / abs(an) < 1e-10


# --------------------------------------------------------------------------
# Smoke tests for JSON + plots.
# --------------------------------------------------------------------------
def test_json_roundtrip(tmp_path: Path):
    result = cb.run_sweep([Fraction(1, 2), Fraction(2, 3)], [1, 2], 5, 12)
    tier0 = cb.run_tier0([Fraction(1, 2), Fraction(2, 3)], [0, 1, 2])
    payload = cb.to_json_payload(result, tier0)
    out = tmp_path / "cb.json"
    out.write_text(json.dumps(payload, indent=2))
    loaded = json.loads(out.read_text())
    assert "eta_sweep" in loaded
    assert loaded["tier0"]["casimir_second_diff_two"] is True
    assert loaded["budget"] == pytest.approx(Q112)


def test_plots_written(tmp_path: Path):
    result = cb.run_sweep([Fraction(1, 2), Fraction(2, 3)], [1, 2, 3], 5, 12)
    tier0 = cb.run_tier0([Fraction(1, 2), Fraction(2, 3)], [0, 1, 2, 3])
    paths = cb.write_all_plots(
        result, tier0, [Fraction(1, 2), Fraction(2, 3)], [1, 2, 3], 5, 12,
        out_dir=tmp_path,
    )
    for p in paths:
        assert p.exists()
        assert p.stat().st_size > 0
