"""Pins for the DP.3 M = 2 round (2026-07-26).

These pin the two refutations and the eps_slab certificate.  They read
the banked exact data (`computations/dp3_m2_entries.json`) rather than
re-contracting — a full M = 2 rebuild is hours of CPU.  The gates that
license that data (fixed-tile == skeleton_value; driver == repo function
at M = 1) are exercised separately and are marked slow.
"""
from __future__ import annotations

import json
import os
from fractions import Fraction

import pytest

from computations.dp3_m2_analysis import (
    blocked_final_at,
    blocked_image,
    blocked_verdicts,
    contributions_to,
    entry_verdicts,
    final_at,
    load,
)
from computations.exact_haar_network import sign_on_unit_interval

Frac = Fraction

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ENTRIES = os.path.join(HERE, "computations", "dp3_m2_entries.json")

pytestmark = pytest.mark.skipif(not os.path.exists(ENTRIES),
                                reason="M=2 entry data not present")


@pytest.fixture(scope="module")
def data():
    return load(ENTRIES)


def test_entries_present(data):
    T, _, _ = data
    for k in [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2)]:
        assert k in T and T[k], f"missing entry {k}"


def test_kernel_is_symmetric(data):
    """z-flip symmetry of the slab: T[n,m] == T[m,n] as exact polys."""
    T, _, _ = data
    for (n, m) in list(T):
        assert T[(n, m)] == T[(m, n)]


def test_M1_agreement_below_eps_slab_exponent(data):
    """T_{M=2}[0,0] must agree with the banked M=1 value below E* = 38."""
    T, _, _ = data
    m1 = {0: Frac(1), 18: Frac(16), 30: Frac(16), 36: Frac(32),
          42: Frac(16), 48: Frac(4)}
    for e in range(38):
        assert T[(0, 0)].get(e, Frac(0)) == m1.get(e, Frac(0)), e


# --- the refutation of DP.3-(i) at entry granularity ----------------------

def test_T11_has_a_final_negative_coefficient(data):
    T, UN, _ = data
    assert T[(1, 1)][76] == Frac(-32, 3)
    assert final_at(UN, (1, 1), 76), "E=76 coefficient must be final"


def test_T11_negative_is_the_only_final_one(data):
    T, UN, W = data
    v = entry_verdicts(T, UN, W)
    assert v[(1, 1)]["negative_final"] == [(76, "-32/3")]
    for k in [(0, 0), (0, 1), (0, 2), (1, 2)]:
        assert v[k]["negative_final"] == [], k


# --- the refutation at aggregated granularity ----------------------------

def test_blocked_image_has_a_final_negative_coefficient(data):
    T, UN, _ = data
    B = blocked_image(T, 1)
    assert B[79] == Frac(-64, 3)
    assert blocked_final_at(UN, 1, 79)


def test_no_cancellation_is_available_at_that_exponent(data):
    """The DP.6 repair fails because the sibling channels vanish there."""
    T, _, _ = data
    rows = contributions_to(T, 1, 79)
    by_m = {m: (e, c, contrib) for m, e, c, contrib in rows}
    assert by_m[0][1] == 0, "T[1,0] must vanish at s^79"
    assert by_m[2][1] == 0, "T[1,2] must vanish at s^71"
    assert by_m[1][2] == Frac(-64, 3)
    assert sum(r[3] for r in rows) == Frac(-64, 3)


def test_blocked_verdicts_shape(data):
    T, UN, _ = data
    v = blocked_verdicts(T, UN)
    assert v[1]["negative_final"] == [(79, "-64/3")]
    assert v[0]["negative_final"] == []


# --- what survives: functional positivity --------------------------------

def test_T11_final_part_is_positive_as_a_function(data):
    """Coefficientwise negative, Sturm-positive on (0,1)."""
    T, _, W = data
    fin = {e: c for e, c in T[(1, 1)].items() if e < W[(1, 1)]}
    assert any(c < 0 for c in fin.values()), "the negative must be inside"
    assert sign_on_unit_interval(fin) == "positive"


def test_blocked_final_parts_are_positive_as_functions(data):
    T, UN, W = data
    for n in (0, 1):
        win = min(W[(n, m)] + c for m, c in ((0, 0), (1, 3), (2, 8))
                  if W.get((n, m)) is not None)
        fin = {e: c for e, c in blocked_image(T, n).items() if e < win}
        assert sign_on_unit_interval(fin) == "positive", n


# --- eps_slab -------------------------------------------------------------

EPS_STAR = {(0, 0): 38, (0, 1): 32, (0, 2): 32, (0, 3): 68, (1, 1): 38,
            (1, 2): 44, (1, 3): 56, (2, 2): 56, (2, 3): 68, (3, 3): 88}


@pytest.mark.slow
def test_eps_slab_exponents():
    """E*(n,m,1) by pure enumeration; far above the naive C(2) = 8."""
    from computations.eps_slab import e_star
    for (n, m), want in EPS_STAR.items():
        got, _ = e_star(n, m, 1)
        assert got == want, (n, m, got, want)
    assert min(EPS_STAR.values()) == 32


# --- gates (slow) ---------------------------------------------------------

@pytest.mark.slow
def test_fixed_tile_matches_skeleton_value():
    from computations.dp3_fixed_tile import gate
    cases = [(0, 0, (0, 0, 0, 0), (0, 0, 0, 0)),
             (0, 0, (0, 0, 0, 1), (0, 0, 1, 1)),
             (0, 0, (0, 0, 0, 2), (0, 0, 2, 2)),
             (0, 0, (1, 1, 1, 1), (0, 0, 0, 2))]
    assert gate(cases, 2, verbose=False)


@pytest.mark.slow
def test_driver_matches_repo_function_at_M1():
    from computations.dp3_m2_driver import gate_M1
    assert gate_M1(nmax=1, verbose=False)
