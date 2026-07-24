"""Pins for the DP.2 slab blocking kernel (P19)."""

from fractions import Fraction

from computations.slab_blocking_kernel import (
    kernel_entry,
    kernel_entry_2d_gate,
    kernel_entry_frozen,
    kernel_entry_skeleton,
    network_value,
)


def test_2d_disk_gate():
    # N(n,m,0) = d_n^-3 d_m^-3: walls frozen -> two disconnected disks
    assert network_value(1, 1, (0, 0, 0, 0)) == {0: Fraction(1, 64)}
    assert network_value(0, 2, (0, 0, 0, 0)) == {0: Fraction(1, 27)}


def test_frozen_side_scheme_is_exact_2d():
    # univalence kills all transverse terms at thickness one
    assert kernel_entry_frozen(1, 1) == {24: Fraction(4)}
    assert kernel_entry_frozen(0, 1) == {12: Fraction(2)}


def test_open_disk_gate():
    # top tiles + loop only: c'_n = d_n s^{4C(n)} exactly
    assert kernel_entry_2d_gate(1, 2) == {12: Fraction(2)}


def test_owned_boundary_entries_M1():
    # exact M=1 kernel entries (cross-validated skeleton == direct)
    t11 = kernel_entry_skeleton(1, 1, 1)
    assert t11 == {24: Fraction(5), 30: Fraction(12), 36: Fraction(2)}
    assert t11 == kernel_entry(1, 1, 1)


def test_owned_boundary_T00_M1():
    t00 = kernel_entry_skeleton(0, 0, 1)
    assert t00 == {
        0: Fraction(1),
        18: Fraction(16),
        30: Fraction(16),
        36: Fraction(32),
        42: Fraction(16),
        48: Fraction(4),
    }
