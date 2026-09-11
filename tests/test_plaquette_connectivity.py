"""Pytest pins for the SL.1 Part A plaquette-connectivity enumeration.

Every number here is the output of an exact integer enumeration in
``plaquette_connectivity.py`` (see its module docstring for the
exhaustiveness certificate).  These tests pin:

  * the per-notion neighbor counts of a fixed plaquette on Z^d, d = 2..5;
  * the closed-form formulas in d verified at three or more d values;
  * the exact small-n polymer counts N_n under the code-consumed
    edge-adjacency notion;
  * the negative result: NO natural adjacency notion equals 5d - 4;
    the d = 4 value 16 coincides with the non-coplanar edge-neighbor
    count 8(d - 2) at d = 4 only.
"""

import pytest

from computations.plaquette_connectivity import (
    connected_polymer_counts,
    edge_adjacent_plaquettes,
    fixed_plaquette,
    neighbor_counts,
    plaquettes_containing_bond,
    plaquettes_containing_vertex,
)

DIMS = (2, 3, 4, 5)


@pytest.fixture(scope="module")
def counts():
    return {d: neighbor_counts(d) for d in DIMS}


# ----------------------------------------------------------------------
# Neighbor counts and their closed forms
# ----------------------------------------------------------------------

def test_edge_neighbors_are_8d_minus_12(counts):
    assert [counts[d]["edge"] for d in DIMS] == [4, 12, 20, 28]
    for d in DIMS:
        assert counts[d]["edge"] == 8 * d - 12


def test_coplanar_edge_neighbors_always_4(counts):
    for d in DIMS:
        assert counts[d]["edge_coplanar"] == 4


def test_noncoplanar_edge_neighbors_are_8d_minus_16(counts):
    assert [counts[d]["edge_noncoplanar"] for d in DIMS] == [0, 8, 16, 24]
    for d in DIMS:
        assert counts[d]["edge_noncoplanar"] == 8 * (d - 2)


def test_vertex_neighbors_are_8d2_minus_16d_plus_8(counts):
    assert [counts[d]["vertex"] for d in DIMS] == [8, 32, 72, 128]
    for d in DIMS:
        assert counts[d]["vertex"] == 8 * d * d - 16 * d + 8  # = 8(d-1)^2


def test_vertex_only_neighbors(counts):
    assert [counts[d]["vertex_only"] for d in DIMS] == [4, 20, 52, 100]
    for d in DIMS:
        assert counts[d]["vertex_only"] == 8 * d * d - 24 * d + 20
        # consistency: vertex = edge + vertex_only
        assert counts[d]["vertex"] == counts[d]["edge"] + counts[d]["vertex_only"]


def test_no_two_shared_vertices_without_shared_edge(counts):
    """Two plaquettes sharing >= 2 vertices share an edge (no diagonal-only)."""
    for d in DIMS:
        assert counts[d]["two_vertices_no_edge"] == 0


def test_plaquettes_per_bond_is_2_d_minus_1_bfs_424():
    """BFS 1978 eq. (4.24): 2(nu - 1) plaquettes through a fixed bond."""
    for d in DIMS:
        assert plaquettes_containing_bond(d) == 2 * (d - 1)


def test_plaquettes_per_vertex_is_2d_d_minus_1():
    for d in DIMS:
        assert plaquettes_containing_vertex(d) == 2 * d * (d - 1)


# ----------------------------------------------------------------------
# The 5d - 4 formula matches NO adjacency notion
# ----------------------------------------------------------------------

def test_5d_minus_4_matches_no_notion_across_d(counts):
    notions = (
        "edge", "edge_coplanar", "edge_noncoplanar", "vertex", "vertex_only",
    )
    for notion in notions:
        assert not all(counts[d][notion] == 5 * d - 4 for d in (3, 4, 5)), (
            f"unexpected: notion {notion} matches 5d-4 across d"
        )
    for d in (3, 4, 5):
        assert plaquettes_containing_bond(d) != 5 * d - 4
        assert plaquettes_containing_vertex(d) != 5 * d - 4


def test_16_at_d4_is_coincidence_with_noncoplanar_count(counts):
    """At d = 4 only, 5d-4 = 16 = 8(d-2) = non-coplanar edge-neighbors."""
    assert counts[4]["edge_noncoplanar"] == 16 == 5 * 4 - 4
    assert counts[3]["edge_noncoplanar"] == 8 != 5 * 3 - 4
    assert counts[5]["edge_noncoplanar"] == 24 != 5 * 5 - 4


# ----------------------------------------------------------------------
# Code-consumed notion: edge-adjacency polymer counts
# ----------------------------------------------------------------------

def test_edge_adjacency_degree_matches_neighbor_count():
    for d in (2, 3, 4, 5):
        p0 = fixed_plaquette(d)
        assert len(edge_adjacent_plaquettes(p0, d)) == 8 * d - 12


def test_polymer_counts_d3():
    assert connected_polymer_counts(3, 4)[1:] == [1, 12, 158, 2148]


def test_polymer_counts_d4():
    assert connected_polymer_counts(4, 4)[1:] == [1, 20, 458, 11132]


def test_polymer_counts_within_16_pow_n_for_small_n():
    """N_n <= 16^n holds exactly for n <= 4 at d = 4 (and n = 5, pinned
    from the full run: N_5 = 280175 <= 16^5 = 1048576).  NOTE: the
    one-step growth ratios (20, 22.9, 24.3, 25.2) exceed 16 and increase
    monotonically, so 16 is NOT a defensible asymptotic connectivity
    constant for unrestricted edge-connected plaquette polymers; the
    rigorous derivable constant is e * Delta = 20e (BF bound, Delta = 20).
    """
    counts = connected_polymer_counts(4, 4)
    for n in range(1, 5):
        assert counts[n] <= 16 ** n


def test_growth_ratios_exceed_16_from_n2_onward():
    counts = connected_polymer_counts(4, 4)
    ratios = [counts[n + 1] / counts[n] for n in range(1, 4)]
    assert all(r > 16 for r in ratios)
    # monotone increasing
    assert ratios == sorted(ratios)
