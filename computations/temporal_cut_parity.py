"""Finite pilots for the temporal-cut four-edge obstruction.

No claim about all connected replica selections or a physical response floor.
Lean proves the general finite graph/geometry statements independently.
"""

from itertools import combinations, product
import json
import signal


def even_degrees(edges):
    return (all(sum(x == a for x, _ in edges) % 2 == 0 for a, _ in edges)
            and all(sum(y == b for _, y in edges) % 2 == 0 for _, b in edges))


def pilot():
    universe = list(product(range(3), repeat=2))
    accepted = []
    for n in range(1, 10):
        for edges in combinations(universe, n):
            if even_degrees(edges):
                assert n >= 4
                accepted.append(n)
    square = [(0, 0), (1, 0), (1, 1), (0, 1)]
    assert even_degrees(square)
    # Three independent time cuts of the literal four-edge tube.
    surviving = []
    for mask in range(1 << 12):
        cuts = [[square[i] for i in range(4) if mask & (1 << (4*t+i))]
                for t in range(3)]
        if all(cut and even_degrees(cut) for cut in cuts):
            surviving.append(mask)
    assert surviving == [(1 << 12) - 1]
    return {"bipartite_3_by_3_nonempty_even_counts": sorted(set(accepted)),
            "nonempty_even_cut_minimum": 4,
            "three_tube_cuts_force_all_twelve": True,
            "general_connected_selection_crossing": "NOT PROVED",
            "original_response_floor": "NOT PROVED"}


if __name__ == "__main__":
    signal.alarm(30)
    print(json.dumps(pilot(), separators=(",", ":")))
