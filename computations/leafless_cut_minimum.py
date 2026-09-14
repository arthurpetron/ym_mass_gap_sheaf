"""Finite pilots for leafless support; no Haar sign or response estimate."""

from collections import Counter
from itertools import product
from odd_face_incidence import boundary
import json
import signal


def leafless(edges):
    left = Counter(a for a, _ in edges)
    right = Counter(b for _, b in edges)
    return all(n != 1 for n in (*left.values(), *right.values()))


def temporal_separators():
    left = set(boundary(((1, 1, 1, 0), 0, 1)))
    right = set(boundary(((1, 1, 1, 3), 0, 1)))
    sides = [((1, 1, 1, t), 0, 3) for t in range(3)]
    sides += [((2, 1, 1, t), 1, 3) for t in range(3)]
    sides += [((1, 2, 1, t), 0, 3) for t in range(3)]
    sides += [((1, 1, 1, t), 1, 3) for t in range(3)]
    faces = sides + [((1, 1, 1, t), 0, 1) for t in (0, 3)]
    boundaries = [set(boundary(face)) for face in faces]
    retained = 0
    for bits in product((False, True), repeat=len(faces)):
        selected = [i for i, keep in enumerate(bits) if keep]
        reached = set(left)
        while True:
            old = len(reached)
            for i in selected:
                if reached & boundaries[i]:
                    reached |= boundaries[i]
            if len(reached) == old:
                break
        connected = bool(reached & right)
        retained += int(connected)
        for t in range(3):
            crossing = [i for i in selected if faces[i][2] == 3 and faces[i][0][3] == t]
            if not crossing:
                below, above = set(left), set(right)
                for i in selected:
                    (below if faces[i][0][3] <= t else above).update(boundaries[i])
                assert all(link[0][3] <= t for link in below)
                assert all(link[0][3] > t for link in above)
                assert not (below & above)
                assert not connected
            if connected:
                assert crossing
    assert retained > 0
    return {"selected_supports": 2**len(faces), "connected_supports": retained,
            "intervening_cuts": 3}


def pilot():
    carrier = list(product(range(3), repeat=2))
    survivors = []
    for bits in product((False, True), repeat=len(carrier)):
        edges = [e for e, keep in zip(carrier, bits) if keep]
        if edges and leafless(edges):
            assert len(edges) >= 4
            survivors.append(len(edges))
    assert min(survivors) == 4
    assert leafless(carrier)  # Degree three is allowed: parity is not assumed.
    square = [(0, 0), (0, 1), (1, 0), (1, 1)]
    pair_sizes = []
    assignments = 0
    for spins in product(range(3), repeat=8):
        assignments += 1
        replicas = [[e for e, j in zip(square, labels) if j > 0]
                    for labels in (spins[:4], spins[4:])]
        if all(leafless(es) for es in replicas) and any(replicas):
            size = sum(map(len, replicas))
            assert size >= 4
            pair_sizes.append(size)
    assert min(pair_sizes) == 4
    for sizes in product(sorted(set(pair_sizes)), repeat=3):
        assert sum(sizes) >= 12
    return {"bipartite_subsets": 512, "nonempty_leafless": len(survivors),
            "minimum_edges": min(survivors), "odd_degree_survivor": "K3,3",
            "paired_square_spin_assignments": assignments,
            "minimum_combined_three_cut_size_given_coverage": 12,
            "temporal_separator_pilot": temporal_separators(),
            "general_original_expansion_claim": "REQUIRES LEAN PROOF",
            "full_original_response_floor": "NOT PROVED"}


if __name__ == "__main__":
    signal.alarm(30)
    print(json.dumps(pilot(), separators=(",", ":")))
