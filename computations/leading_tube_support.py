"""Finite geometry pilot; the general Lean support proof is independent."""

from itertools import combinations, product
import json
import signal


def shifted(vertex, direction):
    return tuple(n + (i == direction) for i, n in enumerate(vertex))


def edges(face):
    vertex, (first, second) = face
    return {(vertex, first), (vertex, second),
            (shifted(vertex, second), first), (shifted(vertex, first), second)}


def pilot():
    checked = 0
    margins = (0, 1, 3)
    for margin in margins:
        origin = (1 + margin,) * 3
        boundary = edges((origin + (margin,), (0, 1)))
        tube = set()
        for time in range(margin, margin + 3):
            for vertex, direction in boundary:
                tube.add((vertex[:3] + (time,), (direction, 3)))
        assert len(tube) == 12
        found = set()
        for vertex in product(range(margin + 5), repeat=4):
            for plane in combinations(range(4), 2):
                face = (vertex, plane)
                criterion = (plane[1] == 3 and margin <= vertex[3] < margin + 3
                             and (vertex[:3] + (margin,), plane[0]) in boundary)
                assert (face in tube) == criterion
                if criterion:
                    found.add(face)
                checked += 1
        assert found == tube
    return {"margins": margins, "face_membership_checks": checked,
            "tube_faces_per_margin": 12,
            "original_weighted_amplitude": "NOT EVALUATED",
            "leading_enumeration_multiplicity": "NOT PROVED"}


if __name__ == "__main__":
    signal.alarm(30)
    print(json.dumps(pilot(), separators=(",", ":")))
