"""Exact center-charge pilot; a zero-term filter, not a response floor.

Checks the all-spin recurrence on a relative quaternion word and the actual
three-layer tube incidence. Two disconnected endpoint caps also pass the
parity test: connected cancellation is an additional, essential condition.
"""

import json
import signal

from computations.exact_haar_network import chi, holonomy, integrate_link
from computations.dual_positivity_geometry_bridge import add_e


def boundary(face):
    base, (a, b) = face
    return [(base, a), (add_e(base, a), b),
            (add_e(base, b), a), (base, b)]


def odd_links(faces):
    charge = set()
    for face, spin in faces:
        if spin % 2:
            charge.symmetric_difference_update(boundary(face))
    return charge


def pilot():
    for spin in range(5):
        p = chi(spin, holonomy([(0, 1), (1, -1)]))
        for monomial in p:
            for link in (0, 1):
                degree = sum(e for variable, e in monomial if variable // 4 == link)
                assert degree % 2 == spin % 2
        if spin % 2:
            assert not integrate_link(p, 0)
    slices = [((1, 1, 1, t), (0, 1)) for t in range(4)]
    sides = [f for t in range(3) for f in (
        ((1, 1, 1, t), (0, 3)), ((2, 1, 1, t), (1, 3)),
        ((1, 2, 1, t), (0, 3)), ((1, 1, 1, t), (1, 3)))]
    endpoints = [(slices[0], 1), (slices[3], 1)]
    assert len(odd_links(endpoints)) == 8
    assert not odd_links(endpoints + [(f, 1) for f in sides])
    assert all(odd_links(endpoints + [(f, 1) for j, f in enumerate(sides) if j != i])
               for i in range(12))
    assert not odd_links(endpoints + endpoints)
    tube_checks = [not odd_links([(f, 1) for f in sides] +
                   (endpoints[:1] if lo else []) + (endpoints[1:] if hi else []))
                   for lo, hi in ((False, False), (True, False), (False, True), (True, True))]
    assert tube_checks == [False, False, False, True]
    return {"relative_character_spins": list(range(5)),
            "tube_faces": 12, "each_single_deletion_rejected": True,
            "disconnected_caps_also_pass": True,
            "tube_partition_lower_upper_mixed_checks": tube_checks,
            "minimal_connected_surface_bound": "NOT PROVED",
            "original_response_floor": "NOT PROVED"}


if __name__ == "__main__":
    signal.alarm(30)
    print(json.dumps(pilot(), separators=(",", ":")))
