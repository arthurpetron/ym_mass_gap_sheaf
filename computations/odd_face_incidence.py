"""Exact odd-face incidence pilot, not a signed connected-response bound."""

from collections import Counter
from itertools import product
import json
import signal


def add_e(v, d):
    return tuple(x + (i == d) for i, x in enumerate(v))


def boundary(face):
    v, a, b = face
    return [(v, a), (add_e(v, a), b), (add_e(v, b), a), (v, b)]


def pilot():
    faces = [((1, 1, 1, 0), 0, 3), ((2, 1, 1, 0), 1, 3),
             ((1, 2, 1, 0), 0, 3), ((1, 1, 1, 0), 1, 3)]
    accepted_counts = set()
    rejected_thin = 0
    for labels in product(range(5), repeat=4):
        charge, odd_incidence = Counter(), Counter()
        for f, n in zip(faces, labels):
            for link in boundary(f):
                charge[link] += n
                odd_incidence[link] += n % 2
        assert all(charge[e] % 2 == odd_incidence[e] % 2 for e in charge)
        count = sum(n % 2 for n in labels)
        vertical_even = all(n % 2 == 0 for e, n in charge.items() if e[1] == 3)
        if 0 < count < 4:
            assert not vertical_even
            rejected_thin += 1
        if vertical_even:
            accepted_counts.add(count)
    assert accepted_counts == {0, 4}
    for time in (0, 3):
        assert all(e[1] != 3 for e in boundary(((1, 1, 1, time), 0, 1)))
    return {"one_cut_labels_checked": 5**4,
            "thin_odd_cuts_rejected": rejected_thin,
            "accepted_odd_face_counts": sorted(accepted_counts),
            "spatial_probe_vertical_charge": 0,
            "every_connected_term_crosses_in_odd_faces": "NOT PROVED",
            "original_response_floor": "NOT PROVED"}


if __name__ == "__main__":
    signal.alarm(30)
    print(json.dumps(pilot(), separators=(",", ":")))
