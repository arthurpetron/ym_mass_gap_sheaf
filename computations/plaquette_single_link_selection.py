"""Exact one-link SU(2) character pilot; no connected-response estimate."""

from fractions import Fraction as F
from itertools import product
from collections import Counter
from odd_face_incidence import boundary
import json
import signal


def mul(a, b):
    x, y, z, t = a
    u, v, w, s = b
    return (x*u-y*v-z*w-t*s, x*v+y*u+z*s-t*w,
            x*w-y*s+z*u+t*v, x*s+y*w-z*v+t*u)


def word(qs, flags):
    value = (F(1), F(0), F(0), F(0))
    for q, flag in zip(qs, flags):
        value = mul(value, (q[0], -q[1], -q[2], -q[3]) if flag else q)
    return value[0]


def haar(mono):
    if any(n % 2 for n in mono):
        return F(0)
    value = F(1)
    for n in mono:
        for k in range(1, n, 2):
            value *= k
    for k in range(2, sum(mono)//2 + 2):
        value /= 2*k
    return value


def pilot():
    spectators = [(F(1, 2),)*4, (F(3, 5), F(4, 5), F(0), F(0)),
                  (F(5, 13), F(0), F(12, 13), F(0))]
    assert all(sum(x*x for x in q) == 1 for q in spectators)
    checks = 0
    for flags in product((False, True), repeat=4):
        for slot in range(4):
            coefficients = []
            for axis in range(4):
                qs = list(spectators)
                qs.insert(slot, tuple(F(i == axis) for i in range(4)))
                value = word(qs, flags)
                assert value == word(qs[slot:]+qs[:slot], flags[slot:]+flags[:slot])
                coefficients.append(value)
            assert sum(c*c for c in coefficients) == 1
            previous, current = {}, {(0, 0, 0, 0): F(1)}
            for spin in range(7):
                assert sum(c*haar(m) for m, c in current.items()) == (1 if spin == 0 else 0)
                checks += 1
                following = {m: -c for m, c in previous.items()}
                for mono, c in current.items():
                    for axis, v in enumerate(coefficients):
                        target = tuple(n + (i == axis) for i, n in enumerate(mono))
                        following[target] = following.get(target, F(0)) + 2*v*c
                previous, current = current, following
    faces = [((1, 1, 1, 0), 0, 3), ((2, 1, 1, 0), 1, 3),
             ((1, 2, 1, 0), 0, 3), ((1, 1, 1, 0), 1, 3)]
    extra_rejections = 0
    for labels in product(range(5), repeat=4):
        charge, occupied = Counter(), Counter()
        for face, spin in zip(faces, labels):
            for link in boundary(face):
                if link[1] == 3:
                    charge[link] += spin
                    occupied[link] += int(spin > 0)
        parity_passes = all(n % 2 == 0 for n in charge.values())
        leaf_passes = all(n != 1 for n in occupied.values())
        assert leaf_passes == (all(labels) or not any(labels))
        extra_rejections += int(parity_passes and not leaf_passes)
    assert extra_rejections == 64
    return {"exact_character_moments": checks, "slots": 4, "orientations": 16,
            "spins": "0..6", "positive_spin_means": "zero",
            "one_cut_label_assignments": 625, "additional_parity_survivors_rejected": extra_rejections,
            "full_original_response_floor": "NOT PROVED"}


if __name__ == "__main__":
    signal.alarm(30)
    print(json.dumps(pilot(), separators=(",", ":")))
