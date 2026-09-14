"""Exact support saturation and three-layer binary strip pilot."""

from itertools import product
import json
import signal


def pilot():
    saturation = 0
    # Two replica populations in three disjoint cuts, plus off-window faces.
    for counts in product((0, 4, 5, 8), repeat=6):
        if any(counts[i]+counts[i+3] < 4 for i in range(3)):
            continue
        for outside in range(3):
            if sum(counts)+outside == 12:
                saturation += 1
                assert outside == 0
                assert all(counts[i]+counts[i+3] == 4 for i in range(3))
    assert saturation == 8
    strips = []
    for lo, a, b, c, hi in product((0, 1), repeat=5):
        equations = (lo+a, a+b, b+c, c+hi)
        if all(n % 2 == 0 for n in equations):
            assert lo == a == b == c == hi
            strips.append((lo, a, b, c, hi))
    assert strips == [(0,)*5, (1,)*5]
    return {"saturated_replica_distributions": saturation,
            "binary_strip_assignments": 32, "passing_strips": strips,
            "original_leading_coefficient_value": "NOT PROVED",
            "signed_remainder_bound": "NOT PROVED"}


if __name__ == "__main__":
    signal.alarm(30)
    print(json.dumps(pilot(), separators=(",", ":")))
