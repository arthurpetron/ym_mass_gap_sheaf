"""Small exact regressions for the unchanged ordered replica enumeration."""

from itertools import product
import json
import signal


def selections(ids):
    if not ids:
        return [()]
    tail = selections(ids[1:])
    return tail + [(ids[0],) + xs for xs in tail]


def labels(cutoff, ids):
    if not ids:
        return [((0,) * 6, (0,) * 6)]
    spins = ([(i, 0) for i in range(1, cutoff + 1)]
             + [(0, i) for i in range(1, cutoff + 1)]
             + list(product(range(1, cutoff + 1), repeat=2)))
    result = []
    for a, b in spins:
        for left, right in labels(cutoff, ids[1:]):
            x, y = list(left), list(right)
            x[ids[0]], y[ids[0]] = a, b
            result.append((tuple(x), tuple(y)))
    return result


def pilot():
    count = 0
    for cutoff in range(4):
        for size in range(4):
            ids = (0, 2, 5)[:size]
            supports = selections(ids)
            assert len(set(supports)) == len(supports) == 2 ** size
            full = []
            for selected in supports:
                block = labels(cutoff, selected)
                assert len(set(block)) == len(block) == ((cutoff + 1) ** 2 - 1) ** len(selected)
                for left, right in block:
                    assert tuple(i for i in ids if left[i] or right[i]) == selected
                full += block
            assert len(set(full)) == len(full) == (cutoff + 1) ** (2 * size)
            enumerated = set(full)
            for values in product(range(cutoff + 1), repeat=2 * size):
                left, right = [0] * 6, [0] * 6
                for position, face in enumerate(ids):
                    left[face] = values[position]
                    right[face] = values[size + position]
                assert (tuple(left), tuple(right)) in enumerated
            count += len(full)
    return {"cutoffs": [0, 1, 2, 3], "maximum_selected_faces": 3,
            "combined_replica_entries": count, "duplicate_entries": 0,
            "explicit_bounded_pair_membership_checks": count,
            "physical_leading_count_positivity": "NOT TESTED"}


if __name__ == "__main__":
    signal.alarm(30)
    print(json.dumps(pilot(), separators=(",", ":")))
