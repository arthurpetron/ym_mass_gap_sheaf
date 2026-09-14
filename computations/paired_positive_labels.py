"""Finite two-replica coverage/inclusion-exclusion pilot; no response bound."""

from itertools import product, combinations
import json
import signal


def pilot():
    sizes = {}
    for cutoff in range(3):
        spins = ([(n + 1, 0) for n in range(cutoff)]
                 + [(0, n + 1) for n in range(cutoff)]
                 + [(n + 1, m + 1) for n in range(cutoff) for m in range(cutoff)])
        assert len(spins) == (cutoff + 1)**2 - 1
        assert len(set(spins)) == len(spins)
        for count in range(4):
            covered = list(product(spins, repeat=count))
            full = list(product(range(cutoff + 1), repeat=2*count))
            expected = {tuple(zip(p[:count], p[count:])) for p in full
                        if all(a or b for a, b in zip(p[:count], p[count:]))}
            assert set(covered) == expected
            # Arbitrary signed interacting two-replica summand: not a product law.
            def value(p):
                return (-1)**sum(a + b for a, b in p) * (1 + sum((i+1)*(a+2*b) for i, (a, b) in enumerate(p)))**2
            difference = 0
            for size in range(count + 1):
                for subset in combinations(range(count), size):
                    moment = sum(value(tuple(zip(p[:count], p[count:]))) for p in full
                                 if all(p[i] == p[count+i] == 0 for i in range(count) if i not in subset))
                    difference += (-1)**(count-size)*moment
            assert difference == sum(value(p) for p in covered)
            sizes[f"K={cutoff},faces={count}"] = len(covered)
    return {"covered_pair_counts": sizes, "signed_mobius_equals_covered_sum": True,
            "original_response_floor": "NOT PROVED"}


if __name__ == "__main__":
    signal.alarm(30)
    print(json.dumps(pilot(), separators=(",", ":")))
