"""Untrusted exact pilot for radius shell counts and trace partitioning.

Small common-parity carriers use arbitrary integer test weights. The actual
physical Gaussian estimates are proved by the separate Lean predecessor.
"""

from collections import Counter
from itertools import product


def main() -> None:
    states_checked = partitions = 0
    for cutoff in range(9):
        states = [s for parity in (0, 1)
                  for s in product(range(parity, cutoff + 1, 2), repeat=6)]
        assert len(states) == len(set(states))
        counts = Counter(max(s) for s in states)
        weights = Counter()
        for s in states:
            weights[max(s)] += 1 + sum(x * x for x in s)
        for radius in range(cutoff + 1):
            assert counts[radius] <= (radius + 1) ** 6
        for threshold in range(cutoff + 3):
            direct = sum(1 + sum(x * x for x in s)
                         for s in states if threshold <= max(s))
            partitioned = sum(weights[m] for m in range(threshold, cutoff + 1))
            assert direct == partitioned
            if threshold:
                base = threshold - 1
                assert all((max(s) >= threshold) == any(x > base for x in s)
                           for s in states)
            partitions += 1
        states_checked += len(states)
    print(f"PASS: {states_checked} exact six-label states; {partitions} weighted tail partitions")
    print("Every radius-M shell has at most (M+1)^6 states, with no duplicates.")
    print("Combinatorial pilot only; no finite sample is a physical trace certificate.")


if __name__ == "__main__":
    main()
