"""Small untrusted check of the inward-mate orbit formula, not OS coverage.

Lean proves the formula for every cutoff independently of this enumeration.
No kernel weights or successful-source completeness are tested here.
"""

from itertools import product


def mate(labels):
    return tuple(1 if label == 0 else label - 1 for label in labels)


def orbit(labels, steps):
    for _ in range(steps):
        labels = mate(labels)
    return labels


def main():
    for cutoff in range(1, 6):
        checked = 0
        for parity in (0, 1):
            for labels in product(range(parity, cutoff + 1, 2), repeat=6):
                steps = 2 * (cutoff // 2) + parity
                assert steps <= cutoff + 1
                assert orbit(labels, steps) == (0,) * 6
                checked += 1
        print(f"K={cutoff}: {checked} uniform-parity cube states reach zero")
    sector_two = {(1,) * 6} | set(product((0, 2), repeat=6))
    assert len(sector_two) == 65
    assert all(mate(state) in sector_two for state in sector_two)
    assert all(mate(state) == (1,) * 6 for state in sector_two - {(1,) * 6})
    assert mate((1,) * 6) == (0,) * 6
    print("Cutoff-two potential mate graph: every state reaches zero in <= 2 moves")
    print("Scope: label geometry only; selected-source coverage is not checked.")


if __name__ == "__main__":
    main()
