"""Exact, untrusted pilot for the full cube boundary upper bound.

The Lean proof must establish every cutoff, not just these finite samples.
No spectral-gap claim is tested or inferred here.
"""

from fractions import Fraction
from itertools import product


EDGES = ((0, 1, 2), (0, 3, 4), (0, 19, 20), (0, 39, 40),
         (1, 3, 5), (1, 9, 11), (1, 39, 41), (3, 9, 13),
         (3, 19, 23), (9, 19, 29), (9, 39, 49), (19, 39, 59))
CORNERS = ((2, 4, 5), (2, 40, 41), (4, 20, 23), (5, 11, 13),
           (11, 41, 49), (13, 23, 29), (20, 40, 59), (29, 49, 59))
FACES = (0, 1, 3, 9, 19, 39)


def fusion(a: int, b: int, c: int) -> bool:
    return abs(a - b) <= c <= a + b and (a + b + c) % 2 == 0


def main() -> None:
    tails = boundaries = 0
    for w in (Fraction(0), Fraction(1, 400), Fraction(1, 10), Fraction(1, 2)):
        heat = [(s + 1) * w ** (s * (s + 2)) for s in range(26)]
        for d in range(17):
            for n in range(26):
                assert sum(heat[d:n]) <= 2 * heat[d]
                tails += 1
        if not w:
            continue
        for cutoff in range(5):
            samples = {(s,) * 6 for s in range(cutoff + 1)}
            samples.update((s, s % 2, s % 2, s % 2, s % 2, s % 2)
                           for s in range(cutoff + 1))
            for values in sorted(samples):
                state = dict(zip(FACES, values))
                choices = [tuple(c for c in range(cutoff + 1)
                                 if fusion(state[a], state[b], c))
                           for a, b, _ in EDGES]
                overlap = Fraction(0)
                for labels in product(*choices):
                    boundary = dict(zip((e[2] for e in EDGES), labels))
                    if all(fusion(boundary[a], boundary[b], boundary[c])
                           for a, b, c in CORNERS):
                        term = Fraction(1)
                        for s in labels:
                            term *= heat[s]
                        overlap += term
                minimal = Fraction(1)
                for a, b, _ in EDGES:
                    minimal *= heat[abs(state[a] - state[b])]
                assert overlap <= 4096 * minimal
                boundaries += 1
    print(f"PASS: {tails} exact scalar tails; {boundaries} full boundary sums")
    print("For 0 <= w <= 1/2: overlap(s,s) <= 2^12 * heat(difference(s))")
    print("Constant 4096 is cutoff-independent, not a spectral-gap rate.")


if __name__ == "__main__":
    main()
