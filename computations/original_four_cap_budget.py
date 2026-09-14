"""Exact scalar pilot for four spatial occurrences paired in projection.

This neither enumerates original configurations nor evaluates Haar weights.
The geometric pairing, injection, occupation floor, and use in the original
sum must be independently proved in Lean before claiming an aggregate bound.
"""

from fractions import Fraction as F
import signal


def main():
    signal.alarm(30)
    w = F(1, 1024)
    face_capacity = 6 * 67**4
    # Five replica splits, three pairings, two literal anchors, two times.
    spatial_capacity = 5 * 3 * face_capacity**2 * 67**2
    higher_capacity = 2 * face_capacity
    odd_rate = 4 * w**3
    relative_higher_rate = F(9, 2**52)
    entropy = higher_capacity * relative_higher_rate
    assert 0 < entropy < 1
    pair_budget = 8 * spatial_capacity * odd_rate**16 / (1 - entropy)
    assert pair_budget <= F(1, 2**15) * w**36
    assert 2 * pair_budget <= F(1, 2**14) * w**36
    print(f"Spatial code capacity: {spatial_capacity}; higher alphabet: {higher_capacity}")
    print(f"Proposed pair sum / w^36: {float(pair_budget / w**36):.9g}")
    print("Scalar cap: pair sum <= 2^-15*w^36; detached remainder <= 2^-14*w^36*Z^2.")
    print("Lean verification: BF4ExactSlabFourCapPairCount, FourCapPairSum and FourCapRemainderBound.")
    print("OPEN: six-or-more spatial faces, positive full response, continuum/Clay.")


if __name__ == "__main__":
    main()
