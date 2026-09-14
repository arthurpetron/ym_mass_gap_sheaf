"""Exact scalar pilot for the original two-spatial-cap short family.

This does not count physical configurations or evaluate their Haar weights.
Lean must independently prove the cap/higher-code injection and its use
in the original signed sum with each core's own detached partition.
"""

from fractions import Fraction as F
import signal


def main():
    signal.alarm(30)
    w = F(1, 1024)
    face_capacity = 6 * 67**4
    spatial_capacity = 3 * face_capacity * 67
    higher_capacity = 2 * face_capacity
    odd_rate = 4 * w**3
    higher_rate = 9 * w**8
    relative_higher_rate = F(9, 2**52)
    assert higher_rate == odd_rate * relative_higher_rate
    entropy = higher_capacity * relative_higher_rate
    assert 0 < entropy < 1
    fundamental = 8 * spatial_capacity * odd_rate**16
    higher = 8 * spatial_capacity * odd_rate**14 * entropy / (1 - entropy)
    pair_budget = fundamental + higher
    assert pair_budget <= F(1, 2**15) * w**36
    assert 2 * pair_budget <= F(1, 2**14) * w**36
    print(f"Spatial code capacity: {spatial_capacity}; higher alphabet: {higher_capacity}")
    print(f"Higher entropy rate: {entropy}; approximately {float(entropy):.9g}")
    print(f"Proposed pair sum / w^36: {float(pair_budget / w**36):.9g}")
    print("Scalar cap: pair sum <= 2^-15*w^36; detached remainder <= 2^-14*w^36*Z^2.")
    print("Lean verification: BF4ExactSlabTwoCapPairCount, TwoCapPairSum and TwoCapRemainderBound.")
    print("OPEN: four-or-more spatial faces, positive full response, continuum/Clay.")


if __name__ == "__main__":
    main()
