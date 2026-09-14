"""Exact scalar feasibility test for the proposed all-spatial forest count.

The count (8*L)^S is a PROPOSED bound, not a Lean theorem or an enumeration
of the original configurations.  This pilot only checks the scalar margin
available if that count, with no omitted multiplicities, is proved.
"""

from fractions import Fraction as F
import signal


def main():
    signal.alarm(30)
    w = F(1, 1024)
    roots = 2 * 6 * 67**4
    degree = 2 * 67 * 24
    scale = 900000
    assert degree <= scale and roots * degree <= scale**2
    # Binary parenthesis shape <= 4^S; summing component counts <= 2^S.
    proposed_spatial_base = 8 * scale
    odd_rate = 4 * w**3
    higher_rate = F(9, 2**52)
    spatial_entropy = proposed_spatial_base * odd_rate
    higher_entropy = roots * higher_rate
    assert 0 < spatial_entropy < 1 and 0 < higher_entropy < 1
    proposed_pair_budget = (
        8 * odd_rate**12 * spatial_entropy**6
        / (1 - spatial_entropy) / (1 - higher_entropy)
    )
    assert proposed_pair_budget <= F(1, 16) * w**36
    allowance = F(1, 4) - F(1, 2**19) - F(1, 2**26) - 2 * F(1, 2**14)
    assert allowance - F(1, 8) >= F(1, 16)
    print(f"Root capacity {roots}; neighbor capacity {degree}; scale {scale}")
    print(f"PROPOSED spatial count base: {proposed_spatial_base}")
    print(f"PROPOSED pair budget / w^36: {float(proposed_pair_budget / w**36):.12g}")
    print("Scalar feasibility PASS; full forest injection/count and original sum OPEN.")
    print("Fixed nome only: no beta-uniform or continuum mass-gap conclusion.")


if __name__ == "__main__":
    main()
