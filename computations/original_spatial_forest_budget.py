"""Exact scalar crosscheck for the original all-spatial forest budget.

The count is now proved in BF4ExactSlabSpatialForestPairCount, the weighted
sum in BF4ExactSlabSpatialForestPairSum, and the original thermodynamic
response floor in BF4ExactSlabThermodynamicPositiveResponse. This pilot
only crosschecks scalar arithmetic; Lean independently proves the source
count, original weighted sum, limit transport and certificate acceptance.
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
    spatial_base = 8 * scale
    odd_rate = 4 * w**3
    higher_rate = F(9, 2**52)
    spatial_entropy = spatial_base * odd_rate
    higher_entropy = roots * higher_rate
    assert 0 < spatial_entropy < 1 and 0 < higher_entropy < 1
    pair_budget = (
        8 * odd_rate**12 * spatial_entropy**6
        / (1 - spatial_entropy) / (1 - higher_entropy)
    )
    assert pair_budget <= F(1, 16) * w**36
    allowance = F(1, 4) - F(1, 2**19) - F(1, 2**26) - 2 * F(1, 2**14)
    assert allowance - F(1, 8) >= F(1, 16)
    print(f"Root capacity {roots}; neighbor capacity {degree}; scale {scale}")
    print(f"Spatial count base: {spatial_base}")
    print(f"Pair budget / w^36: {float(pair_budget / w**36):.12g}")
    print("Scalar crosscheck PASS; original count, sum and response have separate Lean proofs.")
    print("Fixed nome only: no beta-uniform or continuum mass-gap conclusion.")


if __name__ == "__main__":
    main()
