"""Exact arithmetic pilot; untrusted, no enumeration at growing cutoffs.

Source: (2k+14,0,0,0,0,0).  Its inward mate is (2k+13,1,1,1,1,1).
The competing physical target (2k+12,2,2,2,2,2) has the same source boundary
mask.  The mate/competitor heat ratio is
    32(2k+14) / [243(2k+13)] * w^(4k+2).
This tests a direct-mate probability floor, NOT a spectral gap.
"""

from fractions import Fraction


def fusion(a: int, b: int, c: int) -> bool:
    return abs(a - b) <= c <= a + b and (a + b + c) % 2 == 0


def main() -> None:
    # Edge patterns touching the distinguished face, or not touching it.
    for k in range(101):
        high = 2 * k + 14
        for a, b in ((high - 1, 1), (high - 2, 2)):
            assert a + b == high
            assert fusion(a, b, high) and fusion(b, b, 0)
        mate_dim = 32 * high
        competitor_dim = 243 * (high - 1)
        mate_c4 = (high - 1) * (high + 1) + 5 * 3
        competitor_c4 = (high - 2) * high + 5 * 8
        assert mate_dim <= competitor_dim
        assert mate_c4 == competitor_c4 + 4 * k + 2
        if k < 3:
            ratio = Fraction(mate_dim, competitor_dim) * Fraction(1, 400) ** (4 * k + 2)
            print(f"k={k}, cutoff={high}, exact mate/competitor ratio={ratio}")
    print("PASS: 101 exact dimension, Casimir, and admissible-edge checks.")
    print("Lean must prove all-index identities, masks, and the actual normalized probability bound.")


if __name__ == "__main__":
    main()
