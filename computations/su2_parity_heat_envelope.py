"""Bounded scalar pilot; Lean independently checks the all-spin envelope.

This does not enumerate spatial defects or evaluate the original signed
short-core sum. No numerical value here is used as a proof oracle.
"""

from fractions import Fraction
import signal


def main():
    signal.alarm(30)
    for spin in range(10001):
        bit, higher = spin % 2, spin // 2
        assert spin == 2 * higher + bit
        assert 3 * bit + 8 * higher <= spin * (spin + 2)
        assert (spin + 1) ** 2 <= 4 ** bit * 9 ** higher
    for nome in (Fraction(0), Fraction(1, 1024), Fraction(1, 4), Fraction(1)):
        for spin in range(13):
            original = (spin + 1) ** 2 * nome ** (spin * (spin + 2))
            envelope = (4 * nome ** 3) ** (spin % 2) * (9 * nome ** 8) ** (spin // 2)
            assert original <= envelope
    nome = Fraction(1, 1024)
    odd, higher = 4 * nome ** 3, 9 * nome ** 8
    assert 0 < higher < Fraction(1, 2)
    factor = 1 / (1 - higher)
    assert factor <= 1 + 2 * higher
    zero_spatial_relative = Fraction(9, 2 ** 53)
    assert 8 * odd ** 12 * higher == zero_spatial_relative * nome ** 36
    for bit in range(2):
        for count in range(13):
            total = sum((2 * h + bit + 1) ** 2 * nome ** ((2 * h + bit) * (2 * h + bit + 2))
                        for h in range(count))
            assert total <= odd ** bit * factor
    print("10001 labels: parity/higher Casimir and squared-dimension inequalities hold.")
    print("52 rational label cases include nome zero and one; 26 parity-prefix checks passed.")
    print(f"At nome 1/1024: odd rate = {odd}; higher rate = {higher}.")
    print("The higher-label sum has factor 1/(1-r), bounded by 1+2r when r<=1/2.")
    print(f"Zero-spatial non-tube per-pair cap relative to w^36: {zero_spatial_relative}.")
    print("OPEN: admissible spatial-defect counting and original signed short-core smallness.")


if __name__ == "__main__":
    main()
