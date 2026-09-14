"""Exact scalar certificate pilot for the original large-core remainder.

No original numerator or bounded-size core coefficient is evaluated here.
Lean independently checks the scalar blocks and proves their application.
"""

from fractions import Fraction as F
import signal


def main():
    signal.alarm(30)
    nome = F(1, 1024)
    delta = 128 * nome**3
    inverse = 1 / (1 - delta)
    paired = 2 * delta + delta**2
    entropy = 625 * paired * inverse**48
    block = F(1025, 1024)
    assert inverse**8 <= block
    assert block**6 <= F(17, 16)
    assert block**12 <= 2
    assert 625 * paired * F(17, 16) <= F(1, 4096)
    assert 1 / (1 - entropy) <= 2
    reference_half = nome**36 / 4
    for threshold in (30, 31, 32, 33):
        exact = 8 * inverse**96 * 1562500 * entropy**threshold / (1 - entropy)
        dyadic = 16 * 1562500 * F(1, 4096)**threshold * 2
        assert exact <= dyadic
        print(f"threshold={threshold}; exact tail / (w^36/4)~{float(exact/reference_half):.9g}; "
              f"dyadic ceiling / (w^36/4)~{float(dyadic/reference_half):.9g}")
    assert 16 * 1562500 * F(1, 4096)**33 * 2 <= reference_half
    print("Certificate threshold: 33; unresolved other-core window: 12 through 32 faces.")
    print("OPEN: short-core signed bound, positive full response, limits, continuum/Clay.")


if __name__ == "__main__":
    main()
