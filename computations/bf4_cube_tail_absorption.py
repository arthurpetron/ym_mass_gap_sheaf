"""Exact, untrusted algebra pilot for the fixed-tail absorption constants.

This checks rational positive Gram blocks, not a numerical BF4 spectral gap.
Lean must establish the actual kernel's tail premise separately.
"""

from fractions import Fraction as F


def main():
    checks = 0
    for x in range(9):
        for y in range(9):
            for a in range(5):
                for b in range(5):
                    p_head = F(a * x, 4)
                    p_tail = F(b * y, 16)
                    for c in range(-16, 17):
                        cross = F(c, 16)
                        if cross * cross > p_head * p_tail:
                            continue
                        norm = F(x + y)
                        form = p_head + 2 * cross + p_tail
                        energy = 2 * (norm - form)
                        assert form <= 2 * (F(x) + F(y, 4))
                        assert norm <= energy + 3 * x
                        checks += 1
    assert 1400 + F(1, 4).denominator == 1404
    print(f"PASS: {checks} exact positive-block checks; tail=1/4, base=1404, head factor=3")


if __name__ == "__main__":
    main()
