"""Untrusted exact algebra pilot; not a Haar-network or BF4 kernel oracle."""

from fractions import Fraction as F


def main():
    checked = 0
    for w in (F(1, 400), F(1, 2), F(8, 9), F(1)):
        activity = (2 * w**3) ** 6
        assert activity == 64 * w**18
        upper = 1 / (1 + activity)
        floor = activity / (1 + activity)
        assert floor > 0 and floor + upper == 1
        for i in range(101):
            physical_value = upper * F(i, 100)
            assert floor <= 1 - physical_value
            checked += 1
        if w == F(1, 400):
            print(f"anchor discrepancy floor = {floor}")
    print(f"PASS: {checked} exact rational separation implications")


if __name__ == "__main__":
    main()
