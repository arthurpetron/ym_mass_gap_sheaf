"""Exact untrusted pilot for rooted head-energy and gap-conversion algebra.

The test kernels are finite path Grams, not BF4 numerical surrogates used as
proof inputs. Lean must prove the BF4 embedding and persistent-floor instance.
"""

from fractions import Fraction as F
from itertools import product


def main():
    checks = 0
    floor = F(1, 22)
    for n in range(2, 7):
        head_size = min(3, n)
        scale = 1 + head_size**2
        constant = scale / floor
        joint = [[F(2 if i == j else int(abs(i-j) == 1), 4*n-2)
                  for j in range(n)] for i in range(n)]
        weight = [sum(row) for row in joint]
        for f in product((-1, 0, 1), repeat=n):
            energy = sum(joint[i][j] * (f[i]-f[j])**2
                         for i in range(n) for j in range(n))
            head = sum(weight[i] * (f[i]-f[0])**2 for i in range(head_size))
            assert floor * head <= scale * energy
            assert head <= constant * energy
            checks += 1
    for c in (F(1, 100), F(1), F(10), F(220)):
        rate = (1 + 6*c) / (2 + 6*c)
        assert 0 < rate < 1
        assert 1 - rate == 1 / (2 * (1 + 3*c))
    print(f"PASS: {checks} exact rooted path-head bounds; four strict-rate identities")


if __name__ == "__main__":
    main()
