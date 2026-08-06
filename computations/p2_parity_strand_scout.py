"""Scout the fixed-power p=2 parity-strand certificate.

This is an untrusted numerical mirror of
``P2RetunedParityStrandCompiler.P2RetunedCoreParityStrands``.  It does not
certify Lean theorems.  Its purpose is to test the proposed uniform invariant,
locate the least slack, and keep false strengthened carriers out of the proof
frontier.

Physical schedule coordinates are exact before conversion to floating point:

    N_k = 5*2^k - 1,
    w_k = 1 - 1/(12*4^k),
    q_k = 1 - 1/(24*4^k).

For ``g_s = boxSum(w_k,N_k,s)``, the reduced transition checks are

    odd s:   (s+2)(s+3) g_s g_{s+3}
             <= q^4 (s+4)(s+1) g_{s+2} g_{s+1},

    even s:  (s+1)^2 g_{s-1} g_{s+1}
             <= q^2 s(s+2) g_s^2.

The reported slack is right/left, so every required value must be at least 1.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from math import inf


def c4(s: int) -> int:
    return s * (s + 2)


def physical_coordinates(k: int) -> tuple[int, float, float]:
    den = 12 * (4**k)
    return 5 * (2**k) - 1, (den - 1) / den, (2 * den - 1) / (2 * den)


def fusion_row_p2(n_cut: int, w: float) -> list[float]:
    coeff = [(a + 1) * (w ** c4(a)) for a in range(n_cut + 1)]
    row = [0.0] * (2 * n_cut + 1)
    for a, ca in enumerate(coeff):
        for b, cb in enumerate(coeff):
            term = ca * cb
            for s in range(abs(a - b), a + b + 1, 2):
                row[s] += term
    return row


@dataclass(frozen=True)
class Minimum:
    slack: float
    index: int


def scan_scale(k: int) -> tuple[float, Minimum, Minimum, Minimum]:
    n_cut, w, q = physical_coordinates(k)
    g = fusion_row_p2(n_cut, w)

    head_left = 2 * g[2]
    head_right = (q**5) * 3 * g[1]
    head = head_right / head_left

    odd_min = Minimum(inf, -1)
    for s in range(1, 2 * n_cut, 2):
        if s + 2 >= 2 * n_cut:
            break
        left = (s + 2) * (s + 3) * g[s] * g[s + 3]
        right = (q**4) * (s + 4) * (s + 1) * g[s + 2] * g[s + 1]
        slack = right / left
        if slack < odd_min.slack:
            odd_min = Minimum(slack, s)

    even_min = Minimum(inf, -1)
    for s in range(2, 2 * n_cut, 2):
        left = (s + 1) * (s + 1) * g[s - 1] * g[s + 1]
        right = (q**2) * s * (s + 2) * g[s] * g[s]
        slack = right / left
        if slack < even_min.slack:
            even_min = Minimum(slack, s)

    tail_min = Minimum(inf, -1)
    for s in range(1, 2 * n_cut):
        left = (s + 1) * g[s + 1]
        right = (q ** (2 * s + 3)) * (s + 2) * g[s]
        slack = right / left
        if slack < tail_min.slack:
            tail_min = Minimum(slack, s)

    return head, odd_min, even_min, tail_min


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-k", type=int, default=5)
    args = parser.parse_args()

    print(" k    N       head       odd-min@index       even-min@index      tail-min@index")
    for k in range(args.max_k + 1):
        n_cut, _, _ = physical_coordinates(k)
        head, odd, even, tail = scan_scale(k)
        print(
            f"{k:2d} {n_cut:4d}  {head:11.8f}  "
            f"{odd.slack:11.8f}@{odd.index:<4d}  "
            f"{even.slack:11.8f}@{even.index:<4d}  "
            f"{tail.slack:11.8f}@{tail.index:<4d}"
        )


if __name__ == "__main__":
    main()
