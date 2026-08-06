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
    """Return the full p=2 fusion row in O(N^2) arithmetic operations.

    A pair ``(a,b)`` contributes the same positive weight to the arithmetic
    progression ``|a-b|, |a-b|+2, ..., a+b``.  Two parity-separated
    difference arrays therefore replace the old inner Clebsch-mode loop.
    """
    coeff = [(a + 1) * (w ** c4(a)) for a in range(n_cut + 1)]
    stop = 2 * n_cut
    diff = [0.0] * (stop + 3)
    for a, ca in enumerate(coeff):
        for b, cb in enumerate(coeff):
            term = ca * cb
            lo = abs(a - b)
            hi = a + b
            diff[lo] += term
            diff[hi + 2] -= term
    row = [0.0] * (stop + 1)
    for parity in (0, 1):
        running = 0.0
        for s in range(parity, stop + 1, 2):
            running += diff[s]
            row[s] = running
    return row


@dataclass(frozen=True)
class Minimum:
    slack: float
    index: int


def scan_scale(
    k: int,
) -> tuple[
    float,
    Minimum,
    Minimum,
    Minimum,
    Minimum,
    Minimum,
    Minimum,
    Minimum,
    Minimum,
]:
    n_cut, w, q = physical_coordinates(k)
    g = fusion_row_p2(n_cut, w)

    head_left = 2 * g[2]
    head_right = (q**5) * 3 * g[1]
    head = head_right / head_left

    odd_min = Minimum(inf, -1)
    half_time_odd_min = Minimum(inf, -1)
    for s in range(1, 2 * n_cut, 2):
        if s + 2 >= 2 * n_cut:
            break
        left = (s + 2) * (s + 3) * g[s] * g[s + 3]
        right = (q**4) * (s + 4) * (s + 1) * g[s + 2] * g[s + 1]
        slack = right / left
        if slack < odd_min.slack:
            odd_min = Minimum(slack, s)
        half_time_slack = ((w**2) * (s + 4) * (s + 1) * g[s + 2] * g[s + 1]) / left
        if half_time_slack < half_time_odd_min.slack:
            half_time_odd_min = Minimum(half_time_slack, s)

    even_min = Minimum(inf, -1)
    half_time_even_min = Minimum(inf, -1)
    for s in range(2, 2 * n_cut, 2):
        left = (s + 1) * (s + 1) * g[s - 1] * g[s + 1]
        right = (q**2) * s * (s + 2) * g[s] * g[s]
        slack = right / left
        if slack < even_min.slack:
            even_min = Minimum(slack, s)
        half_time_slack = (w * s * (s + 2) * g[s] * g[s]) / left
        if half_time_slack < half_time_even_min.slack:
            half_time_even_min = Minimum(half_time_slack, s)

    tail_min = Minimum(inf, -1)
    half_time_min = Minimum(inf, -1)
    for s in range(1, 2 * n_cut):
        left = (s + 1) * g[s + 1]
        right = (q ** (2 * s + 3)) * (s + 2) * g[s]
        slack = right / left
        if slack < tail_min.slack:
            tail_min = Minimum(slack, s)

        half_time_right = (w ** (s + 2)) * (s + 2) * g[s]
        half_time_slack = half_time_right / left
        if half_time_slack < half_time_min.slack:
            half_time_min = Minimum(half_time_slack, s)

    fixed_w_min = Minimum(inf, -1)
    fixed_w_from_two_min = Minimum(inf, -1)
    for t in range(1, 2 * n_cut):
        left = (t + 1) * (t + 1) * g[t - 1] * g[t + 1]
        right = w * t * (t + 2) * g[t] * g[t]
        slack = right / left
        if slack < fixed_w_min.slack:
            fixed_w_min = Minimum(slack, t)
        if t >= 2 and slack < fixed_w_from_two_min.slack:
            fixed_w_from_two_min = Minimum(slack, t)

    return (
        head,
        odd_min,
        even_min,
        half_time_odd_min,
        half_time_even_min,
        tail_min,
        half_time_min,
        fixed_w_min,
        fixed_w_from_two_min,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-k", type=int, default=5)
    args = parser.parse_args()

    print(
        " k    N       head       odd-min@index       even-min@index      "
        "ht-odd-min@index    ht-even-min@index   tail-min@index       "
        "half-time-min@index  fixed-w-min@index  "
        "fixed-w-t>=2-min@index"
    )
    for k in range(args.max_k + 1):
        n_cut, _, _ = physical_coordinates(k)
        (
            head,
            odd,
            even,
            half_time_odd,
            half_time_even,
            tail,
            half_time,
            fixed_w,
            fixed_w_from_two,
        ) = scan_scale(k)
        print(
            f"{k:2d} {n_cut:4d}  {head:11.8f}  "
            f"{odd.slack:11.8f}@{odd.index:<4d}  "
            f"{even.slack:11.8f}@{even.index:<4d}  "
            f"{half_time_odd.slack:11.8f}@{half_time_odd.index:<4d}  "
            f"{half_time_even.slack:11.8f}@{half_time_even.index:<4d}  "
            f"{tail.slack:11.8f}@{tail.index:<4d}  "
            f"{half_time.slack:11.8f}@{half_time.index:<4d}  "
            f"{fixed_w.slack:11.8f}@{fixed_w.index:<4d}  "
            f"{fixed_w_from_two.slack:11.8f}@{fixed_w_from_two.index:<4d}"
        )


if __name__ == "__main__":
    main()
