"""Untrusted exact pilot for the all-cube balanced difference-boundary move.

No kernel enumeration or floating-point oracle.  The scalar rounding,
fusion channels, and Casimir bounds are separately formalized in Lean.
"""

from itertools import product
from random import Random


def label(radius: int, spin: int) -> int:
    return 2 * ((2 * (spin // 2)) // 3 + (radius + 11) // 12)


def fusion(a: int, b: int, c: int) -> bool:
    return abs(a - b) <= c <= a + b and (a + b + c) % 2 == 0


def check(spins: tuple[int, ...]) -> None:
    radius = max(spins)
    target = tuple(label(radius, s) for s in spins)
    assert all(t % 2 == 0 for t in target)
    assert max(target) <= max(radius, 2)
    assert all(6 * t <= 4 * s + radius + 11 for s, t in zip(spins, target))
    assert 6 * max(0, max(target) - 11) <= 5 * max(0, radius - 11)
    if radius >= 12:
        assert max(target) < radius
    for i in range(6):
        for j in range(i):
            assert fusion(target[i], target[j], abs(spins[i] - spins[j]))
    energy = sum(s * (s + 2) for s in spins)
    target_energy = sum(t * (t + 2) for t in target)
    # Round-up error and the six-face quadratic reserve, with rational
    # denominators cleared. This is NOT a transition probability estimate.
    assert 36 * target_energy + radius * radius <= 36 * energy + 648 * radius + 1728
    if radius >= 1400:
        assert 72 * target_energy + radius * radius <= 72 * energy
        assert 864 * target_energy <= 863 * energy


def main() -> None:
    count = 0
    for parity in (0, 1):
        for raw in product(range(5), repeat=6):
            check(tuple(2 * s + parity for s in raw))
            count += 1
    rng = Random(260912)
    for _ in range(4000):
        parity = rng.randrange(2)
        check(tuple(2 * rng.randrange(100_000) + parity for _ in range(6)))
        count += 1
    for radius in (12, 13, 1399, 1400, 1401, 10_000):
        parity = radius % 2
        for low in (parity, 2 * (radius // 8) + parity, radius):
            check((radius, low, low, low, low, low))
            count += 1
    print(f"PASS: {count} exact common-parity cube samples")
    print("36*C4(target)+M^2 <= 36*C4(source)+648*M+1728")
    print("For M>=1400: 72*C4(target)+M^2 <= 72*C4(source)")
    print("Selected-boundary geometry only; full diagonal/row comparison remains separate.")


if __name__ == "__main__":
    main()
