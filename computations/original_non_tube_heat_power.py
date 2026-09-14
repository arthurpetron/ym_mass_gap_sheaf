"""Finite scalar pilot for the first SU(2) heat-power excess.

The original leading-tube uniqueness and signed cancellations are Lean
theorems, not tested by this scalar pilot. No residual magnitude is bounded.
"""

import signal


def main():
    signal.alarm(30)
    for spin in range(10001):
        excess = max(spin * (spin + 2) - 3, 0)
        assert excess == 0 or excess >= 5
    reachable = {0}
    below_39 = set()
    for count in range(1, 33):
        reachable = {old + spin * (spin + 2)
                     for old in reachable for spin in range(1, 8)
                     if old + spin * (spin + 2) <= 60}
        if count >= 12:
            below_39.update(power for power in reachable if power < 39)
    assert below_39 == {36}
    assert 13 * 3 == 39
    print("10001 scalar spins: Casimir excess is zero or at least five.")
    print("12..32 occupied labels, tested spins 1..7, powers <=60: below 39 only 36 is reachable.")
    print("Lean independently proves the all-spin statement and removes power 36 on each non-tube core.")
    print("OPEN: uniform magnitude of the exact signed cofactor; positive full response; continuum/Clay.")


if __name__ == "__main__":
    main()
