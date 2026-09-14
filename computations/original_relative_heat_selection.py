"""Exact two-link solid-character selection; not a full-action estimate.

All retained V coordinates remain symbolic. The ordinary and solid
characters agree on unit quaternions, not as raw off-sphere polynomials.
Lean must independently prove the all-spin identity.
"""

from fractions import Fraction
import json
import signal

from computations.exact_haar_network import (
    P_ONE, p_var, p_mul, p_add_into, p_scale_s, q_link, q_conj, q_mul,
    integrate_link,
)


def pilot():
    scalar = q_mul(q_link(0), q_conj(q_link(1)))[0]
    radii = []
    for link in range(2):
        radius = {}
        for i in range(4):
            p_add_into(radius, p_mul(p_var(link, i), p_var(link, i)))
        radii.append(radius)
    radius_product = p_mul(*radii)
    characters = [P_ONE, p_scale_s(scalar, 0, Fraction(2))]
    for spin in range(4):
        next_character = p_scale_s(p_mul(scalar, characters[-1]), 0, Fraction(2))
        p_add_into(next_character, p_mul(radius_product, characters[-2]), -1)
        characters.append(next_character)
    checks = []
    for spin, character in enumerate(characters):
        for i in range(4):
            value = integrate_link(p_mul(character, p_var(0, i)), 0)
            expected = p_scale_s(p_var(1, i), 0, Fraction(1, 2)) if spin == 1 else {}
            assert value == expected, (spin, i)
        checks.append({"spin": spin, "terms": len(character), "components_checked": 4})
    heat_checks = 0
    for w in (Fraction(1, 1024), Fraction(1, 4), Fraction(2, 3)):
        for cutoff in range(1, 6):
            for i in range(4):
                value = {}
                for spin in range(cutoff + 1):
                    coefficient = (spin + 1) * w ** (spin * (spin + 2))
                    p_add_into(value, integrate_link(p_mul(characters[spin], p_var(0, i)), 0), coefficient)
                assert value == p_scale_s(p_var(1, i), 0, w ** 3)
                heat_checks += 1
    return {"checks": checks, "heat_checks": heat_checks, "retained_tail": "symbolic V",
            "fundamental_coefficient": "1/2", "full_interacting_bound": "NOT PROVED"}


if __name__ == "__main__":
    signal.alarm(30)
    print(json.dumps(pilot(), separators=(",", ":")))
