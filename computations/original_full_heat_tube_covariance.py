"""Exact conditional tube covariance pilot, not the full interacting law.

All heat spins are included before integration. The surviving boundary
contains a nonconstant linear weight, so its mean cannot be dropped.
Lean proves the symbolic conditional identities independently of this pilot.
"""

from fractions import Fraction
import json
import signal

from computations.exact_haar_network import (
    P_ONE, chi, holonomy, heat_activity, p_mul, p_add_into, p_scale_s,
    p_reduce_units, integrate_link, sp_mul, sp_add, sp_scale,
)


def integrate_all(polynomial, links):
    for link in links:
        polynomial = integrate_link(polynomial, link)
    assert set(polynomial) <= {()}
    return polynomial.get((), {})


def pilot():
    reference = chi(1, holonomy(list(enumerate((1, 1, -1, -1)))))
    bare_z = integrate_all(P_ONE, range(4))
    bare_mean = integrate_all(reference, range(4))
    bare_square = integrate_all(p_mul(reference, reference), range(4))
    bare_variance = sp_add(sp_mul(bare_z, bare_square), sp_scale(sp_mul(bare_mean, bare_mean), -1))
    assert bare_z == {0: Fraction(1)}
    assert bare_mean == {}
    assert bare_variance == {0: Fraction(1)}
    boundary = {m: dict(c) for m, c in P_ONE.items()}
    p_add_into(boundary, p_scale_s(reference, 0, Fraction(1, 4)))
    z = integrate_all(boundary, range(4))
    a = integrate_all(p_mul(reference, boundary), range(4))
    b = integrate_all(p_mul(p_mul(reference, reference), boundary), range(4))
    variance_numerator = sp_add(sp_mul(z, b), sp_scale(sp_mul(a, a), -1))
    assert z == {0: Fraction(1)}
    assert a == {0: Fraction(1, 4)}
    assert b == {0: Fraction(1)}
    assert variance_numerator == {0: Fraction(15, 16)}
    rows = []
    for cutoff in (1, 2, 3):
        transmitted = chi(1, holonomy([(e, s) for e, s in enumerate((1, 1, -1, -1))]))
        vacuum = P_ONE
        for layer in range(3):
            for edge in range(4):
                lower = 4 * layer + edge
                kernel = heat_activity(holonomy([(lower, 1), (lower + 4, -1)]), cutoff)
                transmitted = p_reduce_units(integrate_link(p_mul(transmitted, kernel), lower))
                vacuum = p_reduce_units(integrate_link(p_mul(vacuum, kernel), lower))
            assert vacuum == P_ONE
            upper = chi(1, holonomy([(4 * (layer + 1) + e, s) for e, s in enumerate((1, 1, -1, -1))]))
            assert transmitted == p_scale_s(upper, 12 * (layer + 1))
            rows.append({"cutoff": cutoff, "layers": layer + 1,
                         "connected_numerator": f"(15/16)*w^{12*(layer+1)}",
                         "normalized_covariance": f"(15/16)*w^{12*(layer+1)}"})
    return {"checks": rows, "bare_boundary_variance": "1; bare tube connected numerator w^36",
            "boundary": "1+P_upper/4; reference moments checked on four blocks",
            "interacting_remainder": "NOT BOUNDED"}


if __name__ == "__main__":
    signal.alarm(30)
    print(json.dumps(pilot(), separators=(",", ":")))
