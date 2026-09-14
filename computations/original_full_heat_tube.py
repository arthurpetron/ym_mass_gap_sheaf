"""Exact full-packet bare tube pilot; not the interacting covariance.

Every character spin is retained before each integration. Exact sphere-ideal
reduction removes radius-one factors. The surviving upper boundary remains
symbolic; no numeric quaternion samples or proof-oracle claims are used.
"""

import json
import signal

from computations.exact_haar_network import (
    chi, holonomy, heat_activity, p_mul, p_scale_s, p_reduce_units, integrate_link,
)


def pilot():
    signs = [1, 1, -1, -1]
    checks = []
    for cutoff in (1, 2, 3):
        current = chi(1, holonomy(list(enumerate(signs))))
        for layer in range(3):
            for edge in range(4):
                lower = 4 * layer + edge
                kernel = heat_activity(holonomy([(lower, 1), (lower + 4, -1)]), cutoff)
                current = p_reduce_units(integrate_link(p_mul(current, kernel), lower))
            upper = chi(1, holonomy([(4 * (layer + 1) + e, s) for e, s in enumerate(signs)]))
            assert current == p_scale_s(upper, 12 * (layer + 1))
            checks.append({"cutoff": cutoff, "layers": layer + 1,
                           "transmission": f"w^{12 * (layer + 1)}", "retained_terms": len(current)})
    return {"checks": checks, "nome": "symbolic", "boundary": "symbolic upper plaquette",
            "full_interacting_response_floor": "NOT PROVED"}


if __name__ == "__main__":
    signal.alarm(30)
    print(json.dumps(pilot(), separators=(",", ":")))
