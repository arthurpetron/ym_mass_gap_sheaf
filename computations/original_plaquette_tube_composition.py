"""Exact selected-channel tube propagation over three time layers.

The boundary polynomial remains symbolic. This is not the full interacting
covariance: spatial plaquette weights and signed dressing are not included.
Lean independently proves the all-length composition theorem.
"""

from fractions import Fraction
import json
import signal

from computations.exact_haar_network import (
    chi, holonomy, p_add_into, p_mul, p_scale_s, P_ONE, integrate_link, integrate_link_linear_factors,
)
from computations.dual_half_time_reflection_route import boundary_complete_slab_plaquettes


def pilot(layers: int = 3) -> dict:
    signs = [1, 1, -1, -1]
    current = chi(1, holonomy(list(enumerate(signs))))
    trace = []
    for layer in range(layers):
        for edge in range(4):
            lower = 4 * layer + edge
            upper = lower + 4
            side = chi(1, holonomy([(lower, 1), (upper, -1)]))
            current = integrate_link_linear_factors([current, side], lower)
        top = [(4 * (layer + 1) + edge, sign) for edge, sign in enumerate(signs)]
        expected = p_scale_s(chi(1, holonomy(top)), 0, Fraction(1, 16 ** (layer + 1)))
        assert current == expected
        trace.append({"layer": layer + 1, "coefficient": str(Fraction(1, 16 ** (layer + 1))),
                      "terms": len(current)})
    end_character = chi(1, holonomy([(4 * layers + e, s) for e, s in enumerate(signs)]))
    closed = p_mul(current, end_character)
    one_end = current
    for edge in range(4):
        closed = integrate_link(closed, 4 * layers + edge)
        one_end = integrate_link(one_end, 4 * layers + edge)
    assert closed == {(): {0: Fraction(1, 16 ** layers)}}
    assert one_end == {}
    assert Fraction(2) ** (4 * layers) / 16 ** layers == 1
    for c, d in [(Fraction(1, 3), Fraction(-2, 5)), (Fraction(-7), Fraction(11))]:
        centered = chi(1, holonomy(list(enumerate(signs))))
        p_add_into(centered, P_ONE, -c)
        for layer in range(layers):
            for edge in range(4):
                lower = 4 * layer + edge
                side = chi(1, holonomy([(lower, 1), (lower + 4, -1)]))
                centered = integrate_link(p_mul(centered, side), lower)
        end_shifted = {m: dict(v) for m, v in end_character.items()}
        p_add_into(end_shifted, P_ONE, -d)
        centered = p_mul(centered, end_shifted)
        for edge in range(4):
            centered = integrate_link(centered, 4 * layers + edge)
        assert centered == closed
    faces = boundary_complete_slab_plaquettes(3)
    ends = [((1, 1, 1, t), (0, 1)) for t in [0, 3]]
    sides = [face for t in range(3) for face in [
        ((1, 1, 1, t), (0, 3)), ((2, 1, 1, t), (1, 3)),
        ((1, 2, 1, t), (0, 3)), ((1, 1, 1, t), (1, 3)),
    ]]
    assert len(set(sides)) == 12 and all(face in faces for face in ends + sides)
    return {"layers": layers, "trace": trace, "closed_bare_coefficient": str(Fraction(1, 16 ** layers)),
            "weighted_coefficient": f"w^{12 * layers}", "one_end_moment": 0,
            "centering_regressions": 2, "extent_three_endpoint_ids": [faces.index(f) for f in ends],
            "extent_three_side_ids": [faces.index(f) for f in sides],
            "full_interacting_response_floor": "NOT PROVED"}


if __name__ == "__main__":
    signal.alarm(30)
    print(json.dumps(pilot(), separators=(",", ":")))
