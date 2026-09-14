"""Exact literal tube ordering with the entire spectator carrier retained.

The raw link numbering follows Lean's first-occurrence A,D,C,B order.
These finite regressions are not a proof oracle; Lean constructs the
all-margin embedding from geometric membership and injectivity.
"""

import json
import signal

from computations.dual_half_time_reflection_route import boundary_complete_slab_plaquettes
from computations.dual_positivity_geometry_bridge import edges_of


def pilot():
    rows = []
    for margin in range(3):
        extent = 2 * margin + 3
        faces = boundary_complete_slab_plaquettes(extent)
        links = list(dict.fromkeys(link for face in faces for link in edges_of(face)))
        indices = {link: i for i, link in enumerate(links)}
        tube = [link for time in range(4) for link in [
            ((1+margin,1+margin,1+margin,margin+time),0),
            ((2+margin,1+margin,1+margin,margin+time),1),
            ((1+margin,2+margin,1+margin,margin+time),0),
            ((1+margin,1+margin,1+margin,margin+time),1),
        ]]
        prefix = [indices[link] for link in tube]
        assert len(set(prefix)) == 16
        order = prefix + [i for i in range(len(links)) if i not in prefix]
        assert sorted(order) == list(range(len(links))) and order[:16] == prefix
        rows.append({"margin": margin, "extent": extent, "blocks": len(links),
                     "tube_blocks": prefix, "spectator_blocks": len(links)-16})
    return {"rows": rows, "interacting_response_floor": "NOT PROVED"}


if __name__ == "__main__":
    signal.alarm(30)
    print(json.dumps(pilot(), separators=(",", ":")))
