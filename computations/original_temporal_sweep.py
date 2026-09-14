"""Exact shared-link word regression for an ascending temporal gauge sweep.

All faces, including the boundary fallbacks, use one assignment per cut.
Free/cyclic word reduction checks character identities, not Haar invariance
or a covariance lower bound. Lean proves the change of variables separately.
"""

import json
import signal

from computations.boundary_spatial_flatness_coercivity import _signed_boundary
from computations.dual_half_time_reflection_route import boundary_complete_slab_plaquettes
from computations.dual_positivity_geometry_bridge import add_e, edges_of


def inverse(word):
    return [(link, -sign) for link, sign in reversed(word)]


def cyclic(word):
    reduced = []
    for link, sign in word:
        if reduced and reduced[-1] == (link, -sign):
            reduced.pop()
        else:
            reduced.append((link, sign))
    while len(reduced) >= 2 and reduced[0] == (reduced[-1][0], -reduced[-1][1]):
        reduced = reduced[1:-1]
    return tuple(reduced)


def pilot():
    counts = []
    for extent in [1, 2, 3]:
        faces = boundary_complete_slab_plaquettes(extent)
        links = {link for face in faces for link in edges_of(face)}

        def raw(link):
            return [(link, 1)] if link in links else []

        for cut in range(extent):
            def transformed(link):
                if link[0][3] <= cut:
                    return raw(link)
                start, direction = link
                end = add_e(start, direction)
                return (inverse(raw(((start[0], start[1], start[2], cut), 3))) + raw(link)
                        + raw(((end[0], end[1], end[2], cut), 3)))

            def swept(face, stop, assignment):
                boundary = _signed_boundary(face)
                if face[1][1] == 3 and face[0][3] < stop:
                    boundary = (boundary[0], boundary[2])
                word = []
                for link, sign in boundary:
                    term = assignment(link)
                    word += term if sign == 1 else inverse(term)
                return cyclic(word)

            for face in faces:
                assert swept(face, cut, transformed) == swept(face, cut + 1, raw)
        counts.append({"extent": extent, "faces": len(faces), "cuts": extent,
                       "shared_assignment_checks": extent * len(faces)})
    return {"cases": counts, "haar_invariance": "proved separately in Lean",
            "full_interacting_response_floor": "NOT PROVED"}


if __name__ == "__main__":
    signal.alarm(30)
    print(json.dumps(pilot(), separators=(",", ":")))
