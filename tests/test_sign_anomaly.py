"""The sign-anomaly certificate: the dual sign is a genuine class.

Twenty spin configurations on the 4-cube boundary whose amplitude-sign
product is -1 while every face-local datum (face, spin) and every
edge-local datum (edge, ordered incident-spin triple) occurs an even
number of times.  Consequence: no face- or edge-local sign twist (no
generalized Kasteleyn orientation) can make the SU(2) dual sign-free.
The sign is vertex-locally generated (Z = prod {6j}_v) but not
gaugeable by codimension >= 1 data: an anomaly in the strict sense.
"""

import json
import os
from collections import Counter

from computations.hypercube4d_survey import hypercube
from computations.vertex_amplitude import (
    VERTS,
    combo_spins,
    sixj_sign_square,
    vertex_labels,
)

CERT_PATH = os.path.join(os.path.dirname(__file__), "..", "computations",
                         "anomaly_certificate.json")


def _sign_of(spins):
    s = 1
    for v in VERTS:
        sg, _ = sixj_sign_square(vertex_labels(v, spins))
        if sg == 0:
            return 0
        s *= sg
    return s


def test_anomaly_certificate():
    cert = json.load(open(CERT_PATH))
    assert len(cert) == 20
    cx, faces, _meta = hypercube()
    edge_faces = {}
    for fi, f in enumerate(faces):
        for ei, _o in f:
            edge_faces.setdefault(ei, []).append(fi)
    for ei in edge_faces:
        edge_faces[ei] = sorted(edge_faces[ei])

    sign_product = 1
    cnt = Counter()
    for combo in cert:
        spins = combo_spins(combo)
        sg = _sign_of(spins)
        assert sg != 0
        sign_product *= sg
        for fi, n in enumerate(spins):
            if n:
                cnt[("f", fi, n)] += 1
        for ei, fs in edge_faces.items():
            tri = tuple(spins[fi] for fi in fs)
            if any(tri):
                cnt[("e", ei, tri)] += 1
    assert sign_product == -1
    assert all(v % 2 == 0 for v in cnt.values())
