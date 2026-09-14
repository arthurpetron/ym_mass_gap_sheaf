"""Exact local fundamental tube, with all upper boundary variables retained.

Run with --certificate to print the small temporal-gauge-reduced stages.
The five input characters are literal corrected-slab faces 0,2,4,20,40;
face 6 is the opposite plaquette. This is one selected heat-expansion term,
not a positive lower bound for the full interacting connected covariance.
"""

from fractions import Fraction
import json
import signal
import sys

from computations.corrected_slab_haar_network import corrected_slab_haar_complex
from computations.exact_haar_network import (
    chi, holonomy, p_links, p_mul, P_ONE, integrate_link_linear_factors,
    p_scale_s, link_linear_coefficients, integrate_link,
)


def tube_certificate() -> dict:
    _, faces, _ = corrected_slab_haar_complex(1)
    ids = [0, 2, 4, 20, 40]
    factors = [chi(1, holonomy(faces[i])) for i in ids]
    boundary = [link for link, _ in faces[6]]
    interior = set().union(*(p_links(p) for p in factors)) - set(boundary)
    assert len(interior) == 8 and len(set(boundary)) == 4
    stages = [factors]
    order = []
    while interior:
        choices = []
        for link in sorted(interior):
            incident = [i for i, p in enumerate(factors) if link in p_links(p)]
            cost = 1
            for i in incident:
                cost *= max(1, len(factors[i]))
            linear = True
            for i in incident:
                try:
                    link_linear_coefficients(factors[i], link)
                except ValueError:
                    linear = False
                    break
            choices.append((not linear, cost, link, incident))
        generic, _, link, incident = min(choices)
        selected = set(incident)
        if generic:
            merged = dict(P_ONE)
            for i in incident:
                merged = p_mul(merged, factors[i])
            contracted = integrate_link(merged, link)
        else:
            contracted = integrate_link_linear_factors([factors[i] for i in incident], link)
        factors = [contracted] + [p for i, p in enumerate(factors) if i not in selected]
        assert max(map(len, factors)) <= 16384
        order.append(link)
        interior.remove(link)
        stages.append(factors)
    result = dict(P_ONE)
    for p in factors:
        result = p_mul(result, p)
    expected = p_scale_s(chi(1, holonomy(faces[6])), 0, Fraction(1, 16))
    assert result == expected
    # The original fundamental heat coefficient is 2*w^3 at each side.
    assert Fraction(2)**4 * Fraction(1, 16) == 1
    all_links = order + boundary
    # Lean's boundaryCompleteSlabLinks uses first occurrence in edgesOf,
    # whose order is A,D,C,B, not this pilot's sorted raw-link enumeration.
    lean_order = list(dict.fromkeys(
        face[i][0] for face in faces for i in [0, 3, 2, 1]
    ))
    lean_words = [[lean_order.index(link) for link, _ in faces[i]]
                  for i in [0, 2, 4, 6, 20, 40]]
    assert lean_words == [[0, 3, 2, 1], [0, 9, 8, 7], [1, 13, 12, 7],
                          [8, 17, 16, 12], [2, 43, 16, 13], [3, 43, 17, 9]]

    return {
        "source_face_ids": ids,
        "target_face_id": 6,
        "raw_link_order": all_links,
        "lean_face_words_0_2_4_6_20_40": lean_words,
        "words": [[[all_links.index(link), sign] for link, sign in faces[i]] for i in ids + [6]],
        "stage_sizes": [[len(p) for p in fs] for fs in stages],
        "bare_coefficient": "1/16",
        "weighted_coefficient": "w^12",
        "physical_covariance_floor": "NOT PROVED",
    }


def reduced_tube_certificate(include_stages: bool = False) -> dict:
    """Four conditional contractions, before integrating ANY top coordinate.

    This computes the reduced kernels, not the gauge-change theorem; that
    theorem belongs to Lean's BF4ExactSlabTemporalGaugeFaces module.
    """
    orientations = [1, 1, -1, -1]
    lower = [(i, sign) for i, sign in enumerate(orientations)]
    current = chi(1, holonomy(lower))
    stages = [current]
    for i in range(4):
        kernel = chi(1, holonomy([(i, 1), (i + 4, -1)]))
        current = integrate_link_linear_factors([current, kernel], i)
        word = [(j + 4 if j <= i else j, sign) for j, sign in lower]
        expected = p_scale_s(chi(1, holonomy(word)), 0, Fraction(1, 2 ** (i + 1)))
        assert current == expected
        assert len(current) == 64
        stages.append(current)
    result = {
        "lower_word": lower,
        "upper_word": [(i + 4, sign) for i, sign in lower],
        "stage_sizes": [len(p) for p in stages],
        "stage_coefficients": [str(Fraction(1, 2 ** i)) for i in range(5)],
        "bare_coefficient": "1/16",
        "weighted_coefficient": "w^12",
        "physical_covariance_floor": "NOT PROVED",
    }
    if include_stages:
        result["stages"] = [
            sorted([[list(m), str(c[0])] for m, c in p.items()]) for p in stages
        ]
    return result


if __name__ == "__main__":
    signal.alarm(30)
    print(json.dumps({
        "original_tube": tube_certificate(),
        "reduced_tube": reduced_tube_certificate("--certificate" in sys.argv),
    }, separators=(",", ":")))
