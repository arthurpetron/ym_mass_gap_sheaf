"""Untrusted local pilot for the exact cube boundary-mask reduction.

Checks full production incidence words, not a replacement gauge model.
Lean independently proves the arbitrary-cutoff identities.
"""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import prod
from random import Random

from computations.bf4_cube_difference_boundary import EDGES, CORNERS, fusion, mate
from computations.bf4_cutoff_two_krylov_edge_scout import lower_link_constraints
from computations.bf4_cutoff_two_vacuum_column import EXPECTED_LOWER_FACE_IDS, coeff_w
from computations.bf4_cutoff_two_cube_gram_diagonal import fixed_geometry
from computations.exact_haar_network import invariant_multiplicity


CUBE = (0, 1, 3, 9, 19, 39)
INACTIVE = (14, 22, 31, 32, 38, 47, 50, 56, 58, 65, 67, 68)


def overlap(left, right, cutoff):
    domains = [tuple(s for s in range(cutoff + 1)
                     if fusion(left[a], left[b], s) and fusion(right[a], right[b], s))
               for a, b, _ in EDGES]
    total = Fraction(0)
    for spins in product(*domains):
        boundary = dict(zip((e[2] for e in EDGES), spins))
        if all(fusion(*(boundary[f] for f in corner)) for corner in CORNERS):
            total += prod(coeff_w(Fraction(1, 2), s) for s in spins)
    return total


def main():
    lower = lower_link_constraints()
    fixed_ids, fixed_scopes = fixed_geometry()
    profile = [tuple(sorted(
        [EXPECTED_LOWER_FACE_IDS[v] for v in row.lower_variables
         if EXPECTED_LOWER_FACE_IDS[v] in CUBE] + list(row.fixed_face_ids))) for row in lower]
    assert Counter(profile) == Counter(EDGES + tuple((i,) for i in INACTIVE) + ((),) * 24)
    active = {edge[2] for edge in EDGES}
    profile_fixed = [tuple(fixed_ids[i] for i in scope if fixed_ids[i] in active)
                     for scope in fixed_scopes]
    assert Counter(profile_fixed) == Counter(CORNERS + ((),) * 12)
    rng = Random(11)
    samples = 0
    for _ in range(100):
        source = {face: rng.randrange(6) for face in CUBE}
        difference = {f: abs(source[a] - source[b]) for a, b, f in EDGES}
        boundaries = [difference,
                      {**difference, INACTIVE[rng.randrange(12)]: 1},
                      {f: rng.randrange(6) for f in active},
                      {f: rng.randrange(6) for f in fixed_ids}]
        for boundary in boundaries:
            zero_ok = all(boundary.get(f, 0) == 0 for f in INACTIVE)
            for state in (source, {f: mate(s) for f, s in source.items()}):
                actual = prod(invariant_multiplicity(
                    tuple(state.get(EXPECTED_LOWER_FACE_IDS[v], 0) for v in row.lower_variables)
                    + tuple(boundary.get(f, 0) for f in row.fixed_face_ids)) for row in lower)
                mask = zero_ok and all(fusion(state[a], state[b], boundary.get(f, 0))
                                       for a, b, f in EDGES)
                assert actual == int(mask)
                if mask:
                    assert all(boundary.get(f, 0) <= 2 * max(state.values()) for f in fixed_ids)
                samples += 1
            if zero_ok:
                actual_fixed = prod(invariant_multiplicity(
                    tuple(boundary.get(fixed_ids[i], 0) for i in scope)) for scope in fixed_scopes)
                mask_fixed = all(fusion(*(boundary.get(f, 0) for f in corner)) for corner in CORNERS)
                assert actual_fixed == int(mask_fixed)
    print("Production word profiles: 12 triples + 12 pins + 24 empty; 8 corners + 12 empty: PASS")
    print(f"Arbitrary-boundary Boolean masks: {samples} source/mate checks: PASS")
    for labels in ((1,) * 6, (0, 2, 0, 2, 0, 2), (2,) * 6):
        left = dict(zip(CUBE, labels))
        right = left if labels == (1,) * 6 else {f: mate(s) for f, s in left.items()}
        threshold = 2 * max(left.values())
        baseline = overlap(left, right, threshold)
        assert all(overlap(left, right, cutoff) == baseline
                   for cutoff in (threshold + 1, threshold + 2))
    ones = dict.fromkeys(CUBE, 1)
    assert overlap(ones, ones, 1) < overlap(ones, ones, 2)
    print("Exact rational overlap saturation: three pairs PASS; below-threshold change detected")
    print("No uniform norm, spectral or continuum estimate is asserted.")


if __name__ == "__main__":
    main()
