"""Untrusted local checks for the explicit difference-boundary construction.

The Lean proof is arbitrary-label and independently checks production geometry.
This pilot does not establish a uniform transition or spectral bound.
"""

from itertools import product

from computations.bf4_cutoff_two_krylov_edge_scout import lower_link_constraints
from computations.bf4_cutoff_two_vacuum_column import EXPECTED_LOWER_FACE_IDS
from computations.bf4_cutoff_two_cube_gram_diagonal import fixed_geometry
from computations.exact_haar_network import invariant_multiplicity


EDGES = ((0, 1, 2), (0, 3, 4), (0, 19, 20), (0, 39, 40),
         (1, 3, 5), (1, 9, 11), (1, 39, 41), (3, 9, 13),
         (3, 19, 23), (9, 19, 29), (9, 39, 49), (19, 39, 59))
CORNERS = ((2, 4, 5), (2, 40, 41), (4, 20, 23), (5, 11, 13),
           (11, 41, 49), (13, 23, 29), (20, 40, 59), (29, 49, 59))


def mate(spin):
    return 1 if spin == 0 else spin - 1


def fusion(a, b, c):
    return abs(a - b) <= c <= a + b and (a + b + c) % 2 == 0


def main():
    for a, b in product(range(17), repeat=2):
        assert fusion(a, b, abs(a - b))
        assert fusion(mate(a), mate(b), abs(a - b))
    for a, b, c in product(range(17), repeat=3):
        assert fusion(abs(a - b), abs(a - c), abs(b - c))
    cube = (0, 1, 3, 9, 19, 39)
    active = {edge[2] for edge in EDGES}
    for constraint in lower_link_constraints():
        word = tuple(sorted(
            [EXPECTED_LOWER_FACE_IDS[v] for v in constraint.lower_variables
             if EXPECTED_LOWER_FACE_IDS[v] in cube] +
            [face for face in constraint.fixed_face_ids if face in active]))
        assert word == () or word in EDGES
    fixed_ids, fixed_scopes = fixed_geometry()
    for scope in fixed_scopes:
        word = tuple(fixed_ids[i] for i in scope if fixed_ids[i] in active)
        assert word == () or word in CORNERS
    for labels in ((0, 2, 4, 6, 8, 10), (7, 1, 5, 9, 3, 11), (0, 1, 2, 3, 4, 5)):
        state = dict(zip(cube, labels))
        boundary = {face: abs(state[a] - state[b]) for a, b, face in EDGES}
        for transform in (lambda x: x, mate):
            for constraint in lower_link_constraints():
                word = tuple(transform(state[EXPECTED_LOWER_FACE_IDS[v]])
                             if EXPECTED_LOWER_FACE_IDS[v] in state else 0
                             for v in constraint.lower_variables)
                word += tuple(boundary.get(face, 0) for face in constraint.fixed_face_ids)
                assert invariant_multiplicity(word) == 1
        for scope in fixed_scopes:
            assert invariant_multiplicity(tuple(boundary.get(fixed_ids[i], 0)
                                                for i in scope)) == 1
    print("Difference and mate fusion: PASS; distance triangles: PASS (labels 0..16)")
    print("All 48 lower and 20 fixed production scopes match the catalogs")
    print("Three sample cubes: source, mate and fixed multiplicities all equal one")
    print("No uniform traffic, congestion or spectral estimate is asserted.")


if __name__ == "__main__":
    main()
