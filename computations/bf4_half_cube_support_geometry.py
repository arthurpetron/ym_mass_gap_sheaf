"""Untrusted, cutoff-independent check of the half-slab support geometry.

Lean independently checks the full production incidence lists and proves
the SU(2) support consequences for arbitrary labels and cutoffs.
"""

from computations.bf4_cutoff_two_krylov_edge_scout import lower_link_constraints
from computations.bf4_cutoff_two_vacuum_column import EXPECTED_LOWER_FACE_IDS


def main():
    constraints = lower_link_constraints()
    pins = {
        10: 12, 12: 14, 18: 17, 21: 21, 27: 22, 28: 24,
        30: 26, 36: 30, 37: 32, 45: 34, 46: 35, 48: 37,
        54: 38, 55: 40, 57: 41, 63: 42, 64: 44, 66: 46,
    }
    cube = {0, 1, 3, 9, 19, 39}
    assert set(EXPECTED_LOWER_FACE_IDS) - cube == set(pins)
    for face, index in pins.items():
        constraint = constraints[index]
        assert tuple(EXPECTED_LOWER_FACE_IDS[i]
                     for i in constraint.lower_variables) == (face,)
        assert constraint.fixed_face_ids == ()
    edges = ((0, 0, 1, 2), (1, 0, 3, 4), (5, 1, 9, 11),
             (8, 3, 19, 23), (3, 0, 39, 40))
    for index, left, right, boundary in edges:
        constraint = constraints[index]
        active = {EXPECTED_LOWER_FACE_IDS[i] for i in constraint.lower_variables}
        assert active & cube == {left, right}
        assert constraint.fixed_face_ids == (boundary,)
    print("18 exterior singleton pins: PASS; no fixed-interface contribution")
    print("5 cube parity edges: PASS; they connect all 6 cube faces")
    print("Geometry only; arbitrary-cutoff support implications are proved in Lean.")


if __name__ == "__main__":
    main()
