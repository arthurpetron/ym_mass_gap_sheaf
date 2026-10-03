#!/usr/bin/env python3
"""Exact bent-loop gain pilot on the full six-face cutoff-one cube.

DIAGNOSTIC ONLY: the original-carrier-to-cube-matrix Lean pin is NOT FORMALIZED.
This does not satisfy the repository's headCutoff/all-later certificate guard,
prove a completed gain sign, or establish a continuum/scaling result.

Recompute the existing full 32-state spatial matrix. Every additional Haar
contraction goes through the UNCHANGED checkpoint engine, including its
odd-incidence, degree, signed-int64 and einsum intermediate-size guards.
The executable prints JSON to stdout only; it never writes generated files.
Run with the parent's fresh capacity authorization and one-thread NumPy env.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from computations.cube_cutoff_one_checkpoint import (
    CYCLES, CYCLE_INDEX, CYCLE_LOOPS, EDGES, FACES, FACE_MASKS, FILLINGS,
    components, dot, encode, face_loops, haar_loops, matvec, spatial_matrix,
    transfer,
)

Vector = tuple[F, ...]
Matrix = tuple[Vector, ...]
Polynomial = tuple[F, ...]
PolyVector = tuple[Polynomial, ...]
PolyMatrix = tuple[PolyVector, ...]
MAX_POLYNOMIAL_DEGREE = 80


def canonical(coefficients) -> Polynomial:
    values = list(map(F, coefficients))
    while values and values[-1] == 0:
        values.pop()
    if len(values) > MAX_POLYNOMIAL_DEGREE+1:
        raise ValueError("Exact polynomial degree exceeds the pilot's fixed cap80")
    return tuple(values)


def poly_add(a: Polynomial, b: Polynomial) -> Polynomial:
    return canonical((a[i] if i < len(a) else F(0)) +
                     (b[i] if i < len(b) else F(0))
                     for i in range(max(len(a), len(b))))


def poly_scale(c: F, a: Polynomial) -> Polynomial:
    return canonical(c*x for x in a)


def poly_mul(a: Polynomial, b: Polynomial) -> Polynomial:
    if not a or not b:
        return ()
    if len(a)+len(b)-2 > MAX_POLYNOMIAL_DEGREE:
        raise ValueError("Exact product exceeds the pilot's fixed degree cap80")
    out = [F(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    out[i+j] += x*y
    return canonical(out)


def poly_sum(values) -> Polynomial:
    result = ()
    for value in values:
        result = poly_add(result, value)
    return result


def poly_shift(a: Polynomial, degree: int) -> Polynomial:
    if degree < 0:
        raise ValueError("Negative polynomial degree")
    return canonical([F(0)]*degree+list(a)) if a else ()


def poly_eval(a: Polynomial, r: F) -> F:
    result = F(0)
    for coefficient in reversed(a):
        result = result*r+coefficient
    return result


def polynomial_matrix(cycle_index: int | None = None) -> PolyMatrix:
    """Actual A(r) or M_F(r); each entry uses precisely two full face fillings."""
    if cycle_index is not None and not 0 <= cycle_index < len(CYCLES):
        raise ValueError("Observable is not in the full original cycle basis")
    inserted_mask = 0 if cycle_index is None else CYCLES[cycle_index]
    inserted_loops = () if cycle_index is None else CYCLE_LOOPS[cycle_index]
    rows = [[() for _ in CYCLES] for _ in CYCLES]
    for i, mask in enumerate(CYCLES):
        for j in range(i, len(CYCLES)):
            entry = [F(0)]*7
            for s in FILLINGS[mask ^ CYCLES[j] ^ inserted_mask]:
                degree = s.bit_count()
                entry[degree] += 2**degree*haar_loops(
                    CYCLE_LOOPS[i]+inserted_loops+CYCLE_LOOPS[j]+face_loops(s))
            rows[i][j] = rows[j][i] = canonical(entry)
    return tuple(tuple(row) for row in rows)


def poly_matvec(matrix: PolyMatrix, vector: PolyVector) -> PolyVector:
    if len(vector) != 32 or len(matrix) != 32 or any(len(row) != 32 for row in matrix):
        raise ValueError("Polynomial map requires the full 32-state carrier")
    return tuple(poly_sum(poly_mul(a, b) for a, b in zip(row, vector)) for row in matrix)


def poly_dot(a: PolyVector, b: PolyVector) -> Polynomial:
    if len(a) != 32 or len(b) != 32:
        raise ValueError("Polynomial pairing requires the full 32-state carrier")
    return poly_sum(poly_mul(x, y) for x, y in zip(a, b))


@dataclass(frozen=True)
class PolynomialGainPilot:
    spatial: PolyMatrix
    insertion: PolyMatrix
    terminal_message: PolyVector
    odd_mean_numerator: Polynomial
    odd_partition: Polynomial
    cleared_centered_message: PolyVector
    cleared_gain: Polynomial
    tail_majorant_at_one_eighth: F
    candidate_interval_floor: F


def compute_polynomial_pilot() -> PolynomialGainPilot:
    """P(r)=Z(r)^2*G(r), computed without formal division or omitted debt."""
    _, index = bent_loop()
    A = polynomial_matrix()
    M = polynomial_matrix(index)
    U = tuple(poly_shift(A[i][0], mask.bit_count()) for i, mask in enumerate(CYCLES))
    AU = poly_matvec(A, U)
    Z, numerator = AU[0], AU[index]
    observed = tuple(poly_shift(A[i][index], mask.bit_count())
                     for i, mask in enumerate(CYCLES))
    bZ = tuple(poly_add(poly_mul(Z, v), poly_scale(-1, poly_mul(numerator, u)))
               for v, u in zip(observed, U))
    AbZ, MbZ = poly_matvec(A, bZ), poly_matvec(M, bZ)
    first_cleared = poly_add(poly_mul(Z, poly_dot(U, MbZ)),
                             poly_scale(-1, poly_mul(numerator, poly_dot(U, AbZ))))
    P = poly_add(poly_dot(bZ, AbZ), poly_scale(-1, poly_shift(first_cleared, 6)))
    tail = sum((abs(coefficient)*F(1, 8)**(i-10)
                for i, coefficient in enumerate(P) if i > 10), F(0))
    leading = P[10] if len(P) > 10 else F(0)
    return PolynomialGainPilot(A, M, U, numerator, Z, bZ, P, tail, leading-tail)


def bent_loop() -> tuple[tuple[int, int], int]:
    """First adjacent face pair in the original deterministic cube ordering."""
    pair = next((i, j) for i, j in combinations(range(len(FACES)), 2)
                if FACE_MASKS[i] & FACE_MASKS[j])
    mask = FACE_MASKS[pair[0]] ^ FACE_MASKS[pair[1]]
    loops = components(mask)
    if len(loops) != 1 or len(loops[0]) != 6 or mask.bit_count() != 6:
        raise ArithmeticError("Adjacent faces did not produce one six-link loop")
    return pair, CYCLE_INDEX[mask]


def insertion_matrix(r: F, cycle_index: int) -> Matrix:
    """M[i,j]=H[V*W_i*F*W_j], retaining every original spatial factor.

    Parity selects the same two complementary face fillings as the original
    engine. No amplitude or face multiplicity replaces a Haar contraction.
    At most five fundamental factors meet an edge; odd incidence vanishes,
    so nonzero terms use the existing quadratic/quartic tensors.
    """
    if not F(0) <= r < F(1, 4):
        raise ValueError("Cutoff-one positive-weight pilot requires 0 <= r < 1/4")
    if not 0 <= cycle_index < len(CYCLES):
        raise ValueError("Observable is not in the full original cycle basis")
    rows = [[F(0) for _ in CYCLES] for _ in CYCLES]
    mask = CYCLES[cycle_index]
    for i, a in enumerate(CYCLES):
        for j in range(i, len(CYCLES)):
            parity = a ^ CYCLES[j] ^ mask
            value = sum((
                (2*r)**s.bit_count() * haar_loops(
                    CYCLE_LOOPS[i] + CYCLE_LOOPS[cycle_index] +
                    CYCLE_LOOPS[j] + face_loops(s))
                for s in FILLINGS[parity]), F(0))
            rows[i][j] = rows[j][i] = value
    return tuple(tuple(row) for row in rows)


def kinetic(r: F, vector: Vector) -> Vector:
    if len(vector) != len(CYCLES):
        raise ValueError("Kinetic multiplier requires the full 32-state basis")
    return tuple(r**mask.bit_count()*v for mask, v in zip(CYCLES, vector))


@dataclass(frozen=True)
class SignedGainPilot:
    r: F
    adjacent_faces: tuple[int, int]
    cycle_index: int
    spatial: Matrix
    insertion: Matrix
    one: Vector
    observable: Vector
    terminal_message: Vector
    observed_message: Vector
    centered_message: Vector
    odd_partition: F
    even_partition: F
    own_mean: F
    reference: F
    first_cross: F
    second_square: F
    gain: F
    uncentered_first_cross: F
    uncentered_second_square: F
    uncentered_gain: F


def compute_pilot() -> SignedGainPilot:
    """Fixed r=1/8 (w=1/2), K=1, n=0; no stored-matrix trust path."""
    r = F(1, 8)
    pair, index = bent_loop()
    A = spatial_matrix(r)
    M = insertion_matrix(r, index)
    one = tuple(F(i == 0) for i in range(len(CYCLES)))
    f = tuple(F(i == index) for i in range(len(CYCLES)))
    # g_0=1, Amsg=Tg_0. Observed=T(g_0*f), with T=D*A.
    Amsg = transfer(A, r, one)
    observed = transfer(A, r, f)
    Zodd = dot(one, matvec(A, Amsg))
    Eeven = dot(Amsg, matvec(A, Amsg))
    if Zodd <= 0 or Eeven <= 0:
        raise ArithmeticError("Original diagnostic partition is not positive")
    c = dot(f, matvec(A, Amsg)) / Zodd
    b = tuple(v-c*u for v, u in zip(observed, Amsg))
    reference = r**CYCLES[index].bit_count()
    C1 = dot(Amsg, matvec(M, b)) - c*dot(Amsg, matvec(A, b))
    C2 = dot(b, matvec(A, b))
    G = C2-reference*C1
    C1raw = dot(Amsg, matvec(M, observed))
    C2raw = dot(observed, matvec(A, observed))
    # Independent literal heat reconstruction and exact OWN-mean cancellation.
    if observed != kinetic(r, matvec(M, one)):
        raise ArithmeticError("Inserted heat message disagrees with T*f")
    if b != transfer(A, r, tuple(v-c*u for v, u in zip(f, one))):
        raise ArithmeticError("Literal T(f-c) reconstruction failed")
    if dot(f, matvec(A, Amsg))-c*Zodd != 0:
        raise ArithmeticError("Original odd OWN centering failed")
    return SignedGainPilot(
        r, pair, index, A, M, one, f, Amsg, observed, b, Zodd,
        Eeven, c, reference, C1, C2, G, C1raw, C2raw,
        C2raw-reference*C1raw,
    )


def report(pilot: SignedGainPilot) -> dict:
    """Exact rational data; no matrix pin or convergence result is inferred."""
    return {
        "scope": "Six-face SU(2) cube cutoff-one bent-loop diagnostic ONLY",
        "original_source_to_matrix_pin": "NOT FORMALIZED IN LEAN",
        "headCutoff_guard": "FAILED: K=1 < headCutoff(1/2), which is at least17",
        "completed_gain_or_uniform_scaling_claim": False,
        "arithmetic": "Fraction and unchanged signed int64 Haar contraction guards",
        "matrix_provenance": "spatial_matrix(r) recomputed; no cached A loaded",
        "w": encode(F(1, 2)), "r": encode(pilot.r),
        "kernel_cutoff": 1, "terminal_depth": 0,
        "source": "g_0=1; q=V*g_0; Amsg=T*g_0; b=T(g_0*(F-own_mean))",
        "action": "V=product over ALL SIX faces of (1+2*r*chi_face)",
        "basis_size": len(CYCLES), "cube_edge_count": len(EDGES),
        "adjacent_faces": list(pilot.adjacent_faces),
        "observable_cycle_mask": CYCLES[pilot.cycle_index],
        "observable_loop": list(CYCLE_LOOPS[pilot.cycle_index][0]),
        "reference_a": encode(pilot.reference),
        "one_factor_pointwise_floor": encode(1-4*pilot.r),
        "odd_partition": encode(pilot.odd_partition),
        "even_partition": encode(pilot.even_partition),
        "own_odd_mean": encode(pilot.own_mean),
        "C1_raw_cross": encode(pilot.first_cross),
        "C2_raw_square": encode(pilot.second_square),
        "G_raw": encode(pilot.gain),
        "G_over_same_even_partition": encode(pilot.gain/pilot.even_partition),
        "gain_sign": (pilot.gain > 0)-(pilot.gain < 0),
        "uncentered_C1": encode(pilot.uncentered_first_cross),
        "uncentered_C2": encode(pilot.uncentered_second_square),
        "uncentered_gain": encode(pilot.uncentered_gain),
        "own_center_gain_difference": encode(pilot.gain-pilot.uncentered_gain),
        "original_own_center_residual": encode(F(0)),
        "original_messages": {
            "Amsg": [encode(x) for x in pilot.terminal_message],
            "observed": [encode(x) for x in pilot.observed_message],
            "b": [encode(x) for x in pilot.centered_message],
        },
    }


def polynomial_report(pilot: PolynomialGainPilot, rational: SignedGainPilot) -> dict:
    P, r = pilot.cleared_gain, rational.r
    reconstruction = poly_eval(P, r)-rational.odd_partition**2*rational.gain
    if reconstruction != 0:
        raise ArithmeticError("Cleared polynomial disagrees with exact rational OWN gain")
    lower_vanishes = all(coefficient == 0 for coefficient in P[:10])
    leading = P[10] if len(P) > 10 else F(0)
    return {
        "scope": "Exact cleared polynomial of the SAME finite K1/n0 cube diagnostic ONLY",
        "degree_cap": MAX_POLYNOMIAL_DEGREE,
        "degree": len(P)-1,
        "cleared_gain_coefficients": [encode(c) for c in P],
        "cleared_gain_identity": "P=Zodd^2*G; bZ=Zodd*T(F)-meanNumerator*T(1)",
        "evaluation_reconstruction_residual": encode(reconstruction),
        "all_coefficients_below10_zero": lower_vanishes,
        "coefficient10": encode(leading),
        "expected_coefficient10_equals2": leading == 2,
        "absolute_tail_majorant_at_one_eighth": encode(pilot.tail_majorant_at_one_eighth),
        "candidate_interval_floor": encode(pilot.candidate_interval_floor),
        "candidate_floor_strictly_positive": pilot.candidate_interval_floor > 0,
        "interval": "0<r<=1/8",
        "interval_conclusion_available": lower_vanishes and pilot.candidate_interval_floor > 0,
        "bound": "P(r)/r^10 >= coefficient10 - sum(i>10,abs(ci)*(1/8)^(i-10))",
        "original_source_to_matrix_pin": "NOT FORMALIZED IN LEAN",
        "headCutoff_guard": "FAILED: K=1 < headCutoff(1/2), which is at least17",
        "all_cutoff_or_completed_or_scaling_claim": False,
    }


if __name__ == "__main__":
    rational = compute_pilot()
    data = report(rational)
    data["cleared_polynomial"] = polynomial_report(compute_polynomial_pilot(), rational)
    print(json.dumps(data, indent=2))
