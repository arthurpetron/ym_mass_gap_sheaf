"""The kappa-system: the sign anomaly of the SU(2) dual, as a model.

kappa(n) in Z_2 is defined exactly by  (-1)^kappa = prod_v sgn{6j}_v
on the 4-cube boundary.  This module packages the completed model:

**Support law (exhaustive at spins <= 2, moment-arbitrated).**
Over ALL 38,151 admissible spins <= 2 assignments:
  - every assignment in the 2-surface cone (n = a + b with a, b closed
    surfaces; equivalently exists a in the kernel with D(n) subset a
    subset D(n) u S(n)) is POSITIVE (8,128/8,128);
  - every negative (6,704) is NON-decomposable: its support carries
    branch curves (edges with spin pattern {2,1,1} where a doubled
    sheet splits).  kappa lives on *branched double covers* — and, at
    higher multiplicity, on >= 3-sheet loci (the j = 3/2 wall).
Minimal branched negative: Z = -1/196608, confirmed by raw moments.

**Finite-spin sign structure (item 1, exact on the occurring range).**
  sgn{6j}(t) = sigma_boundary(top of Racah family) x (-1)^{nu(t)}
  - nu = node count above t in the one-parameter Racah family
    (Sturm oscillation; verified 566/566, mean nu = 0.48 — which is
    why bare Ponzano-Regge already scores 65% at spins <= 2);
  - sigma_boundary is an EXACT quadratic form over F_2 in the label
    bits (degree-2 fit exact on all 264 stretched tuples): a quadratic
    refinement at the boundary, oscillation in the interior;
  - asymptotically nu tracks the Regge phase: kappa is the mod-2
    shadow of the gravitational action.

**Grassmann realization (item 2, minimal).**
kappa is realized by free fermions with vertex-local quadratic action:
one Grassmann pair (psi_v, psibar_v) per vertex,
    S(n) = sum_v s_v(n) psibar_v psi_v,   s_v = sgn{6j}_v,
    integral e^S  =  prod_v s_v  =  (-1)^{kappa(n)},
equivalently the Pfaffian sign of the block-diagonal antisymmetric
matrix A(n) = diag[ [0, s_v], [-s_v, 0] ].  This is the *minimal* local
realization: the certificate (tests/test_sign_anomaly.py) proves no
c-number face- or edge-local weight can do the job, while the vertex
level is the lowest cell dimension at which kappa is locally
generated.  An edge-coupled Kasteleyn-Pfaffian (non-diagonal A with
couplings on edges) remains open — the certificate does not forbid it,
because Pfaffians are not products of local weights.

**Graded RG position.**  Z(n) = (-1)^{kappa(n)} |Z(n)|; the dual RG
runs on |Z| with kappa carried by the fermions above; the negative
sector is heat-kernel suppressed (leading branched negative enters at
total Casimir weight s^{4x3+...}; see the graded census in the notes).
"""

from __future__ import annotations

from fractions import Fraction
from typing import List, Sequence, Tuple

from computations.hypercube4d_survey import hypercube
from computations.vertex_amplitude import (
    VERTS,
    sixj_sign_square,
    surface_masks,
    vertex_labels,
)

_CX, _FACES, _META = hypercube()

_EDGE_FACES = {}
for _fi, _f in enumerate(_FACES):
    for _ei, _o in _f:
        _EDGE_FACES.setdefault(_ei, []).append(_fi)


def kappa(spins: Sequence[int]) -> int:
    """kappa(n) in {0, 1}; raises ValueError on a vanishing amplitude."""
    k = 0
    for v in VERTS:
        sg, _ = sixj_sign_square(vertex_labels(v, spins))
        if sg == 0:
            raise ValueError("amplitude vanishes; kappa undefined")
        if sg < 0:
            k ^= 1
    return k


def vertex_signs(spins: Sequence[int]) -> List[int]:
    out = []
    for v in VERTS:
        sg, _ = sixj_sign_square(vertex_labels(v, spins))
        out.append(sg)
    return out


def decomposable(spins: Sequence[int]) -> bool:
    """Is n in the 2-surface cone?  (spins must be <= 2.)"""
    D = 0
    S = 0
    for i, n in enumerate(spins):
        if n == 2:
            D |= 1 << i
        elif n == 1:
            S |= 1 << i
        elif n != 0:
            raise ValueError("decomposable() is defined for spins <= 2")
    for a in surface_masks():
        if (a & D) == D and (a & ~(D | S)) == 0:
            return True
    return False


def branch_edges(spins: Sequence[int]) -> List[int]:
    """Edges with incident spin pattern {2,1,1}: the branch locus."""
    out = []
    for ei, fs in _EDGE_FACES.items():
        if sorted(spins[fi] for fi in fs) == [1, 1, 2]:
            out.append(ei)
    return out


def fermion_matrix(spins: Sequence[int]) -> List[List[int]]:
    """The 32x32 antisymmetric matrix of the minimal Grassmann action."""
    signs = vertex_signs(spins)
    N = 2 * len(VERTS)
    A = [[0] * N for _ in range(N)]
    for i, s in enumerate(signs):
        A[2 * i][2 * i + 1] = s
        A[2 * i + 1][2 * i] = -s
    return A


def pfaffian_sign(A: List[List[int]]) -> int:
    """Exact Pfaffian sign of an antisymmetric integer matrix
    (fraction-free elimination on a working copy)."""
    import copy

    M = [[Fraction(x) for x in row] for row in copy.deepcopy(A)]
    n = len(M)
    sign = 1
    for i in range(0, n, 2):
        # find pivot in row i beyond column i
        p = None
        for j in range(i + 1, n):
            if M[i][j] != 0:
                p = j
                break
        if p is None:
            return 0
        if p != i + 1:
            # swap columns/rows p <-> i+1; each swap flips Pfaffian sign
            for r in range(n):
                M[r][p], M[r][i + 1] = M[r][i + 1], M[r][p]
            M[p], M[i + 1] = M[i + 1], M[p]
            sign = -sign
        piv = M[i][i + 1]
        if piv < 0:
            pass  # handled by final product
        for r in range(i + 2, n):
            if M[i][r] != 0:
                c = M[i][r] / piv
                for s2 in range(n):
                    M[s2][r] -= c * M[s2][i + 1]
                for s2 in range(n):
                    M[r][s2] -= c * M[i + 1][s2]
    prod = Fraction(1)
    for i in range(0, n, 2):
        prod *= M[i][i + 1]
    return 1 if prod > 0 else (-1 if prod < 0 else 0)


def grassmann_sign(spins: Sequence[int]) -> int:
    """(-1)^kappa via the fermionic Pfaffian — the graded realization."""
    return pfaffian_sign(fermion_matrix(spins))
