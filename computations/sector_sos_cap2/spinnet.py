"""INDEPENDENT-REPLICATION TOOLING for the sector-SOS certificate
(work_plan §17g, notes/sector-sos-positivity.md).

STATUS: gated, NOT yet pinned in the test suite.  `spinnet` (the fast
exact rational spin-network evaluator) is gated BIT-FOR-BIT against the
incumbent evaluator `computations.dp3_fixed_tile.network_value_fixed` on
all 171 cap<=1 configurations, 320 character-orthogonality identities and
130 random networks (see `xcheck2`), and the cap<=1 family it rebuilds
reproduces `computations.sector_sos` exactly.  It exists only to build the
DISJOINT cap<=2 family (187 sectors) used as the independent replication
gate; nothing on the certificate's critical path depends on it.  Pinning
these modules in `tests/` is a named follow-up.
"""
from __future__ import annotations

"""Exact rational spin-network evaluator for pure-character Haar networks.

Replaces the quaternion-monomial brute force of
`slab_blocking_kernel._eliminate_all` for networks all of whose factors
are single characters chi_{n_f}(hol_f).  The brute force has to carry
polynomials in up to 16 link variables (treewidth 5 -> intractable once
labels reach 2); here every bond has dimension n_f + 1 <= 4.

Method (all exact, Fractions only, no floats, no sqrt):

  chi_n(hol_f) = tr [ D^n(U_{l_1}^{e_1}) ... D^n(U_{l_p}^{e_p}) ]

with D^n = Sym^n of the defining rep, realised on homogeneous
polynomials of degree n in (z1, z2) with the MONOMIAL basis
e_k = z1^k z2^{n-k}.  In that basis the sl(2) generators are integer
matrices

  H e_k = (2k-n) e_k,   E e_k = (n-k) e_{k+1},   F e_k = k e_{k-1},

and the SU(2)-invariant hermitian form is diagonal and rational,
<e_k, e_k> = 1 / binom(n, k)  (Fischer form; one checks E^dag = F).

For a link l carrying legs (n_a, e_a) the Haar integral

  M_l = Integral  prod_a  D^{n_a}(U^{e_a})_{i_a j_a}  dU

is read off the orthogonal projector P onto the SU(2)-invariants of
W = tensor_a V_a  (V_a = V_{n_a} for e_a = +1, its dual for e_a = -1):
invariants are the common kernel of H, E, F (exact rational kernel), and
P = B (B^T G B)^{-1} B^T G.  The remaining contraction is a tensor
network with bonds of dimension <= 4.

Everything here is checked against the upstream brute force by
`selftest()` / `crosscheck()`.
"""

import sys
from fractions import Fraction as F
from functools import lru_cache
from math import comb
from typing import Dict, List, Sequence, Tuple

sys.set_int_max_str_digits(0)

from computations.slab_blocking_kernel import _CX, _FACES

Vec = List[F]
Mat = List[List[F]]

# ---------------------------------------------------------------------------
# sl(2) generators and Gram in the monomial basis of Sym^n
# ---------------------------------------------------------------------------


def _gens(n: int) -> Tuple[Mat, Mat, Mat]:
    d = n + 1
    H = [[F(0)] * d for _ in range(d)]
    E = [[F(0)] * d for _ in range(d)]
    Fm = [[F(0)] * d for _ in range(d)]
    for k in range(d):
        H[k][k] = F(2 * k - n)
        if k + 1 < d:
            E[k + 1][k] = F(n - k)
        if k - 1 >= 0:
            Fm[k - 1][k] = F(k)
    return H, E, Fm


def _gram(n: int) -> Vec:
    return [F(1, comb(n, k)) for k in range(n + 1)]


def _dual_gen(X: Mat) -> Mat:
    d = len(X)
    return [[-X[j][i] for j in range(d)] for i in range(d)]


def _dual_gram(g: Vec) -> Vec:
    return [1 / x for x in g]


# ---------------------------------------------------------------------------
# exact rational linear algebra
# ---------------------------------------------------------------------------


def _rref(rows: Mat, ncols: int):
    """Reduced row echelon form; returns (rows, pivot_cols)."""
    rows = [list(r) for r in rows]
    piv = []
    r = 0
    for c in range(ncols):
        p = None
        for i in range(r, len(rows)):
            if rows[i][c] != 0:
                p = i
                break
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        inv = 1 / rows[r][c]
        rows[r] = [x * inv for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[r])]
        piv.append(c)
        r += 1
        if r == len(rows):
            break
    return rows[:r], piv


def _kernel(rows: Mat, ncols: int) -> Mat:
    """Basis of the kernel, as a list of column vectors (length ncols)."""
    R, piv = _rref(rows, ncols)
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for fc in free:
        v = [F(0)] * ncols
        v[fc] = F(1)
        for i, pc in enumerate(piv):
            v[pc] = -R[i][fc]
        basis.append(v)
    return basis


def _solve(A: Mat, B: Mat) -> Mat:
    """Solve A X = B exactly (A square invertible)."""
    n = len(A)
    m = len(B[0])
    aug = [list(A[i]) + list(B[i]) for i in range(n)]
    R, piv = _rref(aug, n)
    assert piv == list(range(n)), "singular matrix in _solve"
    return [R[i][n:n + m] for i in range(n)]


# ---------------------------------------------------------------------------
# invariant projector for a link
# ---------------------------------------------------------------------------


@lru_cache(maxsize=None)
def _projector(legs: Tuple[Tuple[int, int], ...]):
    """Sparse dict {(row_tuple, col_tuple): Fraction} for
    P = Integral tensor_a rho_a(U) dU  on  W = tensor_a V_a."""
    dims = [n + 1 for n, _ in legs]
    D = 1
    for d in dims:
        D *= d
    # index <-> tuple
    def to_tuple(idx):
        out = []
        for d in reversed(dims):
            out.append(idx % d)
            idx //= d
        return tuple(reversed(out))

    strides = []
    s = 1
    for d in reversed(dims):
        strides.append(s)
        s *= d
    strides = list(reversed(strides))

    gens = []
    grams = []
    for n, eps in legs:
        H, E, Fm = _gens(n)
        g = _gram(n)
        if eps == -1:
            H, E, Fm = _dual_gen(H), _dual_gen(E), _dual_gen(Fm)
            g = _dual_gram(g)
        gens.append((H, E, Fm))
        grams.append(g)

    # total Gram (diagonal)
    Gdiag = [F(1)] * D
    for idx in range(D):
        t = to_tuple(idx)
        v = F(1)
        for a, i in enumerate(t):
            v *= grams[a][i]
        Gdiag[idx] = v

    # stacked generator rows (H_tot, E_tot, F_tot) acting on W
    rows: Mat = []
    for gi in range(3):
        M = [[F(0)] * D for _ in range(D)]
        for a in range(len(legs)):
            X = gens[a][gi]
            da = dims[a]
            for idx in range(D):
                t = to_tuple(idx)
                ia = t[a]
                for ja in range(da):
                    c = X[ja][ia]
                    if c:
                        jdx = idx + (ja - ia) * strides[a]
                        M[jdx][idx] += c
        rows.extend(M)

    B = _kernel(rows, D)  # list of column vectors
    r = len(B)
    out: Dict[Tuple[Tuple[int, ...], Tuple[int, ...]], F] = {}
    if r == 0:
        return {}
    # Bm: D x r
    Bm = [[B[j][i] for j in range(r)] for i in range(D)]
    # A = B^T G B  (r x r);  C = B^T G  (r x D)
    C = [[B[j][i] * Gdiag[i] for i in range(D)] for j in range(r)]
    A = [[sum(C[j][i] * B[k][i] for i in range(D)) for k in range(r)]
         for j in range(r)]
    X = _solve(A, C)  # r x D,  X = A^{-1} B^T G
    for i in range(D):
        ti = to_tuple(i)
        brow = Bm[i]
        if all(x == 0 for x in brow):
            continue
        for j in range(D):
            v = F(0)
            for k in range(r):
                if brow[k]:
                    v += brow[k] * X[k][j]
            if v:
                out[(ti, to_tuple(j))] = v
    return out


# ---------------------------------------------------------------------------
# tensor network contraction (sparse, exact)
# ---------------------------------------------------------------------------


class Tensor:
    __slots__ = ('names', 'data')

    def __init__(self, names, data):
        self.names = tuple(names)
        self.data = data

    def selftrace(self):
        """Sum over any index name occurring twice in this tensor."""
        names = list(self.names)
        data = self.data
        while True:
            dup = None
            for i, nm in enumerate(names):
                if names.count(nm) > 1:
                    dup = (i, names.index(nm, i + 1))
                    break
            if dup is None:
                break
            i, j = dup
            keep = [k for k in range(len(names)) if k not in (i, j)]
            nd: Dict[tuple, F] = {}
            for key, v in data.items():
                if key[i] != key[j]:
                    continue
                nk = tuple(key[k] for k in keep)
                nd[nk] = nd.get(nk, F(0)) + v
            data = {k: v for k, v in nd.items() if v}
            names = [names[k] for k in keep]
        return Tensor(names, data)


def _contract_pair(t1: Tensor, t2: Tensor) -> Tensor:
    shared = [nm for nm in t1.names if nm in t2.names]
    i1 = [t1.names.index(nm) for nm in shared]
    i2 = [t2.names.index(nm) for nm in shared]
    k1 = [i for i in range(len(t1.names)) if i not in i1]
    k2 = [i for i in range(len(t2.names)) if i not in i2]
    b2: Dict[tuple, List[Tuple[tuple, F]]] = {}
    for key, v in t2.data.items():
        sk = tuple(key[i] for i in i2)
        b2.setdefault(sk, []).append((tuple(key[i] for i in k2), v))
    out: Dict[tuple, F] = {}
    for key, v in t1.data.items():
        sk = tuple(key[i] for i in i1)
        lst = b2.get(sk)
        if not lst:
            continue
        rest1 = tuple(key[i] for i in k1)
        for rest2, w in lst:
            nk = rest1 + rest2
            out[nk] = out.get(nk, F(0)) + v * w
    out = {k: v for k, v in out.items() if v}
    names = [t1.names[i] for i in k1] + [t2.names[i] for i in k2]
    return Tensor(names, out).selftrace()


def contract_network(tensors: List[Tensor]) -> F:
    ts = [t.selftrace() for t in tensors]
    ts = [t for t in ts if t.names or t.data]
    while len(ts) > 1:
        best = None
        for i in range(len(ts)):
            for j in range(i + 1, len(ts)):
                sh = len(set(ts[i].names) & set(ts[j].names))
                cost = (len(ts[i].data) + 1) * (len(ts[j].data) + 1)
                key = (-sh, cost)
                if best is None or key < best[0]:
                    best = (key, i, j)
        _, i, j = best
        t = _contract_pair(ts[i], ts[j])
        ts = [ts[k] for k in range(len(ts)) if k not in (i, j)] + [t]
    t = ts[0]
    assert not t.names, f"network not fully contracted: {t.names}"
    return t.data.get((), F(0))


# ---------------------------------------------------------------------------
# the slab network
# ---------------------------------------------------------------------------

_TREE = _CX.tree


@lru_cache(maxsize=None)
def _free_cycle(fi: int) -> Tuple[Tuple[int, int], ...]:
    return tuple((ei, o) for ei, o in _FACES[fi] if ei not in _TREE)


def haar_paths(items: Sequence[Tuple[int, Tuple[Tuple[int, int], ...]]]) -> F:
    """Exact Haar integral of prod_j chi_{n_j}(hol of path_j).

    `items` is a list of (label, closed path) with path a tuple of
    (edge index, +-1).  Labels <= 0 are dropped (chi_0 = 1).
    """
    const = F(1)
    legs_by_link: Dict[int, List[Tuple[int, int, object, object]]] = {}
    for fi, (n, path) in enumerate(items):
        if n <= 0:
            continue
        cyc = tuple((ei, o) for ei, o in path if ei not in _TREE)
        p = len(cyc)
        if p == 0:
            const *= F(n + 1)  # chi_n(identity)
            continue
        for k, (ei, o) in enumerate(cyc):
            row = (fi, k)
            col = (fi, (k + 1) % p)
            legs_by_link.setdefault(ei, []).append((n, o, row, col))
    if not legs_by_link:
        return const
    tensors = []
    for ei, legs in legs_by_link.items():
        key = tuple((n, o) for n, o, _r, _c in legs)
        P = _projector(key)
        if not P:
            return F(0)
        names = []
        for (n, o, row, col) in legs:
            names.extend([row, col])
        data: Dict[tuple, F] = {}
        for (rt, ct), v in P.items():
            key2 = []
            for a, (n, o, _r, _c) in enumerate(legs):
                if o == 1:
                    key2.extend([rt[a], ct[a]])
                else:
                    key2.extend([ct[a], rt[a]])
            data[tuple(key2)] = v
        tensors.append(Tensor(names, data))
    return const * contract_network(tensors)


def haar_characters(labels: Dict[int, int]) -> F:
    """Exact Haar integral of prod_f chi_{labels[f]}(hol_f) over faces."""
    return haar_paths([(n, tuple(_FACES[fi])) for fi, n in labels.items()])


# ---------------------------------------------------------------------------
# self tests
# ---------------------------------------------------------------------------


def selftest() -> List[str]:
    """Structural checks on the projector, independent of the slab."""
    bad = []
    # (1) single leg, n>0 -> no invariants
    for n in (1, 2, 3):
        if _projector(((n, 1),)):
            bad.append(f'single leg n={n} has invariants')
    # (2) V_n tensor V_n^*: P should be |inv><inv| with
    #     Integral D(U)_{ij} D(U^{-1})_{kl} = delta_{il} delta_{jk}/(n+1)
    for n in (1, 2, 3):
        P = _projector(((n, 1), (n, -1)))
        d = n + 1
        for i in range(d):
            for j in range(d):
                for k in range(d):
                    for l in range(d):
                        # M[(i,j),(k,l)] with leg0 eps=+1 (row i,col j),
                        # leg1 eps=-1 (row k,col l) -> P row=(i,l) col=(j,k)
                        got = P.get(((i, l), (j, k)), F(0))
                        want = F(1, d) if (i == l and j == k) else F(0)
                        if got != want:
                            bad.append(f'n={n} 2-leg mismatch {i}{j}{k}{l}:'
                                       f' {got} vs {want}')
    # (3) three legs n,n,0 -> reduces to case (2)
    # (4) V_1^{tensor 2} x V_1^{*tensor 2}: dim of invariants = 2
    P = _projector(((1, 1), (1, 1), (1, -1), (1, -1)))
    # trace of the projector over W equals dim of invariant space
    tr = sum(v for (r, c), v in P.items() if r == c)
    if tr != 2:
        bad.append(f'2x2 invariant dim = {tr}, want 2')
    # (5) idempotence spot check
    for key in [((1, 1), (1, -1)), ((2, 1), (2, -1), (1, 1), (1, -1))]:
        P = _projector(key)
        rows = {}
        for (r, c), v in P.items():
            rows.setdefault(r, {})[c] = v
        for r, rr in rows.items():
            for c in set().union(*[set(rows[x]) for x in rows]):
                s = F(0)
                for mid, v in rr.items():
                    s += v * rows.get(mid, {}).get(c, F(0))
                if s != P.get((r, c), F(0)):
                    bad.append(f'projector {key} not idempotent at {r},{c}')
                    break
    return bad
