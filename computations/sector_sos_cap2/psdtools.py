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

"""Exact rational PSD tests: LDL^T with zero-pivot handling, and the
independent elementary-symmetric (characteristic polynomial) test."""

from fractions import Fraction as F
from typing import List, Tuple

Mat = List[List[F]]


def is_symmetric(A: Mat) -> bool:
    n = len(A)
    return all(len(r) == n for r in A) and all(
        A[i][j] == A[j][i] for i in range(n) for j in range(i + 1, n))


def ldl_psd(A: Mat) -> Tuple[bool, str]:
    """Exact square-root-free LDL^T / Schur-complement PSD test.

    A symmetric matrix is PSD iff this loop never hits a negative pivot
    and every zero pivot has an identically zero remaining row (else the
    2x2 principal minor (k,j) equals -A[k][j]^2 < 0).
    """
    n = len(A)
    M = [list(r) for r in A]
    pivots = []
    for k in range(n):
        p = M[k][k]
        if p < 0:
            return False, f'negative pivot {p} at index {k}'
        if p == 0:
            for j in range(k + 1, n):
                if M[k][j] != 0:
                    return False, (f'zero pivot at {k} with nonzero '
                                   f'off-diagonal M[{k}][{j}]={M[k][j]}')
            pivots.append(F(0))
            continue
        pivots.append(p)
        for i in range(k + 1, n):
            f = M[i][k] / p
            if f == 0:
                continue
            for j in range(k + 1, n):
                M[i][j] -= f * M[k][j]
    return True, 'pivots ' + ','.join(str(x) for x in pivots)


def elementary_symmetric(A: Mat) -> List[F]:
    """e_1..e_n of the eigenvalues, via Faddeev-LeVerrier (exact)."""
    n = len(A)
    c = []
    M = [list(r) for r in A]
    for k in range(1, n + 1):
        if k > 1:
            # M <- A (M - c_{k-1} I)
            Mm = [[M[i][j] - (c[k - 2] if i == j else F(0))
                   for j in range(n)] for i in range(n)]
            M = [[sum(A[i][t] * Mm[t][j] for t in range(n))
                  for j in range(n)] for i in range(n)]
        ck = sum(M[i][i] for i in range(n)) / k
        c.append(ck)
    return [((-1) ** (k + 1)) * c[k - 1] for k in range(1, n + 1)]


def esym_psd(A: Mat) -> Tuple[bool, str]:
    e = elementary_symmetric(A)
    bad = [(k + 1, e[k]) for k in range(len(e)) if e[k] < 0]
    if bad:
        return False, f'negative e_k: {bad[:3]}'
    return True, 'all e_k >= 0'


def _selftest():
    ok = True
    tests = [
        ([[F(2), F(1)], [F(1), F(2)]], True),
        ([[F(1), F(2)], [F(2), F(1)]], False),
        ([[F(0), F(1)], [F(1), F(0)]], False),
        ([[F(0), F(0)], [F(0), F(3)]], True),
        ([[F(1), F(1)], [F(1), F(1)]], True),
        ([[F(1), F(0), F(0)], [F(0), F(0), F(1)], [F(0), F(1), F(0)]], False),
        ([[F(4), F(2), F(0)], [F(2), F(1), F(0)], [F(0), F(0), F(0)]], True),
        ([[F(-1)]], False),
    ]
    for A, want in tests:
        a = ldl_psd(A)[0]
        b = esym_psd(A)[0]
        if a != want or b != want:
            ok = False
            print('PSD selftest FAIL', A, want, a, b)
    print('psdtools selftest', 'OK' if ok else 'FAILED')
    return ok


if __name__ == '__main__':
    _selftest()
