#!/usr/bin/env python3
"""Exact SU(2) cube cutoff-one pilot; NOT a continuum or all-cutoff certificate.

All Haar contractions use signed integer tensors, divided by their exact
normalization only after contraction. The input is the six-face cubical core;
the link from its finite matrix to the repository's original transfer still
requires Lean checking. No coefficient-multiplicity measure is substituted.
"""
from __future__ import annotations

from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
from pathlib import Path
import json
import math
import numpy as np

EDGES: tuple[tuple[int, int], ...] = tuple((v, v ^ d) for v in range(8)
    for d in (1, 2, 4) if v < (v ^ d))
EDGE_INDEX = {e: i for i, e in enumerate(EDGES)}
FACES: tuple[tuple[int, ...], ...] = tuple((v, v ^ a, v ^ a ^ b, v ^ b)
    for a, b in combinations((1, 2, 4), 2)
    for v in (0, 7 ^ a ^ b))
EPS = ((0, 1), (-1, 0))
PAIRINGS = (((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2)))


def loop_mask(loop: tuple[int, ...]) -> int:
    mask = 0
    for a, b in zip(loop, loop[1:] + loop[:1]):
        mask ^= 1 << EDGE_INDEX[tuple(sorted((a, b)))]
    return mask

FACE_MASKS = tuple(loop_mask(f) for f in FACES)


def is_cycle(mask: int) -> bool:
    return all(sum(bool(mask & (1 << i)) for i, e in enumerate(EDGES) if v in e) % 2 == 0
               for v in range(8))

CYCLES = tuple(mask for mask in range(1 << len(EDGES)) if is_cycle(mask))
CYCLE_INDEX = {m: i for i, m in enumerate(CYCLES)}


def components(mask: int) -> tuple[tuple[int, ...], ...]:
    """Canonical loops of a degree-0/2 cubical even subgraph."""
    remaining = {e for i, e in enumerate(EDGES) if mask & (1 << i)}
    loops = []
    while remaining:
        start, nxt = min(remaining)
        walk = [start]
        prev, current = start, nxt
        remaining.remove((start, nxt))
        while current != start:
            walk.append(current)
            neighbors = sorted(b if a == current else a for a, b in remaining if current in (a, b))
            if len(neighbors) != 1:
                raise ValueError('Not a disjoint cycle family')
            nxt = neighbors[0]
            remaining.remove(tuple(sorted((current, nxt))))
            prev, current = current, nxt
        loops.append(tuple(walk))
    return tuple(loops)

CYCLE_LOOPS = tuple(components(m) for m in CYCLES)


def boundary(face_subset: int) -> int:
    answer = 0
    for i, mask in enumerate(FACE_MASKS):
        if face_subset & (1 << i): answer ^= mask
    return answer

FILLINGS = {m: tuple(s for s in range(64) if boundary(s) == m) for m in CYCLES}


@lru_cache(maxsize=None)
def edge_tensor(directions: tuple[bool, ...]) -> tuple[np.ndarray, int]:
    """Integral of 2 or 4 fundamental U / U^{-1} factors.

    For two factors: eps(row)*eps(column)/2.
    For four: sum over the three pairings of paired epsilons / 6.
    Reverse factors use (U^-1)[a,b] = (-1)^(a+b) U[1-b,1-a].
    """
    degree = len(directions)
    if degree not in (2, 4):
        raise ValueError(f'Unsupported even degree {degree}; never silently truncate')
    tensor = np.zeros((2,) * (2 * degree), dtype=np.int64)
    for indices in product((0, 1), repeat=2 * degree):
        rows, cols, sign = [], [], 1
        for k, forward in enumerate(directions):
            a, b = indices[2*k:2*k+2]
            if forward:
                rows.append(a); cols.append(b)
            else:
                sign *= (-1) ** (a + b)
                rows.append(1-b); cols.append(1-a)
        if degree == 2:
            value = EPS[rows[0]][rows[1]] * EPS[cols[0]][cols[1]]
        else:
            value = sum(math.prod(EPS[rows[a]][rows[b]] * EPS[cols[a]][cols[b]]
                                  for a, b in pairs) for pairs in PAIRINGS)
        tensor[indices] = sign * value
    return tensor, 2 if degree == 2 else 6


@lru_cache(maxsize=None)
def haar_loops(loops: tuple[tuple[int, ...], ...]) -> F:
    """Exact integral of a finite product of unnormalized SU(2) traces."""
    incidence: dict[int, list[tuple[int, int, bool]]] = {}
    nindices = 0
    for loop in loops:
        if len(loop) < 3 or len(set(loop)) != len(loop):
            raise ValueError('Only simple graph cycles are supported by this pilot')
        ids = tuple(range(nindices, nindices + len(loop)))
        nindices += len(loop)
        for k, (a, b) in enumerate(zip(loop, loop[1:] + loop[:1])):
            e = EDGE_INDEX[tuple(sorted((a, b)))]
            incidence.setdefault(e, []).append((ids[k], ids[(k+1) % len(loop)], a < b))
    if any(len(xs) % 2 for xs in incidence.values()): return F(0)
    if not incidence: return F(1)
    if any(len(xs) not in (2, 4) for xs in incidence.values()):
        raise ValueError('Haar degree above four: choose a larger exact moment engine')
    # An upper bound on every signed integer intermediate is 2^(indices + quartic edges).
    quartic = sum(len(xs) == 4 for xs in incidence.values())
    if nindices + quartic >= 62 or nindices >= 52:
        raise OverflowError('Exact int64/einsum index safety envelope exceeded')
    args = []
    denom = 1
    for edge in sorted(incidence):
        xs = incidence[edge]
        tensor, d = edge_tensor(tuple(x[2] for x in xs))
        args.extend([tensor, [i for x in xs for i in x[:2]]])
        denom *= d
    result = np.einsum(*args, [], optimize=('greedy', 2**20), dtype=np.int64)
    return F(int(result), denom)


def face_loops(subset: int) -> tuple[tuple[int, ...], ...]:
    return tuple(face for i, face in enumerate(FACES) if subset & (1 << i))


def spatial_matrix(r: F) -> tuple[tuple[F, ...], ...]:
    """A[a,b]=H[W_a V W_b], V=product_faces(1+2*r*chi_face).

    r=w^3; the kinetic map has multiplier r^|a| on cycle a.
    Positive-weight range: 0 <= r < 1/4. Matrix entries are signed Haar
    integrals, not face multiplicities. Input/output spatial V is retained
    in the weighted pairing A D A when the transfer D A is applied.
    """
    if not F(0) <= r < F(1, 4):
        raise ValueError('This cutoff-one positive-weight pilot requires 0 <= w^3 < 1/4')
    rows = [[F(0) for _ in CYCLES] for _ in CYCLES]
    for i, a in enumerate(CYCLES):
        for j in range(i, len(CYCLES)):
            b = CYCLES[j]
            value = sum(((2*r)**s.bit_count() * haar_loops(CYCLE_LOOPS[i] + CYCLE_LOOPS[j] + face_loops(s))
                         for s in FILLINGS[a ^ b]), F(0))
            rows[i][j] = rows[j][i] = value
    return tuple(tuple(row) for row in rows)


def dot(x, y) -> F:
    if len(x) != len(y):
        raise ValueError('dot-product dimensions differ')
    return sum((a*b for a,b in zip(x,y)), F(0))


def matvec(A, x) -> tuple[F, ...]:
    if any(len(row) != len(x) for row in A):
        raise ValueError('matrix/vector dimensions differ')
    return tuple(dot(row,x) for row in A)


def transfer(A, r: F, x) -> tuple[F, ...]:
    if len(A) != len(CYCLES) or len(x) != len(CYCLES):
        raise ValueError('cube transfer requires the full 32-state basis')
    return tuple(r**m.bit_count()*y for m,y in zip(CYCLES,matvec(A,x)))


def encode(x: F) -> list[int]:
    return [x.numerator, x.denominator]


if __name__ == '__main__':
    print('edges/faces/cycles:', len(EDGES),len(FACES),len(CYCLES))
    print('cube vacuum six-face Haar:', haar_loops(FACES))
    print('one loop norm:',haar_loops((FACES[0],FACES[0])))
    adjacent=next((i,j) for i,j in combinations(range(6),2) if FACE_MASKS[i]&FACE_MASKS[j])
    rect=components(FACE_MASKS[adjacent[0]]^FACE_MASKS[adjacent[1]])
    print('two adjacent faces / rectangle Haar:',haar_loops((FACES[adjacent[0]],FACES[adjacent[1]])+rect))


def solve_exact(A, b):
    """Deterministic rational Gaussian elimination, with explicit singular failure."""
    n = len(b)
    if len(A) != n or any(len(row) != n for row in A): raise ValueError('not square')
    rows = [list(map(F,row)) + [F(rhs)] for row,rhs in zip(A,b)]
    for j in range(n):
        pivot = next((i for i in range(j,n) if rows[i][j]), None)
        if pivot is None: raise ValueError(f'singular at column {j}')
        rows[j], rows[pivot] = rows[pivot], rows[j]
        divisor = rows[j][j]
        rows[j] = [x/divisor for x in rows[j]]
        for i in range(n):
            if i != j:
                factor = rows[i][j]
                rows[i] = [a-factor*b for a,b in zip(rows[i],rows[j])]
    return tuple(row[-1] for row in rows)


def marginal_gram(r, u, indices):
    """H[V*u*W_i*W_j] with the ORIGINAL right spatial weight retained."""
    rows = [[F(0) for _ in indices] for _ in indices]
    for ii,i in enumerate(indices):
        for jj in range(ii,len(indices)):
            j=indices[jj]
            value=F(0)
            for b,ub in enumerate(u):
                if not ub: continue
                parity=CYCLES[i]^CYCLES[j]^CYCLES[b]
                value += ub*sum(((2*r)**s.bit_count() * haar_loops(
                    CYCLE_LOOPS[i]+CYCLE_LOOPS[j]+CYCLE_LOOPS[b]+face_loops(s))
                    for s in FILLINGS[parity]),F(0))
            rows[ii][jj]=rows[jj][ii]=value
    return tuple(tuple(row) for row in rows)


def normalized_pair_escape(A,r):
    """A dual witness against closure of F/U in constant + six plaquette span.

    U=T1, F=T chi_p, nu=V*U. Project a rectangle against that span in nu,
    rather than using a bare-output-Haar detector. This retains the same
    transferred denominator and both endpoint spatial action factors.
    """
    p,q=next((i,j) for i,j in combinations(range(6),2) if FACE_MASKS[i]&FACE_MASKS[j])
    rect=CYCLE_INDEX[FACE_MASKS[p]^FACE_MASKS[q]]
    indices=(0,)+tuple(CYCLE_INDEX[m] for m in FACE_MASKS)+(rect,)
    one=tuple(F(i==0) for i in range(32))
    obs=tuple(F(i==CYCLE_INDEX[FACE_MASKS[p]]) for i in range(32))
    u=transfer(A,r,one); f=transfer(A,r,obs)
    G=marginal_gram(r,u,indices)
    coeff=solve_exact([row[:7] for row in G[:7]],[row[7] for row in G[:7]])
    dual=tuple(-c for c in coeff)+(F(1),)
    orth=matvec(G,dual)
    if any(orth[:7]): raise ArithmeticError('weighted centering failed')
    positive_norm=dot(dual,orth)
    pairing=dot(dual,tuple(matvec(A,f)[i] for i in indices))
    mass=dot(one,matvec(A,u))
    left=dot(one,matvec(A,f))
    mean=orth[0]
    determinant=mass*pairing-left*mean
    if not (positive_norm>0 and determinant!=0):
        raise ArithmeticError('No nonzero weighted escape witness')
    return {'scope':'finite six-face SU(2) cube, cutoff one, exact rational diagnostic; Lean global pin pending',
      'source_face':p,'adjacent_face':q,'test_cycle_mask':CYCLES[rect],
      'basis_indices':list(indices),'marginal_gram':[[encode(x) for x in row] for row in G],
      'dual_coefficients':[encode(x) for x in dual],
      'weighted_pairings_with_constant_and_plaquettes':[encode(x) for x in orth[:7]],
      'dual_squared_norm':encode(positive_norm),'original_partition':encode(mass),
      'full_weight_pairing_with_transferred_source':encode(pairing),
      'connected_determinant':encode(determinant)}
