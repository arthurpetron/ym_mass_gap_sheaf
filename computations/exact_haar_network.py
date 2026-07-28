"""Exact SU(2) Haar network integrator over quaternion link coordinates.

This module is the executable mirror of the Lean constructive Haar spine
(`lean/YMGap/**` quaternion-block calculus: ``finiteProductHaar``, the
four-/six-valent projector files, the cutoff-one Haar factorization).  It
computes *exact* Haar integrals of polynomial class-function networks on
SU(2) links, with all arithmetic in ``fractions.Fraction`` and the
heat-kernel coupling carried symbolically.  No floating point anywhere.

Design (matching the Lean side's choices)
-----------------------------------------

- A link variable is a unit quaternion ``q = (w, x, y, z)`` with
  ``w^2 + x^2 + y^2 + z^2 = 1``; Haar measure on SU(2) is the uniform
  measure on S^3.  Monomial moments are exactly rational:

      E[w^{2a} x^{2b} y^{2c} z^{2d}]
        = (2a-1)!! (2b-1)!! (2c-1)!! (2d-1)!! / (2^A (A+1)!),
      A = a + b + c + d,

  and vanish if any exponent is odd.  (Derivation: Gaussian quotient
  E_gauss[mono] / E_gauss[r^{2A}] with r^2 ~ chi^2_4.)

- Characters: ``chi_n(U) = S_n(tr U)`` (Chebyshev-like recursion), where
  ``n = 2j`` is the *integer* spin label.  ``chi_0 = 1``, ``chi_1 = 2w``,
  ``chi_{n+1} = 2w * chi_n - chi_{n-1}``.  ``d_n = n + 1``,
  ``4 C_2 = n(n+2)``.

- Heat-kernel plaquette activity truncated at ``n <= nmax``:

      A_s(U) = sum_n d_n * s^{n(n+2)} * chi_n(U),   s = e^{-t/4},

  so every network value is a polynomial in ``s`` with exact rational
  coefficients.  Truncation is *exact* for any network whose spins are
  forced <= nmax by fusion parity (and an explicit tail-bound duty
  otherwise; see notes/dual-positivity-survival.md).

- A network is a list of polynomial factors (characters of loop
  holonomies, activities); contraction integrates links one at a time
  with a greedy elimination order.

The point of existence of this module: pointwise positivity of blocked
weights is trivial (integrals of positive integrands), but the *dual*
(character-expansion) coefficients are not.  This integrator decides
their signs exactly.
"""

from __future__ import annotations

from fractions import Fraction
from functools import lru_cache
from itertools import product as iproduct
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

# ---------------------------------------------------------------------------
# Coefficients: exact polynomials in the symbolic coupling s (power -> Fraction)
# ---------------------------------------------------------------------------

SPoly = Dict[int, Fraction]  # {power of s: coefficient}

S_ONE: SPoly = {0: Fraction(1)}


def sp_scale(p: SPoly, c: Fraction) -> SPoly:
    if c == 0:
        return {}
    return {k: v * c for k, v in p.items()}


def sp_add_into(acc: SPoly, p: SPoly, c: Fraction = Fraction(1)) -> None:
    if c == 0:
        return
    for k, v in p.items():
        nv = acc.get(k, Fraction(0)) + v * c
        if nv:
            acc[k] = nv
        else:
            acc.pop(k, None)


def sp_mul(a: SPoly, b: SPoly) -> SPoly:
    out: SPoly = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            k = ka + kb
            nv = out.get(k, Fraction(0)) + va * vb
            if nv:
                out[k] = nv
            else:
                out.pop(k, None)
    return out


def sp_shift(p: SPoly, power: int) -> SPoly:
    return {k + power: v for k, v in p.items()}


# ---------------------------------------------------------------------------
# Polynomials in link coordinates.
# Variable id: 4 * link + component  (component 0..3 = w,x,y,z).
# Monomial: sorted tuple of (var_id, exponent).  Poly: {monomial: SPoly}.
# ---------------------------------------------------------------------------

Mono = Tuple[Tuple[int, int], ...]
Poly = Dict[Mono, SPoly]

P_ZERO: Poly = {}


def p_const(sp: SPoly) -> Poly:
    return {(): dict(sp)} if sp else {}


P_ONE: Poly = p_const(S_ONE)


def p_var(link: int, comp: int) -> Poly:
    return {(((4 * link + comp), 1),): dict(S_ONE)}


def mono_mul(m1: Mono, m2: Mono) -> Mono:
    if not m1:
        return m2
    if not m2:
        return m1
    d = dict(m1)
    for v, e in m2:
        d[v] = d.get(v, 0) + e
    return tuple(sorted(d.items()))


def p_add_into(acc: Poly, p: Poly, c: Fraction = Fraction(1)) -> None:
    for m, sp in p.items():
        slot = acc.get(m)
        if slot is None:
            slot = {}
            acc[m] = slot
        sp_add_into(slot, sp, c)
        if not slot:
            del acc[m]


def p_neg(p: Poly) -> Poly:
    return {m: sp_scale(sp, Fraction(-1)) for m, sp in p.items()}


def p_scale_s(p: Poly, spower: int, c: Fraction = Fraction(1)) -> Poly:
    return {m: sp_shift(sp_scale(sp, c), spower) for m, sp in p.items() if c != 0}


def p_mul(a: Poly, b: Poly, max_out: Optional[int] = None) -> Poly:
    """Exact product; if max_out is set, abort (ContractionTooLarge)
    as soon as the result exceeds that many monomials, bounding peak
    memory to roughly the cap rather than the full product size."""
    out: Poly = {}
    check = 0
    for ma, sa in a.items():
        for mb, sb in b.items():
            m = mono_mul(ma, mb)
            sp = sp_mul(sa, sb)
            slot = out.get(m)
            if slot is None:
                out[m] = sp
                if max_out is not None:
                    check += 1
                    if check % 4096 == 0 and len(out) > max_out:
                        raise ContractionTooLarge(
                            f"product exceeded {max_out} monomials"
                        )
            else:
                sp_add_into(slot, sp)
                if not slot:
                    del out[m]
    if max_out is not None and len(out) > max_out:
        raise ContractionTooLarge(f"product exceeded {max_out} monomials")
    return out


def p_reduce_units(p: Poly) -> Poly:
    """Canonical form modulo the unit-norm ideal (w^2+x^2+y^2+z^2 = 1).

    For every link, eliminates z-exponents >= 2 via
    z^2 -> 1 - w^2 - x^2 - y^2.  The quotient ring has the monomials with
    z-exponent <= 1 as a basis, so two polynomials are equal on SU(2)^L
    iff their reduced forms are identical.  (Integration never needs
    this: the moment formula already lives on the sphere.)
    """
    work = dict(p)
    out: Poly = {}
    while work:
        m, sp = work.popitem()
        target = None
        for v, e in m:
            if v % 4 == 3 and e >= 2:
                target = (v, e)
                break
        if target is None:
            slot = out.get(m)
            if slot is None:
                out[m] = dict(sp)
            else:
                sp_add_into(slot, sp)
                if not slot:
                    del out[m]
            continue
        v, e = target
        base = v - 3  # w-var of this link
        rest = tuple((vv, ee) for vv, ee in m if vv != v)
        low = mono_mul(rest, ((v, e - 2),)) if e > 2 else rest
        for sub, sign in (
            ((), 1),
            (((base, 2),), -1),
            (((base + 1, 2),), -1),
            (((base + 2, 2),), -1),
        ):
            nm = mono_mul(low, sub)
            slot = work.get(nm)
            if slot is None:
                work[nm] = sp_scale(sp, Fraction(sign))
            else:
                sp_add_into(slot, sp, Fraction(sign))
                if not slot:
                    del work[nm]
    return out


def p_equal_on_group(a: Poly, b: Poly) -> bool:
    """Exact equality as functions on SU(2)^L (modulo unit-norm ideal)."""
    diff = dict(a)
    p_add_into(diff, b, Fraction(-1))
    return p_reduce_units(diff) == {}


def p_links(p: Poly) -> set:
    ls = set()
    for m in p:
        for v, _ in m:
            ls.add(v // 4)
    return ls


# ---------------------------------------------------------------------------
# Quaternions with polynomial components.
# ---------------------------------------------------------------------------

Quat = Tuple[Poly, Poly, Poly, Poly]


def q_link(link: int) -> Quat:
    return (p_var(link, 0), p_var(link, 1), p_var(link, 2), p_var(link, 3))


def q_conj(q: Quat) -> Quat:
    return (q[0], p_neg(q[1]), p_neg(q[2]), p_neg(q[3]))


def q_mul(q1: Quat, q2: Quat) -> Quat:
    w1, x1, y1, z1 = q1
    w2, x2, y2, z2 = q2

    def comb(terms: Sequence[Tuple[Poly, Poly, int]]) -> Poly:
        acc: Poly = {}
        for a, b, sign in terms:
            p_add_into(acc, p_mul(a, b), Fraction(sign))
        return acc

    return (
        comb([(w1, w2, 1), (x1, x2, -1), (y1, y2, -1), (z1, z2, -1)]),
        comb([(w1, x2, 1), (x1, w2, 1), (y1, z2, 1), (z1, y2, -1)]),
        comb([(w1, y2, 1), (y1, w2, 1), (z1, x2, 1), (x1, z2, -1)]),
        comb([(w1, z2, 1), (z1, w2, 1), (x1, y2, 1), (y1, x2, -1)]),
    )


def holonomy(path: Sequence[Tuple[int, int]]) -> Quat:
    """Ordered product of link quaternions; (link, +1) or (link, -1)."""
    q: Quat = (P_ONE, P_ZERO, P_ZERO, P_ZERO)
    for link, orient in path:
        ql = q_link(link) if orient == 1 else q_conj(q_link(link))
        q = q_mul(q, ql)
    return q


# ---------------------------------------------------------------------------
# Characters and activities.
# ---------------------------------------------------------------------------


def chi(n: int, q: Quat) -> Poly:
    """chi_n of the holonomy q (n = 2j integer label)."""
    if n == 0:
        return dict(P_ONE)
    two_w = {}
    p_add_into(two_w, q[0], Fraction(2))
    prev: Poly = dict(P_ONE)
    cur: Poly = two_w
    for _ in range(n - 1):
        nxt = p_mul(two_w, cur)
        p_add_into(nxt, prev, Fraction(-1))
        prev, cur = cur, nxt
    return cur


def dim(n: int) -> int:
    return n + 1


def casimir4(n: int) -> int:
    """4 * C_2 for label n = 2j:  n (n + 2)."""
    return n * (n + 2)


def heat_activity(q: Quat, nmax: int) -> Poly:
    """Truncated heat-kernel activity  sum_n d_n s^{n(n+2)} chi_n(q)."""
    acc: Poly = {}
    for n in range(nmax + 1):
        term = p_scale_s(chi(n, q), casimir4(n), Fraction(dim(n)))
        p_add_into(acc, term)
    return acc


# ---------------------------------------------------------------------------
# Exact Haar integration (uniform measure on S^3).
# ---------------------------------------------------------------------------


@lru_cache(maxsize=None)
def _dfact(k: int) -> int:
    """(2k-1)!! with (−1)!! = 1."""
    out = 1
    for i in range(1, k + 1):
        out *= 2 * i - 1
    return out


@lru_cache(maxsize=None)
def _moment(exps: Tuple[int, int, int, int]) -> Fraction:
    if any(e % 2 for e in exps):
        return Fraction(0)
    halves = tuple(e // 2 for e in exps)
    a = halves[0] + halves[1] + halves[2] + halves[3]
    num = 1
    for h in halves:
        num *= _dfact(h)
    den = (2**a) * _factorial(a + 1)
    return Fraction(num, den)


@lru_cache(maxsize=None)
def _factorial(k: int) -> int:
    out = 1
    for i in range(2, k + 1):
        out *= i
    return out


def integrate_link(p: Poly, link: int) -> Poly:
    """Exact Haar integral over one link's S^3."""
    base = 4 * link
    out: Poly = {}
    for m, sp in p.items():
        exps = [0, 0, 0, 0]
        rest: List[Tuple[int, int]] = []
        for v, e in m:
            if base <= v < base + 4:
                exps[v - base] = e
            else:
                rest.append((v, e))
        mom = _moment(tuple(exps))
        if mom == 0:
            continue
        rm: Mono = tuple(rest)
        slot = out.get(rm)
        if slot is None:
            slot = {}
            out[rm] = slot
        sp_add_into(slot, sp, mom)
        if not slot:
            del out[rm]
    return out


MAX_RESULT_MONOMIALS = 2_500_000  # peak-memory cap for guarded merges


class ContractionTooLarge(Exception):
    """Raised when a merge would exceed the monomial budget.

    This is a *resource* verdict, never a mathematical one: callers must
    report such cases as UNREACHED, not as zero or positive.
    """


def _contract_component(
    facs: List[Poly], todo: set, max_pairprod: int
) -> Poly:
    while todo:
        best_link, best_cost, best_idx = None, None, None
        for link in todo:
            idx = [i for i, f in enumerate(facs) if link in p_links(f)]
            cost = 1
            for i in idx:
                cost *= max(1, len(facs[i]))
            if best_cost is None or cost < best_cost:
                best_link, best_cost, best_idx = link, cost, idx
        assert best_link is not None and best_idx is not None
        if best_cost is not None and best_cost > max_pairprod:
            # fallback: binary pre-merge of the two cheapest factors that
            # share a to-integrate link; often unblocks the elimination
            best_pair, best_pp = None, None
            for i in range(len(facs)):
                li = p_links(facs[i]) & todo
                if not li:
                    continue
                for k in range(i + 1, len(facs)):
                    if not (li & p_links(facs[k])):
                        continue
                    pp = max(1, len(facs[i])) * max(1, len(facs[k]))
                    if best_pp is None or pp < best_pp:
                        best_pair, best_pp = (i, k), pp
            if best_pair is None or best_pp is None or best_pp > max_pairprod:
                raise ContractionTooLarge(
                    f"link {best_link}: merge cost {best_cost} > {max_pairprod}"
                )
            i, k = best_pair
            merged2 = p_mul(facs[i], facs[k], max_out=MAX_RESULT_MONOMIALS)
            facs = [f for t, f in enumerate(facs) if t not in (i, k)]
            facs.append(merged2)
            continue
        merged: Poly = dict(P_ONE)
        keep: List[Poly] = []
        for i, f in enumerate(facs):
            if i in best_idx:
                merged = p_mul(merged, f, max_out=MAX_RESULT_MONOMIALS)
            else:
                keep.append(f)
        keep.append(integrate_link(merged, best_link))
        facs = keep
        todo.discard(best_link)
    out: Poly = dict(P_ONE)
    for f in facs:
        out = p_mul(out, f)
    return out


def contract(
    factors: Iterable[Poly],
    links: Iterable[int],
    max_pairprod: int = 200_000_000,
) -> Poly:
    """Integrate the given links out of the product of factors.

    The factor graph is first split into connected components (factors
    joined by shared to-integrate links), each contracted independently
    by greedy elimination (pick the link minimizing the product of the
    touched factors' sizes), and the component results multiplied.
    Exact throughout.  A merge whose size product exceeds
    ``max_pairprod`` raises :class:`ContractionTooLarge` instead of
    exhausting memory.
    """
    facs: List[Poly] = [f for f in factors]
    todo = set(links)
    # union-find over factors via shared to-integrate links
    parent = list(range(len(facs)))

    def find(i: int) -> int:
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    link_owner: Dict[int, int] = {}
    for i, f in enumerate(facs):
        for link in p_links(f):
            if link not in todo:
                continue
            if link in link_owner:
                ra, rb = find(link_owner[link]), find(i)
                if ra != rb:
                    parent[rb] = ra
            else:
                link_owner[link] = i
    groups: Dict[int, List[int]] = {}
    for i in range(len(facs)):
        groups.setdefault(find(i), []).append(i)
    out: Poly = dict(P_ONE)
    for members in groups.values():
        comp_facs = [facs[i] for i in members]
        comp_links = set()
        for f in comp_facs:
            comp_links |= p_links(f) & todo
        res = _contract_component(comp_facs, comp_links, max_pairprod)
        out = p_mul(out, res)
    return out


def scalar(p: Poly) -> SPoly:
    """Extract the constant (fully contracted) value; asserts closure."""
    for m in p:
        if m != ():
            raise ValueError(f"network not fully contracted: leftover {m}")
    return dict(p.get((), {}))


# ---------------------------------------------------------------------------
# Lattice complexes with maximal-tree gauge fixing.
#
# For gauge-invariant integrands (products of characters of closed loops),
# Haar invariance lets us set every spanning-tree link to the identity and
# integrate only the co-tree links.  This is exact, not an approximation,
# and collapses the variable count of every honest-geometry probe.
# ---------------------------------------------------------------------------

Q_ID: Quat = (P_ONE, P_ZERO, P_ZERO, P_ZERO)


class GaugeFixedComplex:
    """A 1-complex with a chosen spanning tree gauge.

    edges: list of (tail_vertex, head_vertex).  After construction,
    ``self.free`` lists the co-tree edge indices (the only Haar
    variables), and ``holonomy_of(path)`` builds exact loop holonomies
    with tree edges replaced by the identity.
    """

    def __init__(self, n_vertices: int, edges: List[Tuple[int, int]]):
        self.edges = edges
        adj: Dict[int, List[Tuple[int, int]]] = {v: [] for v in range(n_vertices)}
        for ei, (a, b) in enumerate(edges):
            adj[a].append((b, ei))
            adj[b].append((a, ei))
        # BFS spanning tree from vertex 0
        tree: set = set()
        seen = {0}
        frontier = [0]
        while frontier:
            nxt = []
            for v in frontier:
                for u, ei in adj[v]:
                    if u not in seen:
                        seen.add(u)
                        tree.add(ei)
                        nxt.append(u)
            frontier = nxt
        if seen != set(range(n_vertices)):
            raise ValueError("complex is not connected")
        self.tree = tree
        self.free = [ei for ei in range(len(edges)) if ei not in tree]

    def edge_quat(self, ei: int, orient: int) -> Quat:
        if ei in self.tree:
            return Q_ID
        q = q_link(ei)
        return q if orient == 1 else q_conj(q)

    def holonomy_of(self, path: Sequence[Tuple[int, int]]) -> Quat:
        """path: list of (edge_index, +-1); must be a closed loop."""
        q = Q_ID
        for ei, orient in path:
            q = q_mul(q, self.edge_quat(ei, orient))
        return q

    def contract_invariant(self, factors: Iterable[Poly]) -> SPoly:
        return scalar(contract(list(factors), self.free))


def brick_complex_nd(dims: Sequence[int]):
    """Hypercubic lattice brick prod_d [0, dims[d]] in any dimension.

    Returns (complex, faces, face_meta) where faces is a list of
    oriented 4-edge paths (one per plaquette) and face_meta[i] =
    (base_point, d1, d2) records the plaquette's corner and plane.
    """
    ndim = len(dims)
    vid: Dict[Tuple[int, ...], int] = {}
    for p in iproduct(*(range(n + 1) for n in dims)):
        vid[p] = len(vid)
    edges: List[Tuple[int, int]] = []
    eid: Dict[Tuple[Tuple[int, ...], Tuple[int, ...]], int] = {}

    def step(p, d):
        q = list(p)
        q[d] += 1
        return tuple(q)

    def add_edge(a, b):
        key = (a, b)
        if key not in eid:
            eid[key] = len(edges)
            edges.append((vid[a], vid[b]))
        return eid[key]

    for p in list(vid):
        for d in range(ndim):
            q = step(p, d)
            if q in vid:
                add_edge(p, q)

    faces: List[List[Tuple[int, int]]] = []
    face_meta: List[Tuple[Tuple[int, ...], int, int]] = []
    for p in list(vid):
        for d1 in range(ndim):
            for d2 in range(d1 + 1, ndim):
                p1, p3 = step(p, d1), step(p, d2)
                if p1 not in vid or p3 not in vid:
                    continue
                p2 = step(p1, d2)
                if p2 not in vid:
                    continue
                faces.append(
                    [
                        (add_edge(p, p1), 1),
                        (add_edge(p1, p2), 1),
                        (add_edge(p3, p2), -1),
                        (add_edge(p, p3), -1),
                    ]
                )
                face_meta.append((p, d1, d2))
    cx = GaugeFixedComplex(len(vid), edges)
    return cx, faces, face_meta


def brick_complex(nx: int, ny: int, nz: int):
    """Cubic lattice brick [0,nx]x[0,ny]x[0,nz]: vertices, edges, faces.

    Returns (complex, faces) where faces is a list of oriented edge
    paths (one per plaquette), each a list of (edge_index, +-1).
    """
    vid: Dict[Tuple[int, int, int], int] = {}
    for x in range(nx + 1):
        for y in range(ny + 1):
            for z in range(nz + 1):
                vid[(x, y, z)] = len(vid)
    edges: List[Tuple[int, int]] = []
    eid: Dict[Tuple[Tuple[int, int, int], Tuple[int, int, int]], int] = {}

    def add_edge(a, b):
        key = (a, b)
        if key not in eid:
            eid[key] = len(edges)
            edges.append((vid[a], vid[b]))
        return eid[key]

    def step(p, d):
        return (p[0] + (d == 0), p[1] + (d == 1), p[2] + (d == 2))

    for p in list(vid):
        for d in range(3):
            q = step(p, d)
            if q in vid:
                add_edge(p, q)

    faces: List[List[Tuple[int, int]]] = []
    for p in list(vid):
        for d1 in range(3):
            for d2 in range(d1 + 1, 3):
                p1, p2, p3 = step(p, d1), step(step(p, d1), d2), step(p, d2)
                if p1 in vid and p2 in vid and p3 in vid:
                    faces.append(
                        [
                            (add_edge(p, p1), 1),
                            (add_edge(p1, p2), 1),
                            (add_edge(p3, p2), -1),
                            (add_edge(p, p3), -1),
                        ]
                    )
    cx = GaugeFixedComplex(len(vid), edges)
    return cx, faces


# ---------------------------------------------------------------------------
# Sign analysis of exact s-polynomials on (0, 1).
# ---------------------------------------------------------------------------


def sp_str(p: SPoly) -> str:
    if not p:
        return "0"
    terms = []
    for k in sorted(p):
        c = p[k]
        terms.append(f"{c}" if k == 0 else f"{c}*s^{k}")
    return " + ".join(terms).replace("+ -", "- ")


def sign_on_unit_interval(p: SPoly) -> str:
    """Exact sign verdict of p(s) on the open interval (0, 1).

    Returns one of 'zero', 'positive', 'negative', 'mixed'.  Fast paths by
    coefficient signs; otherwise exact root counting via Sturm sequences
    (sympy, rational arithmetic).
    """
    if not p:
        return "zero"
    signs = {(""" +""" if v > 0 else "-") for v in p.values()}
    if signs == {" +"}:
        return "positive"
    if signs == {"-"}:
        return "negative"
    import sympy

    s = sympy.Symbol("s")
    expr = sum(sympy.Rational(v.numerator, v.denominator) * s**k for k, v in p.items())
    poly = sympy.Poly(sympy.expand(expr), s)
    if poly.is_zero:
        return "zero"
    # Sign changes on (0,1) happen exactly at odd-multiplicity real roots.
    _, factors = poly.sqf_list()
    odd = sympy.Poly(1, s)
    for fac, mult in factors:
        if mult % 2 == 1:
            odd = odd * fac
    n_in_closed = sympy.polys.polytools.count_roots(odd, 0, 1)
    n_open = n_in_closed - (1 if odd.eval(0) == 0 else 0) - (1 if odd.eval(1) == 0 else 0)
    if n_open > 0:
        return "mixed"
    # constant sign on (0,1): sample at rationals until nonzero
    k = 2
    while True:
        val = poly.eval(sympy.Rational(1, k))
        if val != 0:
            return "positive" if val > 0 else "negative"
        k += 1
