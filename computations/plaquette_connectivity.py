"""Exact enumeration of plaquette-adjacency counts on the hypercubic lattice Z^d.

Milestone SL.1 (fiducial extraction), Part A.

Purpose
-------
The repo's ``computations/large_field_kp.py`` consumes ``MU_PLAQUETTE_4D = 16``
as the plaquette-polymer connectivity constant in the Kotecky-Preiss /
Brydges-Federbush convergence bound

    K_lf = q / (1 - q),   q = mu_plaq * Z_t,

which rests on the counting statement

    N_n(P0) := #{ edge-connected plaquette-polymers X, |X| = n, P0 in X }
             <= mu_plaq ** n,

where "edge-connected" means: the plaquettes of X form a connected graph
under the adjacency "shares at least one lattice bond (edge)".  That is the
adjacency notion the code consumes (see notes/fiducials_notes.md sections 3.1
and 3.2, and BFS 1978 eq. (4.24) for the per-bond count).

The literature-shape value 16 is attributed to the formula 5d - 4 (Seiler
1982, LNP 159 -- cited but unverified).  This module derives, by exact
integer enumeration (no floats), every natural adjacency count for a fixed
plaquette on Z^d at d = 2, 3, 4, 5:

  (a) EDGE      -- plaquettes sharing >= 1 lattice edge with P0
                   (split into coplanar and non-coplanar)
  (b) VERTEX    -- plaquettes sharing >= 1 lattice vertex with P0
                   (and the vertex-only subset: vertex but no edge)
  (c) CODE      -- the notion the KP bound consumes: (a), the max-degree of
                   the plaquette edge-adjacency graph, plus the exact small-n
                   polymer counts N_n under that adjacency as a direct witness
                   for/against N_n <= 16^n.

Also enumerated: plaquettes containing a fixed bond (BFS's 2(d-1)) and
plaquettes containing a fixed vertex.

Exhaustiveness proof
--------------------
A plaquette is stored canonically as (base, mu, nu), base in Z^d,
0 <= mu < nu < d, with vertex set {base, base+e_mu, base+e_nu,
base+e_mu+e_nu}; every coordinate of every vertex lies in
{base_i, base_i + 1}.  P0's vertices have all coordinates in {0, 1}.
Hence a plaquette sharing a VERTEX (a fortiori an edge) with P0 must have
base_i in {-1, 0, 1} for every axis i: if base_i <= -2 its vertex coords on
axis i lie in {base_i, base_i+1} subset (-inf, -1], disjoint from {0, 1};
if base_i >= 2 they lie in [2, +inf).  The enumeration therefore scans the
strictly larger box base in [-2, 2]^d and asserts that no qualifying
plaquette touches |base_i| = 2, which certifies the box is exhaustive.

Integer arithmetic only; no floats anywhere in the counting.

Run:  python3 plaquette_connectivity.py [--nmax4 N] [--nmax3 N]
"""

from __future__ import annotations

import argparse
import sys
from itertools import combinations, product

Plaq = tuple  # (base: tuple[int, ...], mu: int, nu: int)


# ----------------------------------------------------------------------
# Basic geometry (canonical plaquette representation)
# ----------------------------------------------------------------------

def unit(d: int, axis: int) -> tuple:
    return tuple(1 if i == axis else 0 for i in range(d))


def vadd(v: tuple, w: tuple) -> tuple:
    return tuple(a + b for a, b in zip(v, w))


def vsub(v: tuple, w: tuple) -> tuple:
    return tuple(a - b for a, b in zip(v, w))


def plaquette_vertices(p: Plaq, d: int) -> frozenset:
    base, mu, nu = p
    emu, enu = unit(d, mu), unit(d, nu)
    return frozenset(
        [base, vadd(base, emu), vadd(base, enu), vadd(vadd(base, emu), enu)]
    )


def _edge(v: tuple, w: tuple) -> tuple:
    return (v, w) if v <= w else (w, v)


def plaquette_edges(p: Plaq, d: int) -> frozenset:
    base, mu, nu = p
    emu, enu = unit(d, mu), unit(d, nu)
    a, b, c, e = base, vadd(base, emu), vadd(base, enu), vadd(vadd(base, emu), enu)
    return frozenset([_edge(a, b), _edge(a, c), _edge(b, e), _edge(c, e)])


def all_plaquettes_in_box(d: int, lo: int, hi: int):
    axes = list(combinations(range(d), 2))
    for base in product(range(lo, hi + 1), repeat=d):
        for mu, nu in axes:
            yield (base, mu, nu)


# ----------------------------------------------------------------------
# (a), (b): neighbor counts of the fixed plaquette P0
# ----------------------------------------------------------------------

def fixed_plaquette(d: int) -> Plaq:
    return ((0,) * d, 0, 1)


def neighbor_counts(d: int) -> dict:
    """Exact neighbor counts of P0 = unit xy-plaquette at the origin in Z^d.

    Returns a dict of exact integer counts for every adjacency notion.
    Asserts the exhaustiveness certificate described in the module docstring.
    """
    P0 = fixed_plaquette(d)
    V0 = plaquette_vertices(P0, d)
    E0 = plaquette_edges(P0, d)

    n_edge = 0
    n_edge_coplanar = 0       # shares an edge AND lies in the same (0,1)-plane
    n_edge_noncoplanar = 0
    n_vertex = 0              # shares >= 1 vertex (includes edge-sharers)
    n_vertex_only = 0         # shares a vertex but NO edge
    n_two_vertices_no_edge = 0  # diagonal-sharing check (expected 0)

    for p in all_plaquettes_in_box(d, -2, 2):
        if p == P0:
            continue
        sv = plaquette_vertices(p, d) & V0
        if not sv:
            continue
        # exhaustiveness certificate: qualifying plaquettes live strictly
        # inside the scanned box
        base = p[0]
        assert all(-1 <= c <= 1 for c in base), (
            f"exhaustiveness violated at d={d}: {p}"
        )
        se = plaquette_edges(p, d) & E0
        n_vertex += 1
        if se:
            n_edge += 1
            if p[1] == 0 and p[2] == 1:
                n_edge_coplanar += 1
            else:
                n_edge_noncoplanar += 1
        else:
            n_vertex_only += 1
            if len(sv) >= 2:
                n_two_vertices_no_edge += 1

    return {
        "d": d,
        "edge": n_edge,
        "edge_coplanar": n_edge_coplanar,
        "edge_noncoplanar": n_edge_noncoplanar,
        "vertex": n_vertex,
        "vertex_only": n_vertex_only,
        "two_vertices_no_edge": n_two_vertices_no_edge,
    }


def plaquettes_containing_bond(d: int) -> int:
    """# plaquettes containing the fixed bond (0, e_0).  BFS: 2(d-1)."""
    b0 = _edge((0,) * d, unit(d, 0))
    return sum(
        1
        for p in all_plaquettes_in_box(d, -2, 2)
        if b0 in plaquette_edges(p, d)
    )


def plaquettes_containing_vertex(d: int) -> int:
    """# plaquettes containing the origin vertex.  Expected 4*C(d,2) = 2d(d-1)."""
    o = (0,) * d
    return sum(
        1
        for p in all_plaquettes_in_box(d, -2, 2)
        if o in plaquette_vertices(p, d)
    )


# ----------------------------------------------------------------------
# (c): polymer counts N_n under the code's adjacency (edge-adjacency)
# ----------------------------------------------------------------------

def edge_adjacent_plaquettes(p: Plaq, d: int) -> tuple:
    """All plaquettes sharing >= 1 edge with p (the code's adjacency).

    Constructive: for each of p's 4 edges, the plaquettes containing that
    edge are, per perpendicular axis b, the two squares spanned by
    (edge-axis a, b) with base at the edge's min-corner or shifted by -e_b.
    Yields exactly 8d - 12 distinct neighbors (asserted).
    """
    out = set()
    for v, w in plaquette_edges(p, d):
        diff = vsub(w, v)
        a = next(i for i, c in enumerate(diff) if c != 0)
        vmin = v  # canonical edge has v <= w and they differ only on axis a
        for b in range(d):
            if b == a:
                continue
            mu, nu = (a, b) if a < b else (b, a)
            for base in (vmin, vsub(vmin, unit(d, b))):
                q = (base, mu, nu)
                if q != p:
                    out.add(q)
    assert len(out) == 8 * d - 12, (p, d, len(out))
    return tuple(sorted(out))


def connected_polymer_counts(d: int, n_max: int) -> list:
    """Exact N_n = # edge-connected plaquette sets of size n containing P0.

    Uses the standard duplicate-free connected-subgraph enumeration: extend
    the current set S by candidates in list order; skipping a candidate bans
    it for the entire remainder of that branch, so every connected superset
    of {P0} is generated exactly once.
    """
    P0 = fixed_plaquette(d)
    nbr_cache: dict = {}

    def nbrs(p: Plaq) -> tuple:
        r = nbr_cache.get(p)
        if r is None:
            r = edge_adjacent_plaquettes(p, d)
            nbr_cache[p] = r
        return r

    counts = [0] * (n_max + 1)  # counts[n] = N_n; counts[0] unused

    def extend(S: frozenset, cand: tuple, banned: frozenset):
        counts[len(S)] += 1
        if len(S) == n_max:
            return
        for i, c in enumerate(cand):
            banned_new = banned.union(cand[:i])
            S_new = S | {c}
            rest = cand[i + 1:]
            rest_set = set(rest)
            extra = tuple(
                x
                for x in nbrs(c)
                if x not in S_new and x not in banned_new and x not in rest_set
            )
            extend(S_new, rest + extra, banned_new)

    extend(frozenset([P0]), nbrs(P0), frozenset())
    return counts


# ----------------------------------------------------------------------
# Formula identification
# ----------------------------------------------------------------------

CANDIDATE_FORMULAS = {
    "5d-4": lambda d: 5 * d - 4,
    "8d-12": lambda d: 8 * d - 12,
    "8(d-2)": lambda d: 8 * (d - 2),
    "2(d-1)": lambda d: 2 * (d - 1),
    "2d-3": lambda d: 2 * d - 3,
    "2d(d-1)": lambda d: 2 * d * (d - 1),
    "4(d-1)": lambda d: 4 * (d - 1),
}


def fit_polynomial_in_d(pairs):
    """Exact polynomial through the (d, count) points (Lagrange, Fractions).

    Returns coefficient list [c0, c1, ...] (c_k * d^k) as exact Fractions.
    """
    from fractions import Fraction

    xs = [Fraction(d) for d, _ in pairs]
    ys = [Fraction(v) for _, v in pairs]
    n = len(xs)
    # Lagrange interpolation, expanded to coefficients.
    coeffs = [Fraction(0)] * n
    for i in range(n):
        # numerator polynomial prod_{j != i} (x - x_j)
        poly = [Fraction(1)]
        denom = Fraction(1)
        for j in range(n):
            if j == i:
                continue
            denom *= xs[i] - xs[j]
            poly = [Fraction(0)] + poly  # multiply by x
            for k in range(len(poly) - 1):
                poly[k] -= xs[j] * poly[k + 1] * 0  # placeholder
        # simpler: build via convolution
        poly = [Fraction(1)]
        for j in range(n):
            if j == i:
                continue
            # poly *= (x - xs[j])
            new = [Fraction(0)] * (len(poly) + 1)
            for k, c in enumerate(poly):
                new[k + 1] += c
                new[k] -= c * xs[j]
            poly = new
        scale = ys[i] / denom
        for k, c in enumerate(poly):
            coeffs[k] += scale * c
    return coeffs


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax4", type=int, default=5,
                    help="max polymer size for exact N_n at d=4")
    ap.add_argument("--nmax3", type=int, default=5,
                    help="max polymer size for exact N_n at d=3")
    args = ap.parse_args()

    dims = (2, 3, 4, 5)
    rows = {d: neighbor_counts(d) for d in dims}
    per_bond = {d: plaquettes_containing_bond(d) for d in dims}
    per_vertex = {d: plaquettes_containing_vertex(d) for d in dims}

    print("Exact plaquette-adjacency counts on Z^d (fixed unit xy-plaquette P0)")
    print("=" * 74)
    hdr = (f"{'notion':<34}" + "".join(f"d={d:<6}" for d in dims))
    print(hdr)
    print("-" * 74)

    def row(label, getter):
        print(f"{label:<34}" + "".join(f"{getter(d):<8}" for d in dims))

    row("(a) share >=1 edge", lambda d: rows[d]["edge"])
    row("    ... coplanar", lambda d: rows[d]["edge_coplanar"])
    row("    ... non-coplanar", lambda d: rows[d]["edge_noncoplanar"])
    row("(b) share >=1 vertex", lambda d: rows[d]["vertex"])
    row("    ... vertex-only (no edge)", lambda d: rows[d]["vertex_only"])
    row("    ... >=2 shared verts, no edge", lambda d: rows[d]["two_vertices_no_edge"])
    row("plaquettes containing fixed bond", lambda d: per_bond[d])
    row("plaquettes containing fixed vertex", lambda d: per_vertex[d])
    print("-" * 74)
    row("formula 5d-4 (Seiler-cited)", lambda d: 5 * d - 4)
    row("formula 8d-12", lambda d: 8 * d - 12)
    row("formula 8(d-2)", lambda d: 8 * (d - 2))
    row("formula 2(d-1) (BFS 4.24)", lambda d: 2 * (d - 1))
    row("formula 2d(d-1)", lambda d: 2 * d * (d - 1))
    print()

    # Formula matches per notion, over d in {3,4,5} (and noting d=2)
    print("Formula identification over d in {3,4,5}:")
    notions = {
        "share >=1 edge": lambda d: rows[d]["edge"],
        "share >=1 edge, coplanar": lambda d: rows[d]["edge_coplanar"],
        "share >=1 edge, non-coplanar": lambda d: rows[d]["edge_noncoplanar"],
        "share >=1 vertex": lambda d: rows[d]["vertex"],
        "vertex-only": lambda d: rows[d]["vertex_only"],
        "containing fixed bond": lambda d: per_bond[d],
        "containing fixed vertex": lambda d: per_vertex[d],
    }
    for name, getter in notions.items():
        matches = [
            fname
            for fname, f in CANDIDATE_FORMULAS.items()
            if all(f(d) == getter(d) for d in (3, 4, 5))
        ]
        coeffs = fit_polynomial_in_d([(d, getter(d)) for d in (3, 4, 5)])
        poly = " + ".join(
            f"{c}*d^{k}" if k else f"{c}"
            for k, c in enumerate(coeffs)
            if c != 0
        ) or "0"
        d2_ok = ""
        print(f"  {name:<30} exact-fit: {poly:<28} "
              f"matches: {matches if matches else 'NONE of the candidates'}")
    print()
    print("Coincidence checks at d = 4 only:")
    for name, getter in notions.items():
        if getter(4) == 16:
            print(f"  d=4 count 16 == 5*4-4 for notion: {name} "
                  f"(but at d=3: {getter(3)} vs 5d-4 = 11; "
                  f"d=5: {getter(5)} vs 5d-4 = 21)")
    print()

    # (c) the code's notion: polymer counts under edge-adjacency
    print("(c) Code-consumed notion: N_n = # edge-connected plaquette polymers")
    print("    of size n containing P0 (exact enumeration), vs mu^n bounds:")
    for d, nmax in ((3, args.nmax3), (4, args.nmax4)):
        counts = connected_polymer_counts(d, nmax)
        mu_lit = 5 * d - 4
        delta = 8 * d - 12
        print(f"  d = {d}:  (5d-4 = {mu_lit}, max-degree Delta = {delta})")
        prev = None
        for n in range(1, nmax + 1):
            Nn = counts[n]
            ratio = f"{Nn / prev:8.3f}" if prev else "     ---"
            ok_lit = "OK " if Nn <= mu_lit ** n else "VIOLATED"
            print(f"    n={n}:  N_n = {Nn:>10}   N_n/N_(n-1) = {ratio}   "
                  f"N_n <= (5d-4)^n = {mu_lit ** n:>12}: {ok_lit}")
            prev = Nn
    print()
    print("Derived facts for the KP bound (d = 4):")
    print("  * adjacency the code consumes: plaquette edge(bond)-adjacency")
    print(f"  * max degree of that graph:   Delta = 8d-12 = "
          f"{rows[4]['edge']}  (exact, enumerated)")
    print("  * rigorous BF connectivity bound: mu <= e * Delta = 20e (float "
          "only downstream; the integer content is Delta = 20)")
    print("  * 5d-4 = 16 equals the NON-COPLANAR edge-neighbor count 8(d-2)")
    print("    at d = 4 ONLY (8, 16, 24 vs 11, 16, 21): a numerical")
    print("    coincidence, not a formula match.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
