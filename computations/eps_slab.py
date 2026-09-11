"""eps_slab(M) — the DP.2 activity-truncation modulus, certified by pure
combinatorial enumeration (no Haar contraction, no wall-clock budget).

Simplification-Ledger item 7 requires the M-truncation error to enter the
modulus registry as a NAMED modulus with witness discipline, not as an
UNREACHED wall-clock verdict.  This module supplies exactly that.

**The bound.**  Every configuration of the owned-boundary slab that is
present at truncation M+1 but absent at M must carry spin >= M+1 on at
least one face.  Its contribution to T[n,m](s) is a monomial

    (positive weight) * s^{E},   E = sum over faces of C(spin),

with C(k) = k(k+2) the 4x Casimir; so

    min-deg( T_{M+1}[n,m] - T_M[n,m] )  >=  E*(n, m, M)
      := min { E(config) : config admissible, max spin = M+1 }.

E* is a finite combinatorial minimum over triad-admissible labellings of
the slab — decidable exactly, with no dependence on which expensive
skeleton classes a given run happened to reach.  Hence

    | T_{M+1}[n,m](s) - T_M[n,m](s) |  <=  (tail mass) * s^{E*}
                                            for all s in (0,1),

and eps_slab(M) := s^{E*(M)} is the certified suppression exponent.

The naive bound is E* >= C(M+1) (one face carries the new spin).  The
computed values are far larger, because a face at spin M+1 cannot appear
in isolation: the triad conditions at the 4-valent interior edge and at
the corner-linked perimeter-wall classes force companion faces up as
well.  That gap is the substantive content here.

Admissibility mirrors `slab_blocking_kernel`: perimeter-wall classes
q1..q4 (each class carries TWO faces, hence weight 2*C(q_i)), interior
walls w1..w4 (one face each), and four tiles per layer with the layer's
coarse loop spin.  Triads: (loop, q_i, tile_i) at every tile-perimeter
edge, (tile_{i-1}, tile_i, w_{i-1}) cyclically, and the central 4-valent
edge parity sum(w) even.
"""
from __future__ import annotations

import itertools
import sys



from computations.exact_haar_network import casimir4      # noqa: E402


def triad_ok(a: int, b: int, c: int) -> bool:
    return (a + b + c) % 2 == 0 and abs(a - b) <= c <= a + b


def layer_labellings(loop: int, q, w, M: int):
    """All tile 4-tuples for one layer, given loop spin and skeleton."""
    cand = [[a for a in range(M + 1) if triad_ok(loop, qi, a)] for qi in q]
    out = []
    for tiles in itertools.product(*cand):
        ok = all(triad_ok(tiles[i - 1], tiles[i], w[i - 1]) for i in range(4))
        if ok:
            out.append(tiles)
    return out


def skeletons(M: int):
    for q in itertools.product(range(M + 1), repeat=4):
        wch = []
        good = True
        for i in range(4):
            ws = [w for w in range(M + 1)
                  if triad_ok(q[i], q[(i + 1) % 4], w)]
            if not ws:
                good = False
                break
            wch.append(ws)
        if not good:
            continue
        for w in itertools.product(*wch):
            if sum(w) % 2 == 0:
                yield q, w


def exponent(q, w, top, bot) -> int:
    return (sum(2 * casimir4(qi) for qi in q)
            + sum(casimir4(wi) for wi in w)
            + sum(casimir4(a) for a in top)
            + sum(casimir4(b) for b in bot))


def e_star(n: int, m: int, M: int):
    """min exponent of a configuration whose max spin is exactly M+1."""
    best, witness = None, None
    Mp = M + 1
    for q, w in skeletons(Mp):
        tops = layer_labellings(n, q, w, Mp)
        bots = layer_labellings(m, q, w, Mp)
        if not tops or not bots:
            continue
        for top in tops:
            for bot in bots:
                if max(list(q) + list(w) + list(top) + list(bot)) != Mp:
                    continue
                E = exponent(q, w, top, bot)
                if best is None or E < best:
                    best, witness = E, (q, w, top, bot)
    return best, witness


def main():
    M = 1
    print("=" * 74)
    print(f"eps_slab({M}) — certified truncation exponent E*(n,m,{M})")
    print(f"  naive single-face bound: C({M+1}) = {casimir4(M + 1)}")
    print("=" * 74)
    rows = []
    for n in range(4):
        for m in range(n, 4):
            E, wit = e_star(n, m, M)
            rows.append(((n, m), E))
            if E is None:
                print(f"  T[{n},{m}]: no admissible spin-{M+1} configuration "
                      f"-> difference is IDENTICALLY ZERO")
                continue
            q, w, top, bot = wit
            print(f"  T[{n},{m}]: E* = {E:3d}   witness q={q} w={w} "
                  f"top={top} bot={bot}")
    ok = [E for _, E in rows if E is not None]
    print(f"\n  GLOBAL: min E* over n,m <= 3 is {min(ok)}  "
          f"(vs naive {casimir4(M + 1)})")
    print(f"  => eps_slab({M}) <= (tail mass) * s^{min(ok)} on (0,1);")
    print(f"     at s = 1/2 the suppression factor alone is "
          f"2^-{min(ok)} = {2.0 ** -min(ok):.3e}")


if __name__ == "__main__":
    main()
