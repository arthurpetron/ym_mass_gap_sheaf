"""SU(2) M -> infinity: certified windows for the slab kernel via a
DOMINATION TRANSFER OPERATOR (work_plan §16f residual (b), first
executable stage; §16c route (a) 'certified windows at growing M with
eps_slab-grade tails').

**The bound.**  In the fixed-tile form (dp3_fixed_tile),

    T[n,m](s) = sum over labellings L = (q_1..4, w_1..4, a_1..4,
                b_1..4) of  W(L) * N(L),
    W(L) = prod over the 20 faces of d_spin s^{C(spin)}  > 0,

with N(L) the pure-character Haar value and admissibility exactly the
eps_slab triad conditions.  Since |chi_k| <= d_k pointwise and Haar
is a probability measure,  |N(L)| <= d_n d_m prod_f d_spin, so

    |T_inf[n,m](s) - T_M[n,m](s)|
        <= d_n d_m * sum_{L admissible, max spin > M}
                     prod_f d_spin^2 s^{C(spin)}    =: TAIL(M; s).

**The transfer factorization of the dominated mass.**  The
admissibility graph is a 4-cycle: corner i carries (a_i, b_i, q_i)
with triads (n, q_i, a_i), (m, q_i, b_i); side i carries w_i with
triads (a_i, a_{i+1}, w_i), (b_i, b_{i+1}, w_i); the central edge
demands sum w_i even.  Hence the dominated mass is EXACTLY

    d_n d_m * tr_{parity-even}( T^4 ),

T the nonnegative transfer matrix on states (a, b, q) with node
weight d_a^2 s^{C(a)} d_b^2 s^{C(b)} d_q^4 s^{2C(q)} and
parity-resolved edge weight sum_w d_w^2 s^{C(w)}.  TAIL(M) is the
full trace minus the labels-<=-M trace, computed EXACTLY at a label
cutoff Lambda; the Lambda-slop is bounded RIGOROUSLY by Frobenius /
Cauchy-Schwarz estimates on the symmetrized kernel
sqrt(nw) edge sqrt(nw) (same trace), with every ingredient a
certified geometric sum.  All rationals.

This transfer operator is the |N|-free SHELL of the true corner
transfer factorization (the (b) program): same label space, same
cyclic structure — the open half is to replace the domination
weights by the actual recoupling amplitudes.

**T_2 finality.**  The banked M=2 entries carry UNREACHED configs
(labels listed, exact below E*): their mass is bounded per listed
config by d_n d_m prod d^2 s^E — added to the window as U_2(s).

**Consumption.**  T_inf in [T_2 - U_2 - TAIL(2), T_2 + U_2 +
TAIL(2)]; the discriminating observable X_11 = log(T11 T00 / T01^2)
gets certified M -> infinity windows wherever the bounds are small —
the designated first consumer of the resummation, executed against
the exact flat target (2/3) C(n) C(m) tau^2 + x3 tau^3 from
c_su2_tau3.

Run:  python -m computations.su2_minf_windows
"""

from __future__ import annotations

import json
import math
import os
import sys
from fractions import Fraction
from typing import Dict, List, Tuple

Frac = Fraction
HERE = os.path.dirname(os.path.abspath(__file__))
OUT_JSON = os.path.join(HERE, "su2_minf_windows_results.json")

sys.set_int_max_str_digits(0)


def cas4(k: int) -> int:
    return k * (k + 2)


def dim(k: int) -> int:
    return k + 1


def triad(a: int, b: int, c: int) -> bool:
    return (a + b + c) % 2 == 0 and abs(a - b) <= c <= a + b


# ---------------------------------------------------------------------------
# Certified geometric label sums.
# ---------------------------------------------------------------------------


def tail_pow2(K: int, s: Frac) -> Frac:
    """sum_{k > K} (k+1)^2 s^{C(k)}, certified: consecutive ratio
    <= 4 s^{2K+3} < 1."""
    r = 4 * s ** (2 * K + 3)
    assert r < 1
    return Frac((K + 2) ** 2) * s ** cas4(K + 1) / (1 - r)


def tail_pow4(K: int, s: Frac) -> Frac:
    r = 16 * s ** (2 * (2 * K + 3))
    assert r < 1
    return Frac((K + 2) ** 4) * s ** (2 * cas4(K + 1)) / (1 - r)


def sum_pow2(K: int, s: Frac) -> Frac:
    return sum((Frac((k + 1) ** 2) * s ** cas4(k)
                for k in range(K + 1)), Frac(0)) + tail_pow2(K, s)


def sum_pow4(K: int, s: Frac) -> Frac:
    return sum((Frac((k + 1) ** 4) * s ** (2 * cas4(k))
                for k in range(K + 1)), Frac(0)) + tail_pow4(K, s)


# ---------------------------------------------------------------------------
# The domination transfer operator.
# ---------------------------------------------------------------------------


class DomTransfer:
    def __init__(self, n: int, m: int, s: Frac, lam: int):
        self.n, self.m, self.s, self.lam = n, m, s, lam

    def _states(self, cap: int):
        out = []
        for q in range(cap + 1):
            for a in range(cap + 1):
                if not triad(self.n, q, a):
                    continue
                for b in range(cap + 1):
                    if triad(self.m, q, b):
                        out.append((a, b, q))
        return out

    def node_w(self, st) -> Frac:
        a, b, q = st
        s = self.s
        return (Frac(dim(a) ** 2) * s ** cas4(a)
                * Frac(dim(b) ** 2) * s ** cas4(b)
                * Frac(dim(q) ** 4) * s ** (2 * cas4(q)))

    def edge_w(self, st1, st2, wcap: int, parity: int) -> Frac:
        a1, b1, _ = st1
        a2, b2, _ = st2
        tot = Frac(0)
        for w in range(parity, wcap + 1, 2):
            if triad(a1, a2, w) and triad(b1, b2, w):
                tot += Frac(dim(w) ** 2) * self.s ** cas4(w)
        return tot

    def dominated_trace(self, cap: int) -> Frac:
        """d_n d_m * tr_{parity-even}(T^4), ALL labels <= cap: exact."""
        sts = self._states(cap)
        ns = len(sts)
        nw = [self.node_w(st) for st in sts]
        M0 = [[nw[j] * self.edge_w(sts[i], sts[j], cap, 0)
               for j in range(ns)] for i in range(ns)]
        M1 = [[nw[j] * self.edge_w(sts[i], sts[j], cap, 1)
               for j in range(ns)] for i in range(ns)]

        def mat_mul(A, B):
            out = [[Frac(0)] * ns for _ in range(ns)]
            for i in range(ns):
                Ai = A[i]
                oi = out[i]
                for k in range(ns):
                    aik = Ai[k]
                    if aik == 0:
                        continue
                    Bk = B[k]
                    for j in range(ns):
                        if Bk[j]:
                            oi[j] += aik * Bk[j]
            return out

        import itertools as it

        prods = {}
        mats = {0: M0, 1: M1}
        for p1 in (0, 1):
            for p2 in (0, 1):
                prods[(p1, p2)] = mat_mul(mats[p1], mats[p2])
        tot = Frac(0)
        for ps in it.product((0, 1), repeat=4):
            if sum(ps) % 2:
                continue
            A = prods[(ps[0], ps[1])]
            B = prods[(ps[2], ps[3])]
            tot += sum(sum(A[i][k] * B[k][i] for k in range(ns))
                       for i in range(ns))
        return Frac(dim(self.n) * dim(self.m)) * tot

    def lam_slop(self) -> Frac:
        """Certified bound on the dominated mass of 4-cycles using
        any label > lam, by a UNION BOUND over the position of the
        first bad element: every such cycle passes through a bad
        state (some label > lam) at one of the 4 corners or a bad
        wall at one of the 4 sides; dropping the triad constraints
        of the remaining elements only increases the mass, so

          slop <= d_n d_m [ 4 * NodeTail * NodeSum^3 * Wall^4
                            + 4 * WallTail * Wall^3 * NodeSum^4 ],

        every factor a certified geometric sum.  No square roots —
        the bound carries the full s^{C(lam+1)} decay of the tail."""
        s = self.s
        lam = self.lam
        S2 = sum_pow2(lam, s)
        S4 = sum_pow4(lam, s)
        node_sum = S2 * S2 * S4          # >= sum of all node weights
        node_tail = (2 * tail_pow2(lam, s) * S2 * S4
                     + S2 * S2 * tail_pow4(lam, s))
        w_all = S2                        # >= sum_w d_w^2 s^{C(w)}
        w_tail = tail_pow2(lam, s)
        slop = (4 * node_tail * node_sum ** 3 * w_all ** 4
                + 4 * w_tail * w_all ** 3 * node_sum ** 4)
        return Frac(dim(self.n) * dim(self.m)) * slop


def tail_bound(n: int, m: int, s: Frac, M: int, lam: int) -> Frac:
    dt = DomTransfer(n, m, s, lam)
    full = dt.dominated_trace(lam)
    upto = dt.dominated_trace(M)
    assert full >= upto
    return full - upto + dt.lam_slop()


# ---------------------------------------------------------------------------
# T_2 with finality: poly value + unreached-config mass bound.
# ---------------------------------------------------------------------------


def load_m2():
    path = os.path.join(HERE, "dp3_m2_entries.json")
    with open(path) as fh:
        return json.load(fh)


def entry_value_and_unreached(d, key: str, n: int, m: int,
                              s: Frac) -> Tuple[Frac, Frac]:
    poly = {int(k): Frac(v[0], v[1]) for k, v in d[key]["poly"].items()}
    val = sum(c * s ** k for k, c in poly.items())
    u = Frac(0)
    for cfg in d[key]["unreached"]:
        if "q" not in cfg:
            raise ValueError("unreached config without labels")
        mass = Frac(dim(n) * dim(m))
        for q in cfg["q"]:
            mass *= Frac(dim(q) ** 4) * s ** (2 * cas4(q))
        for w in cfg["w"]:
            mass *= Frac(dim(w) ** 2) * s ** cas4(w)
        for a in cfg["top"]:
            mass *= Frac(dim(a) ** 2) * s ** cas4(a)
        for b in cfg["bot"]:
            mass *= Frac(dim(b) ** 2) * s ** cas4(b)
        u += mass
    return val, u


# ---------------------------------------------------------------------------
# Consumption: certified X_11 windows vs the exact flat target.
# ---------------------------------------------------------------------------


def x11_window(s: Frac, lam: int = 6) -> Dict:
    d = load_m2()
    T, U, tails = {}, {}, {}
    for key, (n, m) in (("0,0", (0, 0)), ("1,1", (1, 1)),
                        ("0,1", (0, 1))):
        T[key], U[key] = entry_value_and_unreached(d, key, n, m, s)
        tails[key] = tail_bound(n, m, s, 2, lam)
    lo = {k: T[k] - U[k] - tails[k] for k in T}
    hi = {k: T[k] + U[k] + tails[k] for k in T}
    ok_pos = all(v > 0 for v in lo.values())
    out = {"s": str(s),
           "T2": {k: float(T[k]) for k in T},
           "unreached": {k: float(U[k]) for k in U},
           "tail": {k: float(tails[k]) for k in tails},
           "positive": ok_pos}
    if ok_pos:
        r_lo = lo["1,1"] * lo["0,0"] / (hi["0,1"] ** 2)
        r_hi = hi["1,1"] * hi["0,0"] / (lo["0,1"] ** 2)
        out["X11_lo"] = math.log(float(r_lo))
        out["X11_hi"] = math.log(float(r_hi))
        out["ratio_gt_1_certified"] = bool(r_lo > 1)
    return out


def main() -> None:
    import time

    t0 = time.time()
    print("SU(2) M -> infinity: domination-transfer tail bounds")
    print("=" * 72)
    print("GATE — domination: dominated(2) >= |T_2| entrywise sums")
    d = load_m2()
    ok = True
    for s in (Frac(1, 2), Frac(3, 4)):
        for key, (n, m) in (("0,0", (0, 0)), ("1,1", (1, 1)),
                            ("0,1", (0, 1))):
            dt = DomTransfer(n, m, s, 4)
            dom2 = dt.dominated_trace(2)
            t2, u2 = entry_value_and_unreached(d, key, n, m, s)
            good = dom2 + u2 >= t2      # reached mass <= domination
            ok &= good
            print(f"  s={s} T[{key}]: dominated(2)={float(dom2):.4f}"
                  f"  T_2={float(t2):.4f}  unreached<={float(u2):.2e}"
                  f"  {'OK' if good else 'FAIL'}")
    print(f"  gate: {'PASSED' if ok else 'FAILED'}  "
          f"[{time.time() - t0:.0f}s]")

    print("=" * 72)
    print("Certified X_11 windows at M -> infinity  (lam = 6)")
    res = {"gate": ok, "rows": []}
    x3 = None
    try:
        with open(os.path.join(HERE, "c_su2_tau3_results.json")) as fh:
            x3 = Frac(json.load(fh)["X"]["1,1"]["tau3"])
    except Exception:
        pass
    for s in (Frac(11, 20), Frac(3, 5), Frac(13, 20), Frac(7, 10),
              Frac(3, 4), Frac(4, 5)):
        row = x11_window(s)
        tau = -math.log(float(s))
        flat = 6 * tau * tau + (float(x3) * tau ** 3
                                if x3 is not None else 0.0)
        row["tau"] = tau
        row["flat_target_tau3"] = flat
        res["rows"].append(row)
        if "X11_lo" in row:
            inside = (row["X11_lo"] <= flat <= row["X11_hi"])
            print(f"  s={s}: X11 in [{row['X11_lo']:+.6f}, "
                  f"{row['X11_hi']:+.6f}]  flat(2/3-exact+tau^3) "
                  f"{flat:+.6f} {'IN' if inside else 'OUT'}  "
                  f"X11>0 certified: {row['ratio_gt_1_certified']}")
        else:
            print(f"  s={s}: window not positive "
                  f"(tail T00 ~ {row['tail']['0,0']:.3e})")
    with open(OUT_JSON, "w") as fh:
        json.dump(res, fh, indent=1)
    print(f"\nledger written to {OUT_JSON}  [{time.time() - t0:.0f}s]")


if __name__ == "__main__":
    main()
