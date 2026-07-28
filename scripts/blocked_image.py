"""DP.3-(i) vs (i') at the AGGREGATED level: the blocked image (Bv)_n.

The blocking map applied to the heat-kernel envelope v_m = d_m s^{C(m)}:

    (Bv)_n (s) = sum_m T[n,m](s) * d_m * s^{C(m)} .

Two questions, deliberately separated:

  (i)  coefficientwise  — is (Bv)_n a polynomial with nonnegative
       coefficients?  This is preservation of the cone C_exp as defined
       in docs/dp3-exponent-cone-statement.md.
  (i') functional       — is (Bv)_n positive as a FUNCTION on (0,1)?
       This is the property DP.2's Birkhoff/Hilbert measurements
       actually consume.

Each entry T[n,m] is exact only below its own window D_{n,m}; the
product T[n,m] * d_m s^{C(m)} is therefore exact below D_{n,m} + C(m),
and the sum is exact below the minimum of those.  Verdicts are reported
inside that final window (rigorous) and for the full computed
polynomial (provisional).
"""
from __future__ import annotations

import glob
import json
import sys
from fractions import Fraction

sys.path.insert(0, "/home/claude/dp3m2")

from computations.exact_haar_network import (          # noqa: E402
    casimir4, dim, sign_on_unit_interval, sp_str,
)

Frac = Fraction


def load():
    T, D = {}, {}
    for f in sorted(glob.glob("/home/claude/dp3m2/fx_[A-Z]*.json")):
        for key, rec in json.load(open(f)).items():
            n, m = map(int, key.split(","))
            poly = {int(p): Frac(a, b) for p, (a, b) in rec["poly"].items()}
            win = rec["exact_below_E"]
            for k in ((n, m), (m, n)):
                if k not in T or (win or 10 ** 9) > (D.get(k) or 0):
                    T[k], D[k] = poly, win
    return T, D


def main():
    T, D = load()
    have = sorted(T)
    print("entries available:", sorted({tuple(sorted(k)) for k in have}))
    print()
    for n in (0, 1, 2):
        need = [(n, m) for m in (0, 1, 2)]
        if any(k not in T for k in need):
            missing = [k for k in need if k not in T]
            print(f"(Bv)_{n}: missing {missing} — skipped\n")
            continue
        out, windows = {}, []
        for m in (0, 1, 2):
            shift = casimir4(m)
            coef = Frac(dim(m))
            for e, c in T[(n, m)].items():
                out[e + shift] = out.get(e + shift, Frac(0)) + coef * c
            if D[(n, m)] is not None:
                windows.append(D[(n, m)] + shift)
        out = {k: v for k, v in out.items() if v}
        W = min(windows) if windows else None
        fin = {k: v for k, v in out.items() if W is None or k < W}
        negs_full = sorted((e, c) for e, c in out.items() if c < 0)
        negs_fin = sorted((e, c) for e, c in fin.items() if c < 0)
        print(f"(Bv)_{n}:  FINAL below E = {W}")
        print(f"   final part: {sp_str(fin) if fin else 0}")
        print(f"   (i)  coefficientwise nonneg on the FINAL part: "
              f"{'NO -> ' + str(negs_fin[:3]) if negs_fin else 'YES'}")
        print(f"   (i') Sturm sign of the final part on (0,1): "
              f"{sign_on_unit_interval(fin) if fin else 'zero'}")
        print(f"   full computed polynomial: {len(out)} terms; "
              f"negative coefficients: "
              f"{[(e, str(c)) for e, c in negs_full[:4]] or 'none'} "
              f"(provisional above E = {W})")
        print()


if __name__ == "__main__":
    main()
