"""DP.2 measurements from a saved kernel JSON."""
import json
import math
import sys
from fractions import Fraction as Fr

sys.path.insert(0, "/home/claude/ym_dig")
from computations.exact_haar_network import casimir4, dim, sign_on_unit_interval, sp_str  # noqa: E402

D = json.load(open(sys.argv[1]))
N, M = D["N"], D["M"]
T = {}
for k, poly in D["T"].items():
    n, m = map(int, k.split(","))
    e = {int(p): Fr(a, b) for p, (a, b) in poly.items()}
    T[(n, m)] = e
    T[(m, n)] = e
print(f"kernel N={N} M={M}; unreached: {D.get('unreached') or 'none'}")


def ev(e, s):
    return sum(c * s**p for p, c in e.items())


print("== entries ==")
for n in range(N + 1):
    for m in range(n, N + 1):
        e = T[(n, m)]
        v = sign_on_unit_interval(e) if e else "zero"
        print(f"T[{n},{m}]: {len(e)} terms; sign(0,1): {v}; {sp_str(e) if e and len(e) <= 6 else ''}")

# usable sector: strictly positive rows/cols
for sv in (Fr(1, 4), Fr(1, 2), Fr(3, 4)):
    cand = [n for n in range(N + 1) if T[(n, n)]]
    idx = [n for n in cand
           if all(ev(T[(n, m)], sv) > 0 for m in cand)]
    print(f"s={sv}: strictly positive sector {idx}")
    if len(idx) < 2:
        continue
    # Birkhoff diameter over columns restricted to sector
    worst = Fr(1)
    for a in range(len(idx)):
        for b in range(a + 1, len(idx)):
            ca = [ev(T[(n, idx[a])], sv) for n in idx]
            cb = [ev(T[(n, idx[b])], sv) for n in idx]
            r1 = max(x / y for x, y in zip(ca, cb))
            r2 = max(y / x for x, y in zip(ca, cb))
            worst = max(worst, r1 * r2)
    Delta = math.log(float(worst))
    print(f"   Birkhoff: Delta = {Delta:.4f}, q = tanh(D/4) = {math.tanh(Delta/4):.6f}")
    # flow: v = T e_s on the sector
    vv = {}
    for n in idx:
        acc = Fr(0)
        for m in idx:
            acc += ev(T[(n, m)], sv) * Fr(dim(m)) * sv ** casimir4(m)
        vv[n] = acc
    xs = [casimir4(n) for n in vv]
    ys = [math.log(float(v / dim(n))) for n, v in vv.items()]
    k = len(xs)
    xb, yb = sum(xs) / k, sum(ys) / k
    den = sum((x - xb) ** 2 for x in xs)
    if den == 0:
        continue
    slope = sum((x - xb) * (y - yb) for x, y in zip(xs, ys)) / den
    resid = [y - (yb + slope * (x - xb)) for x, y in zip(xs, ys)]
    width = max(resid) - min(resid)
    print(f"   flow: fitted s' = {math.exp(slope):.6f}  (s^4 = {float(sv)**4:.6f})  "
          f"corridor log-width = {width:.6f}")
