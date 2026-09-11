"""Build the enveloped cone and measure its two defining clauses."""
import sys, math
sys.path.insert(0, '/home/claude/ym_dig')
from fractions import Fraction
from computations.dual_positivity_survival import wheel_value
from computations.exact_haar_network import casimir4, dim

def build_kernel(M, s):
    js = [j for j in range(0, M+1, 2)]
    ms = list(range(0, M+1))
    K = {}
    for m in ms:
        for j in js:
            w = wheel_value((j,)*4, (m,)*4)
            if w:
                K[(m, j)] = w[0] * (Fraction(dim(j)) * s**casimir4(j))**4
    rows = sorted({m for (m, j) in K})
    rows = [m for m in rows if all((m, j) in K for j in js)]  # strictly positive rows
    return K, rows, js

def envelope(n, s):
    return Fraction(dim(n)) * s**casimir4(n)

def hdist(u, v):
    r1 = max(Fraction(a, 1)/Fraction(b, 1) if isinstance(a, int) else a/b for a, b in zip(u, v))
    r2 = max(b/a for a, b in zip(u, v))
    return math.log(float(r1 * r2))

s = Fraction(1, 2)
print("CLAUSE 1 — envelope invariance: corridor width of T(envelope), by cutoff")
for M in (2, 3, 4, 5, 6):
    K, rows, js = build_kernel(M, s)
    if len(rows) < 2: continue
    vhat = []
    for m in rows:
        v = sum(K[(m, j)] * envelope(j, s) for j in js)
        vhat.append(v / envelope(m, s))
    ratio = max(vhat) / min(vhat)
    print(f"  cutoff {M}: reachable rims {rows}, corridor width log = {math.log(float(ratio)):.4f}")

print("CLAUSE 2 — uniform contraction: Hilbert distance of iterates from corridor extremes")
for M in (3, 4, 5, 6):
    K, rows, js = build_kernel(M, s)
    if len(rows) < 2: continue
    # two extreme corridor inputs: envelope tilted up/down by factor 3 at the ends
    e = [envelope(j, s) for j in js]
    u = [e[i] * (3 if i == 0 else 1) for i in range(len(js))]
    w = [e[i] * (3 if i == len(js)-1 else 1) for i in range(len(js))]
    # one application (rims then re-embed onto even spins by index map: use rims∩spokes)
    common = [m for m in rows if m in js]
    if len(common) < 2:
        print(f"  cutoff {M}: no closed sector"); continue
    def apply(vec):
        out = []
        for m in common:
            out.append(sum(K[(m, j)] * vec[ji] for ji, j in enumerate(js)))
        return out
    d0 = hdist([u[js.index(m)] for m in common], [w[js.index(m)] for m in common])
    u1, w1 = apply(u), apply(w)
    d1 = hdist(u1, w1)
    # second iterate within the closed sector
    def apply2(vec_common):
        full = []
        for j in js:
            full.append(vec_common[common.index(j)] if j in common else Fraction(0))
        # replace zeros by envelope (outside sector) to stay in cone
        full = [v if v > 0 else envelope(js[i], s) for i, v in enumerate(full)]
        return apply(full)
    u2, w2 = apply2(u1), apply2(w1)
    d2 = hdist(u2, w2)
    print(f"  cutoff {M}: d0={d0:.4f} -> d1={d1:.4f} -> d2={d2:.4f}; "
          f"per-step q ≈ {d1/d0:.4f}, {d2/d1 if d1>1e-12 else 0:.4f}")
