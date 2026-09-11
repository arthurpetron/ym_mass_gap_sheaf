"""Fit the renormalized coupling s' and measure the flowed corridor."""
import sys, math
sys.path.insert(0, '/home/claude/ym_dig')
from fractions import Fraction
from computations.dual_positivity_survival import wheel_value
from computations.exact_haar_network import casimir4, dim

s = Fraction(1, 2)
for M in (2, 3, 4, 5):
    js = [j for j in range(0, M+1, 2)]
    ms = list(range(0, M+1))
    rows = []
    for m in ms:
        v = Fraction(0)
        ok = True
        for j in js:
            w = wheel_value((j,)*4, (m,)*4)
            if w:
                v += w[0] * (Fraction(dim(j)) * s**casimir4(j))**4
        if v > 0:
            rows.append((m, v))
    if len(rows) < 2:
        continue
    # fit: log(v_m / d_m) = a + (log s') * C4(m)   [least squares]
    xs = [casimir4(m) for m, _v in rows]
    ys = [math.log(float(v / dim(m))) for m, v in rows]
    n = len(xs)
    xb = sum(xs)/n; yb = sum(ys)/n
    slope = sum((x-xb)*(y-yb) for x, y in zip(xs, ys)) / sum((x-xb)**2 for x in xs)
    sp = math.exp(slope)
    # corridor width against flowed envelope
    resid = [y - (yb + slope*(x - xb)) for x, y in zip(xs, ys)]
    width = max(resid) - min(resid)
    print(f"cutoff {M}: rims {[m for m,_ in rows]}  fitted s' = {sp:.5f} "
          f"(s^4 = {float(s)**4:.5f})  flowed-corridor log-width = {width:.4f}")
