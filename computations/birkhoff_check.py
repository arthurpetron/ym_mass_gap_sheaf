"""Check the imagination: is the wheel (channel-mixing) kernel a strict
Birkhoff contraction with cutoff-saturating projective diameter?"""
import sys, math
sys.path.insert(0, '/home/claude/ym_dig')
from fractions import Fraction
from computations.dual_positivity_survival import wheel_value
from computations.exact_haar_network import casimir4, dim

def K_entry(j, m, s):
    """uniform-spoke j (even), uniform-rim m kernel with heat-kernel weights"""
    w = wheel_value((j,)*4, (m,)*4)
    if not w:
        return Fraction(0)
    return w[0] * (Fraction(dim(j)) * s**casimir4(j))**4

def hilbert_diameter(K, rows, cols):
    """max over column pairs of Hilbert metric distance between columns."""
    worst = Fraction(1)
    for a in range(len(cols)):
        for b in range(a+1, len(cols)):
            # osc = max_m K[m][a]/K[m][b] * max_m K[m][b]/K[m][a]
            r1 = max((K[m][a] / K[m][b] for m in range(len(rows))))
            r2 = max((K[m][b] / K[m][a] for m in range(len(rows))))
            osc = r1 * r2
            if osc > worst:
                worst = osc
    return worst   # exp(diameter)

s = Fraction(1, 2)
print(f"s = {s}; uniform sector (even spokes)")
for M in (2, 3, 4, 5):
    js = [j for j in range(0, M+1, 2)]
    ms = list(range(0, M+1))
    K = [[K_entry(j, m, s) for j in js] for m in ms]
    # check strict positivity
    zeros = sum(1 for row in K for v in row if v == 0)
    if zeros:
        # drop zero rows (rim channels not reachable)
        keep = [i for i, row in enumerate(K) if all(v > 0 for v in row)]
        K = [K[i] for i in keep]
        ms_k = [ms[i] for i in keep]
    else:
        ms_k = ms
    if len(K) < 2:
        print(f"  cutoff {M}: sector too small after zero-row removal")
        continue
    osc = hilbert_diameter(K, ms_k, js)
    Delta = math.log(float(osc))
    q = math.tanh(Delta / 4)
    print(f"  cutoff {M}: spokes {js}, rims kept {ms_k}: "
          f"Delta = {Delta:.4f}, Birkhoff q = tanh(D/4) = {q:.6f}")
# also s-dependence at largest cutoff
print("s-dependence (cutoff 4):")
for sv in (Fraction(1,4), Fraction(1,2), Fraction(3,4), Fraction(9,10)):
    js = [0, 2, 4]; ms = list(range(5))
    K = [[K_entry(j, m, sv) for j in js] for m in ms]
    keep = [i for i, row in enumerate(K) if all(v > 0 for v in row)]
    K = [K[i] for i in keep]
    if len(K) < 2: continue
    osc = hilbert_diameter(K, keep, js)
    Delta = math.log(float(osc))
    print(f"  s={sv}: Delta = {Delta:.4f}, q = {math.tanh(Delta/4):.6f}")
