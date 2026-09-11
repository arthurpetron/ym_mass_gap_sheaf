"""Polynomial Brown pipeline: block decomposition + torsor-shift lemma.

Lemma (used): for nondegenerate B, lifts act by beta -> beta - q(v);
achievable set = beta0 - spectrum(q).  Base lift: q(b_i) = q2(b_i).
"""
import sys, random, time, cmath
sys.path.insert(0, '/home/claude/ym_dig')
sys.setrecursionlimit(100000)
from scratch.brown_invariant import h1_and_forms, kap, admissible_triple, completes
from computations.kappa_system import decomposable
from collections import defaultdict, Counter

def brown_block(qmat_q, Bm):
    """(q values on basis, B matrix) -> (beta0 or None, spectrum flags).
    Returns Brown of the base form via symplectic reduction, and whether
    q attains values {0,1,2,3} (for achievable set)."""
    import copy
    n = len(qmat_q)
    basis = [1 << i for i in range(n)]   # vectors as bitmasks over current basis
    q = dict((1 << i, qmat_q[i] % 4) for i in range(n))
    B = dict()
    for i in range(n):
        for j in range(n):
            B[(1 << i, 1 << j)] = Bm[i][j]
    def q_of(x, qb, Bb, gens):
        val = 0
        xs = [g for g in gens if x & g]
        for g in xs:
            val += qb[g]
        for a in range(len(xs)):
            for b in range(a+1, len(xs)):
                val += 2 * Bb[(xs[a], xs[b])]
        return val % 4
    # work with explicit small structure: reduce by 2-blocks
    gens = list(basis)
    qb = dict(q)
    Bb = dict(B)
    G_phase = 0.0
    G_scale = 1.0
    while gens:
        x = None; y = None
        for i in range(len(gens)):
            for j in range(len(gens)):
                if i != j and Bb[(gens[i], gens[j])] == 1:
                    x, y = gens[i], gens[j]
                    break
            if x is not None: break
        if x is None:
            # radical: B=0 on remaining; Gauss sum = prod over gens of (1 + i^{q})
            for g in gens:
                term = 1 + 1j**qb[g]
                if abs(term) < 1e-12:
                    return None, None   # degenerate (q=2 on radical): Gauss sum 0
                G_scale *= abs(term)
                G_phase += cmath.phase(term)
            break
        # 2-block Gauss factor
        blockG = 1 + 1j**qb[x] + 1j**qb[y] + 1j**((qb[x]+qb[y]+2) % 4)
        if abs(blockG) < 1e-12:
            return None, None
        G_scale *= abs(blockG)
        G_phase += cmath.phase(blockG)
        # complement: z -> z + B(z,y)x + B(z,x)y
        newgens = []
        for z in gens:
            if z in (x, y): continue
            w = z
            if Bb[(z, y)]: w ^= x
            if Bb[(z, x)]: w ^= y
            newgens.append((z, w))
        # recompute q, B on new generators (expressed via old combination)
        nq = {}
        nB = {}
        reps = {}
        for z, w in newgens:
            reps[z] = w
        # evaluate q(w), B(w,w') from original bilinear data
        def q_orig(mask):
            xs = [1 << i for i in range(n) if mask & (1 << i)]
            val = 0
            for g in xs: val += qmat_q[[1 << i for i in range(n)].index(g)]
            for a in range(len(xs)):
                for b_ in range(a+1, len(xs)):
                    ia = xs[a].bit_length()-1; ib = xs[b_].bit_length()-1
                    val += 2*Bm[ia][ib]
            return val % 4
        def B_orig(m1, m2):
            tot = 0
            for i in range(n):
                if not (m1 >> i) & 1: continue
                for j in range(n):
                    if (m2 >> j) & 1:
                        tot ^= Bm[i][j]
            return tot
        gens2 = [w for _z, w in newgens]
        # dedupe zero vectors
        gens2 = [g for g in gens2 if g != 0]
        # rebuild dicts
        qb = {g: q_orig(g) for g in gens2}
        Bb = {(g1, g2): B_orig(g1, g2) for g1 in gens2 for g2 in gens2}
        # check independence loosely (skip degenerate collapse)
        gens = gens2
    beta0 = round((G_phase / (2*cmath.pi)) * 8) % 8
    return beta0, None

def spectrum(qmat_q, Bm, samples=4096):
    n = len(qmat_q)
    vals = set()
    rnd = random.Random(5)
    for _ in range(min(samples, 1 << n)):
        x = rnd.getrandbits(n)
        v = 0
        xs = [i for i in range(n) if (x >> i) & 1]
        for i in xs: v += qmat_q[i]
        for a in range(len(xs)):
            for b in range(a+1, len(xs)):
                v += 2*Bm[xs[a]][xs[b]]
        vals.add(v % 4)
        if len(vals) == 4: break
    return vals

# ---- run over sample ----
from computations.vertex_amplitude import sixj_sign_square, vertex_labels, VERTS
from computations.hypercube4d_survey import hypercube
cx, faces, meta = hypercube()

configs = []
spins = [0]*24
def dfs(fi):
    if fi == 24:
        k = kap(spins)
        if k is not None and not decomposable(spins):
            configs.append((tuple(spins), k))
        return
    for v in (0, 1, 2):
        spins[fi] = v
        if all(admissible_triple(*(spins[x] for x in fs)) for _e, fs in completes[fi]):
            dfs(fi+1)
    spins[fi] = 0
dfs(0)
random.seed(17)
neg = [c for c in configs if c[1] == 1]
pos = [c for c in configs if c[1] == 0]
sample = random.sample(neg, 150) + random.sample(pos, 150)

b1s = Counter()
stats = Counter()
selfcheck_fail = 0
beta_by_kappa = defaultdict(Counter)
t0 = time.time()
for sp, k in sample:
    try:
        data = h1_and_forms(list(sp))
    except Exception:
        stats['build_error'] += 1; continue
    if data is None:
        stats['build_none'] += 1; continue
    n = data['b1']; b1s[n] += 1
    basis, walks, q2f, Bf = data['basis'], data['walks'], data['q2'], data['B']
    Bm = [[0]*n for _ in range(n)]
    unknown = 0
    for i in range(n):
        Bm[i][i] = q2f(basis[i])
    for i in range(n):
        for j in range(i+1, n):
            v = Bf(walks[i], walks[j])
            if v is None:
                unknown += 1; v = 0
            Bm[i][j] = Bm[j][i] = v
    if unknown:
        stats['B_unknown_pairs'] += 1
        continue
    qv = [q2f(b) for b in basis]
    # self-check: B(x,x) == q2(x) baked in by construction
    try:
        beta0, _ = brown_block(qv, Bm)
    except Exception:
        stats['brown_error'] += 1; continue
    if beta0 is None:
        stats['gauss_zero'] += 1
        continue
    spec = spectrum(qv, Bm)
    achievable = {(beta0 - t) % 8 for t in spec}
    target = 4 if k == 1 else 0
    stats['analyzed'] += 1
    stats[f'{"OK" if target in achievable else "FAIL"}_k{k}'] += 1
    beta_by_kappa[k][beta0] += 1
print(f"[{time.time()-t0:.0f}s] b1 distribution: {dict(sorted(b1s.items()))}", flush=True)
print(f"stats: {dict(stats)}", flush=True)
print("base-lift beta0 census by kappa:", flush=True)
for k in (0, 1):
    print(f"  kappa={k}: {dict(sorted(beta_by_kappa[k].items()))}", flush=True)
