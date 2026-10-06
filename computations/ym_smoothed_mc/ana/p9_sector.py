"""P9 item 1: P7 (beta 2.95, 48^3x48, side 8) split by the sign of the direction-3 smeared spatial Polyakov loop,
plus a sector-symmetrized estimator (equal weight to both sectors). usage: p9_sector.py <rundir> <out.md>"""
import sys, os, json, numpy as np
sys.path.insert(0, os.path.dirname(__file__)); from load import load, load_poly
rundir, outp = sys.argv[1], sys.argv[2]; path = f'{rundir}/data.bin'
h, plaq, Es, O = load(path); P = load_poly(path); N = len(plaq); sides = h['sides']; s = sides[len(sides)//2]; j = sides.index(s)
Lt = h['Lt']; nq = Lt//2; h2 = s//2; tfl = h['tflow']; rhos = [np.sqrt(6*t)/s for t in tfl]; k1 = int(np.argmin([abs(r-1) for r in rhos]))
B = 10
sgn = np.sign(P[:, k1, 2]); pmax = np.abs(P[:, k1, :3]).max(1)
seg = np.concatenate([[0], np.cumsum(np.diff(sgn) != 0)])
ref = json.load(open(os.path.join(os.path.dirname(__file__), '..', 'runs', 'p6', 'b2.95_s8.json')))
def perconf(X): return X.mean(1), np.stack([(X*np.roll(X, -n, axis=1)).mean(1) for n in range(nq+1)], 1)
def fm(v, e):
    if not (np.isfinite(v) and np.isfinite(e)): return 'n/a'
    d = min(4, max(1, int(np.ceil(-np.log10(max(e, 1e-9))))+1)); return f"{v:.{d}f}({int(round(e*10**d))})"
def analyze_level_chrono(k, labels, Bc=5):
    """members of each label concatenated chronologically and binned by Bc (bins may straddle gaps)."""
    M, Q = perconf(O[:, k, j].mean(1)); out = []
    for G in np.unique(labels):
        idx = np.where(labels == G)[0]; n = len(idx) - len(idx) % Bc
        for i in range(0, n, Bc): out.append((G, M[idx[i:i+Bc]].mean(), Q[idx[i:i+Bc]].mean(0)))
    return np.array([x[0] for x in out]), np.array([x[1] for x in out]), np.array([x[2] for x in out])
def analyze_level(k, labels):
    """labels: per-meas group id (bins never straddle a change of label or segment). Returns dict group->(Mb,Qb) bins."""
    M, Q = perconf(O[:, k, j].mean(1))
    bins = []  # (group, Mbin, Qbin)
    cut = np.concatenate([[0], np.where((np.diff(labels) != 0) | (np.diff(seg) != 0))[0]+1, [N]])
    for a, b in zip(cut[:-1], cut[1:]):
        for i in range(a, b - (b-a) % B, B): bins.append((labels[a], M[i:i+B].mean(), Q[i:i+B].mean(0)))
    g = np.array([x[0] for x in bins]); Mb = np.array([x[1] for x in bins]); Qb = np.array([x[2] for x in bins]); return g, Mb, Qb
def derived(q, m, mode):
    if mode == 'E1': c = q - m*m; return np.array([c[s+1]/c[h2], (1-c[1]/c[0])*s, c[s]/c[0]])
    if mode == 'E3f': c = q - q[nq]; return np.array([c[s+1]/c[h2], (1-c[1]/c[0])*s, c[s]/c[0]])
    d = q[:-1] - q[1:]; return np.array([d[s+1]/d[h2], (1-d[1]/d[0])*s, np.nan])
def est(g, Mb, Qb, groups, mode, sym):
    def f(mask):
        if sym:  # equal weight per group
            qs = [Qb[mask & (g == G)].mean(0) for G in groups]; ms = [Mb[mask & (g == G)].mean() for G in groups]
            return derived(np.mean(qs, 0), np.mean(ms), mode)
        mm = mask & np.isin(g, groups); return derived(Qb[mm].mean(0), Mb[mm].mean(), mode)
    nb = len(g); full = f(np.ones(nb, bool)); js = np.array([f(np.arange(nb) != i) for i in range(nb)])
    return full, np.sqrt((nb-1)/nb*((js - js.mean(0))**2).sum(0))
L = [f"# P9 addendum to P7_FINAL: Polyakov-sector split (beta 2.95, 48^3x48, side 8)\n",
     f"Sector = sign of the direction-3 smeared spatial Polyakov loop at rho={rhos[k1]:.2f} (P7 logs it per measurement; rho=1.5 has the same sign history). "
     f"N={N}: P3<0 in {(sgn<0).sum()} meas, P3>0 in {(sgn>0).sum()} meas; {int(seg[-1])} sign changes; contiguous segments of length {np.bincount(seg).tolist()}. "
     f"Bins of {B} meas inside each contiguous segment (remainders dropped), jackknife over bins. E1 = vacuum subtraction with the subset mean; "
     "E3f = far-lag Q(n)-Q(Lt/2); E3d = differenced. 'sym' = sector-symmetrized: Q and <O> averaged with EQUAL weight over the two sectors "
     "(what an ergodic run would give, since the center transformation maps one sector onto the other and leaves contractible loops invariant).\n",
     "**Caveat:** the dir-3 sector flipped only 4 times, so each sector is ~2-3 independent stretches; the sector errors and the sector difference are themselves only "
     "roughly estimated (bins inside a stretch are correlated through the slow mode).\n"]
groups_sets = [('all (P7_FINAL, bin 10)', [-1, 1], False), ('P3 < 0', [-1], False)]
for k in range(len(tfl)):
    if not (0.7 < rhos[k] < 1.3): continue
    key = f"{rhos[k]:.2f}"; rf = ref['levels'].get(key, {}).get('est')
    g, Mb, Qb = analyze_level(k, sgn)
    L.append(f"\n## rho = {key}  (Ls=32 reference: W E1 {fm(rf['E1_stream'][0][0], rf['E1_stream'][1][0])}, E3f {fm(rf['E3_farlag'][0][0], rf['E3_farlag'][1][0])}, E3d {fm(rf['E3_diff'][0][0], rf['E3_diff'][1][0])}, eps*s {fm(rf['E1_stream'][0][2], rf['E1_stream'][1][2])})\n")
    L.append("| subset | bins | W E1 | W E3f | W E3d | eps*s E1 | eps*s E3f | eps*s E3d | R(s)/R(0) E1 | <O> |"); L.append("|---|---|---|---|---|---|---|---|---|---|")
    for lab, G, sym in groups_sets:
        r1 = est(g, Mb, Qb, G, 'E1', sym); rf_ = est(g, Mb, Qb, G, 'E3f', sym); rd = est(g, Mb, Qb, G, 'E3d', sym)
        nbk = int(np.isin(g, G).sum()); om = np.mean([Mb[g == x].mean() for x in G]) if sym else Mb[np.isin(g, G)].mean()
        L.append(f"| {lab} | {nbk} | {fm(r1[0][0], r1[1][0])} | {fm(rf_[0][0], rf_[1][0])} | {fm(rd[0][0], rd[1][0])} | {fm(r1[0][1], r1[1][1])} | {fm(rf_[0][1], rf_[1][1])} | {fm(rd[0][1], rd[1][1])} | {fm(r1[0][2], r1[1][2])} | {om:.5f} |")
    # sector difference with errors (independent bins in different sectors)
    L.append("")
    # stretch split: the two long negative stretches (seg 0 and seg 2) as independent "streams"
    for G in ([0], [2], [4]):
        lab = np.where(np.isin(seg, G), 1, 0); gS, MS, QS = analyze_level(k, lab); r = est(gS, MS, QS, [1], 'E1', False); rd = est(gS, MS, QS, [1], 'E3d', False)
        L.append(f"Stretch {G[0]} only (meas {np.where(seg==G[0])[0][0]}-{np.where(seg==G[0])[0][-1]}, {int((gS==1).sum())} bins): W E1 {fm(r[0][0], r[1][0])}, W E3d {fm(rd[0][0], rd[1][0])}, eps*s {fm(r[0][1], r[1][1])}")
    # magnitude split: terciles of |P3| (the ordered direction) and of max_d|P_d|; members binned chronologically by 5
    for nm, val in [('|P3|', np.abs(P[:, k1, 2])), ('max_d|P_d|', pmax)]:
        q = np.quantile(val, [1/3, 2/3]); lab = np.digitize(val, q); gM, MM, QM = analyze_level_chrono(k, lab)
        cells = []
        for G in range(3):
            r = est(gM, MM, QM, [G], 'E1', False); cells.append(f"{['low','mid','high'][G]} ({val[lab==G].mean():.3f}): W {fm(r[0][0], r[1][0])}, eps*s {fm(r[0][1], r[1][1])}, <O> {MM[gM==G].mean():.5f}")
        L.append(f"Tercile split by {nm} (bins of 5 members, chronological): " + " | ".join(cells))
open(outp, 'w').write('\n'.join(L) + '\n'); print('\n'.join(L))
