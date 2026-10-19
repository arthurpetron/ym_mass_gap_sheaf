#!/usr/bin/env python3
"""Steps 3 and 4 of the 2026-10-18 evening follow-up.
Step 3: continuum extrapolation of the pair shifts with forms from asymptotic-freedom theory of cutoff effects
        (Husung-Marquard-Sommer, arXiv:1912.08498): Delta(a) ~ a^2 [gbar^2(1/a)]^Gamma, Gamma = n_hat + gamma_hat_i, with n_hat = 1
        because the tree-level (order g^2) a^2 effect of g^2_GF is removed by the exact lattice normalisation N_lat(c,L), gamma_hat_1 = 7/11,
        gamma_hat_2 = 63/55 (pure gauge, one-loop anomalous dimensions).  Forms: s(L) = s_c + A L^-2 [gbar^2(1/a_L)]^Gamma (+ B L^-4).
Step 4: non-parametric bootstrap over CONFIGURATIONS: each chain is resampled in moving blocks (same indices for c=0.3 and c=0.4, i.e. shared
        configurations) and the whole pipeline (pair shifts, beta-interpolation for the old u values, continuum extrapolation, slope fit) is re-run
        per replica; replicas give the covariance between the two schemes (and between pairs sharing an ensemble).
Pairs used: finest three, 6->12, 8->16, 12->24 (4->8 not used).  s0 = 2 b0 ln 2 fixed.  MC evidence only.
usage: step34.py OUTPREFIX [NBOOT] [pdg|nominal] [dirs-comma]
'pdg': deviations of every replica ensemble mean from the central mean are multiplied by sqrt(max(1, chi2/dof of the chain means)) per (L,beta,c) group with >= 3 chains
(chain-to-chain overdispersion that the within-chain bootstrap cannot see)."""
import sys, os, glob, json, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gfana import load_run, time_index, N_lat, gamma_method
from stepscale import fit_inv, inv_model, solve_beta, S0
R = '/Users/darthur/ym_numerics_runs'
DIRS = [R + '/prod', R + '/prod2', R + '/prod3', R + '/prod4']
EXC = ('_cold', '_tau', '.alt', '.zeu', 'bad_')
b0 = 11 / (24 * np.pi ** 2); b1 = 136 / 3 / (16 * np.pi ** 2) ** 2; K1_2L = 0.0026
GH1, GH2 = 7 / 11, 63 / 55
CS = (0.3, 0.4)
NEW = {1.0: (5.63, 5.74, 5.89), 1.9: (3.77, 3.88, 4.02), 2.9: (3.08, 3.19, 3.34)}
OLD = {1.54: 4.5, 2.41: 3.6}
UN = sorted(set(NEW) | set(OLD)); LS = (6, 8, 12)

def two(u, n=2000):
    x = 1 / u; h = np.log(2) / n
    for _ in range(n): x -= h * (2 * b0 + 2 * b1 / x)
    return 1 / u - x
def dtwo(u): return (two(u * 1.001) - two(u / 1.001)) / (u * 0.002)
def gbar2_at_lattice(u, N, n=400):
    """two-loop coupling at mu = 1/a = N/L_phys given gbar^2(1/L_phys) = u (N = lattice size): integrate d(1/g^2)/dln mu = 2 b0 + 2 b1 g^2"""
    x = 1 / u; h = np.log(N) / n
    for _ in range(n): x += h * (2 * b0 + 2 * b1 / x)
    return 1 / x

def load_all(dirs):
    E = {}
    for dr in dirs:
        for f in sorted(glob.glob(os.path.join(dr, 'su2_L*_b*.csv'))):
            n = os.path.basename(f)
            if any(x in n for x in EXC): continue
            try: r = load_run(f, 3)
            except Exception: continue
            if len(r['sweep']) < 20: continue
            try: idx = [time_index(r, c) for c in CS]
            except AssertionError: continue
            X = np.column_stack([r['times'][i] ** 2 * r['E'][:, i, 0] / N_lat(c, r['L']) for c, i in zip(CS, idx)])
            E.setdefault((r['L'], round(r['beta'], 6)), []).append(X)
    return E

def ens_mean(chains, idxs=None):
    if idxs is None: tot = np.vstack(chains)
    else: tot = np.vstack([c[i] for c, i in zip(chains, idxs)])
    return tot.mean(0)

def resample_idx(chains, rng, B=3):
    out = []
    for c in chains:
        n = len(c); k = int(np.ceil(n / B)); st = rng.integers(0, n - B + 1, size=k)
        out.append((st[:, None] + np.arange(B)[None, :]).ravel()[:n])
    return out

def shifts(M, ERR, u12c, ic):
    """pair shifts s[un][L] (scheme index ic) from ensemble means M[(L,b)] (array of 2); old-u 6->12, 8->16 by beta-interpolation (M=2)."""
    out = {}
    for un in UN:
        d = {}
        if un in NEW:
            for L, b in zip(LS, NEW[un]):
                u = M[(L, b)][ic]; sg = M[(2 * L, b)][ic]; d[L] = 1 / u - 1 / sg + dtwo(u) * (u12c[un] - u)
        else:
            u = M[(12, OLD[un])][ic]; sg = M[(24, OLD[un])][ic]; d[12] = 1 / u - 1 / sg + dtwo(u) * (u12c[un] - u)
            for L in (6, 8):
                bs = sorted(b for (l, b) in M if l == L and (2 * L, b) in M)
                g1 = np.array([M[(L, b)][ic] for b in bs]); g2 = np.array([M[(2 * L, b)][ic] for b in bs])
                e1 = np.array([ERR[(L, b)][ic] for b in bs]); e2 = np.array([ERR[(2 * L, b)][ic] for b in bs])
                try:
                    c1 = fit_inv(bs, g1, e1, 2); c2 = fit_inv(bs, g2, e2, 2)
                    bstar = solve_beta(c1, u12c[un], min(bs) - 1e-9, max(bs) + 1e-9)
                    d[L] = 1 / u12c[un] - inv_model(c2, bstar)   # s = 1/u - 1/Sigma, 1/Sigma = inv_model(c2, beta*)
                except Exception:
                    d[L] = np.nan
        out[un] = d
    return out

# ---- continuum forms: columns for each pair (L = smaller lattice); 'u' = nominal coupling at the scale of the pair
def basis(form, L, u):
    x = 1.0 / L ** 2
    if form == 'lin': return [1.0, x]
    if form == 'quad': return [1.0, x, x * x]
    if form.startswith('T'):                        # T<Gamma>: a^2 [gbar^2(1/a_L)]^Gamma
        G = float(form[1:]); g2 = gbar2_at_lattice(u, L)
        return [1.0, x * g2 ** G]
    if form.startswith('Q'):                        # Q<Gamma>: theory form + a^4 term
        G = float(form[1:]); g2 = gbar2_at_lattice(u, L)
        return [1.0, x * g2 ** G, x * x]
    if form == 'const': return [1.0]
    raise ValueError(form)
FORMS = ['lin', 'quad', 'T0.636', 'T1', 'T1.636', 'T2.145', 'Q1.636', 'const']
PRIMARY = 'T1.636'

def cont_weights(form, un, uc, e):
    """WLS estimator weights (row of (A^T W A)^-1 A^T W) for the continuum value and chi2 machinery"""
    A = np.array([basis(form, L, uc) for L in LS]); W = np.diag(1 / np.asarray(e) ** 2)
    C = np.linalg.inv(A.T @ W @ A); return (C @ A.T @ W)[0], A, W

def build_replica(E, rng, ERR, B=3, central=False, SF=None, M0=None):
    ch = {k: v for k, v in E.items()}
    idxs = {k: (None if central else resample_idx(v, rng, B)) for k, v in ch.items()}
    M = {k: ens_mean(v, idxs[k]) for k, v in ch.items()}
    if SF and M0:
        for k in M:
            if k in SF: M[k] = M0[k] + SF[k] * (M[k] - M0[k])
    return M

def chain_sf(E):
    SF = {}
    for k, chains in E.items():
        if len(chains) < 3: continue
        sf = np.ones(2)
        for i in range(2):
            ms = np.array([c[:, i].mean() for c in chains]); es = np.array([gamma_method(c[:, i])[1] for c in chains]); w = 1 / es ** 2
            mw = (w * ms).sum() / w.sum(); chi = np.sum(((ms - mw) / es) ** 2) / (len(ms) - 1); sf[i] = np.sqrt(max(1.0, chi))
        SF[k] = sf
    return SF

def main(pref, NB, dirs, pdg=False):
    E = load_all(dirs)
    need = [(L, b) for un in NEW for L, b in zip(LS, NEW[un])] + [(2 * L, b) for un in NEW for L, b in zip(LS, NEW[un])] + [(12, 3.6), (24, 3.6), (12, 4.5), (24, 4.5)]
    miss = [k for k in need if k not in E]
    assert not miss, miss
    ERR = {k: np.array([gamma_method(np.vstack(v)[:, i])[1] for i in range(2)]) for k, v in E.items()}
    rng = np.random.default_rng(20261018)
    M0 = build_replica(E, rng, ERR, central=True)
    SF = chain_sf(E) if pdg else None
    if pdg: ERR = {k: ERR[k] * (SF[k] if k in SF else 1.0) for k in ERR}
    u12c = {}
    # target u per scheme: u of the 12->24 pair (central)
    U12 = {c: {} for c in range(2)}
    for un in UN:
        b12 = NEW[un][2] if un in NEW else OLD[un]
        for ic in range(2): U12[ic][un] = M0[(12, b12)][ic]
    S0c = [shifts(M0, ERR, U12[ic], ic) for ic in range(2)]
    reps = [[None] * NB for _ in range(2)]
    for k in range(NB):
        Mk = build_replica(E, rng, ERR, SF=SF, M0=M0)
        for ic in range(2): reps[ic][k] = shifts(Mk, ERR, U12[ic], ic)
    # arrays S[ic][un][L] -> (NB+1)
    S = {ic: {un: {L: np.array([S0c[ic][un][L]] + [reps[ic][k][un][L] for k in range(NB)]) for L in LS} for un in UN} for ic in range(2)}
    nanbad = sum(int(np.isnan(S[ic][un][L]).sum()) for ic in range(2) for un in UN for L in LS)
    pe = {ic: {un: {L: float(np.nanstd(S[ic][un][L][1:])) for L in LS} for un in UN} for ic in range(2)}
    md = ['# Steps 3-4: theory-based extrapolation forms and configuration-bootstrap joint fits (step34.py)' + (' -- PDG chain-scatter scaling ON' if pdg else '') + '\n', f'Bootstrap replicas: {NB} (moving blocks of 3 configurations per chain, same configurations for c=0.3 and 0.4); NaN replicas: {nanbad}\n', 'Pair shifts (central, bootstrap error) at the common u of each scheme:\n', '| u nom | c | u | 6->12 | 8->16 | 12->24 |', '|---|---|---|---|---|---|']
    for ic, c in enumerate(CS):
        for un in UN: md.append(f'| {un} | {c} | {U12[ic][un]:.4f} | ' + ' | '.join(f'{S[ic][un][L][0]:.4f}({pe[ic][un][L]*1e4:.0f})' for L in LS) + ' |')
    # continuum values and k1 for each form
    RES = {}
    for form in FORMS:
        cont = {ic: {} for ic in range(2)}; chi = {ic: {} for ic in range(2)}
        for ic in range(2):
            for un in UN:
                e = [pe[ic][un][L] for L in LS]; uc = U12[ic][un]
                if form == 'quad' or form.startswith('Q'): Lsel = LS
                w, A, Wm = cont_weights(form, un, uc, e)
                y = np.array([S[ic][un][L] for L in LS])         # 3 x (NB+1)
                cont[ic][un] = w @ y
                r = y[:, 0] - A @ (np.linalg.inv(A.T @ Wm @ A) @ A.T @ Wm @ y[:, 0]); chi[ic][un] = (float(r @ Wm @ r), 3 - A.shape[1])
        RES[form] = dict(cont=cont, chi=chi)
    def slopes(form, which, k2free, joint=False):
        """which: list of ic. GLS with bootstrap covariance. joint: common k1 (universal), separate k2 per scheme"""
        ics = which; nu = len(UN)
        T = np.vstack([RES[form]['cont'][ic][un] - S0 for ic in ics for un in UN])
        C = np.cov(T[:, 1:]); C = np.atleast_2d(C)
        us = np.array([U12[ic][un] for ic in ics for un in UN])
        if joint:
            cols = [us]
            for j, ic in enumerate(ics):
                cols.append(np.array([U12[ic][un] ** 2 if jj == j else 0.0 for jj, ic2 in enumerate(ics) for un in UN]))
            A = np.column_stack(cols if k2free else cols[:1])
        else:
            A = np.column_stack([us, us ** 2]) if k2free else us[:, None]
        Ci = np.linalg.inv(C); G = np.linalg.inv(A.T @ Ci @ A) @ A.T @ Ci
        p = G @ T; res = T[:, 0] - A @ p[:, 0]; chi2 = float(res @ Ci @ res)
        return p, np.sqrt(np.diag(np.atleast_2d(np.cov(p[:, 1:])))), chi2, T.shape[0] - A.shape[1]
    md.append('\n## Step 3: continuum values (per c, per u) and k1 for each extrapolation form\n')
    md.append('Continuum shift (bootstrap error) at each u; chi2 of the pair fit (dof = 3 - #params):\n')
    md.append('| form | c | ' + ' | '.join(f'u={un}' for un in UN) + ' |'); md.append('|---|---|' + '---|' * len(UN))
    for form in FORMS:
        for ic, c in enumerate(CS):
            md.append(f'| {form} | {c} | ' + ' | '.join(f"{RES[form]['cont'][ic][un][0]:.4f}({np.std(RES[form]['cont'][ic][un][1:])*1e4:.0f}) [{RES[form]['chi'][ic][un][0]:.1f}/{RES[form]['chi'][ic][un][1]}]" for un in UN) + ' |')
    md.append('\nTwo-loop exact at those u: ' + ', '.join(f'{un}: {two(un):.4f}' for un in UN) + f'; one-loop {S0:.4f}\n')
    md.append('\n### Slope k1 (s0 fixed; two-loop-consistent target 0.0026), each c separately, GLS with bootstrap covariance across u\n')
    md.append('| form | k2 | c=0.3: k1 +- sig | (k1-0)/sig | (k1-0.0026)/sig | c=0.4: k1 +- sig | (k1-0)/sig | (k1-0.0026)/sig | k1(0.4)-k1(0.3) naive z | correlated z (bootstrap) | classification (rule) |'); md.append('|---|---|---|---|---|---|---|---|---|---|---|')
    OUT = {}
    for form in FORMS:
        for k2free in (True, False):
            pk = {}
            for ic in range(2): pk[ic] = slopes(form, [ic], k2free)
            d = pk[1][0][0, 0] - pk[0][0][0, 0]; dn = np.hypot(pk[0][1][0], pk[1][1][0]); dr = pk[1][0][0, 1:] - pk[0][0][0, 1:]
            ec = np.std(dr)
            k = {ic: (pk[ic][0][0, 0], pk[ic][1][0]) for ic in range(2)}
            two_ = all(abs(v - K1_2L) <= 2 * s and abs(v) >= 3 * s for v, s in k.values()); one_ = all(abs(v) <= 2 * s and abs(v - K1_2L) >= 3 * s for v, s in k.values())
            cl = 'TWO-LOOP' if two_ else ('ONE-LOOP' if one_ else 'UNDECIDED')
            OUT[(form, k2free)] = dict(k=k, d=d, dn=dn, ec=ec, cl=cl, chi=[pk[0][2:], pk[1][2:]])
            md.append(f"| {form} | {'free' if k2free else '0'} | {k[0][0]:.5f} +- {k[0][1]:.5f} | {k[0][0]/k[0][1]:+.1f} | {(k[0][0]-K1_2L)/k[0][1]:+.1f} | {k[1][0]:.5f} +- {k[1][1]:.5f} | {k[1][0]/k[1][1]:+.1f} | {(k[1][0]-K1_2L)/k[1][1]:+.1f} | {d:+.5f}/{dn:.5f} = {d/dn:+.1f} | {d:+.5f}/{ec:.5f} = {d/ec:+.1f} | {cl} |")
    # spread across physical forms
    phys = ['T0.636', 'T1', 'T1.636', 'T2.145']
    md.append('\n### Remaining extrapolation-form spread of k1 (k2 free)\n')
    for ic, c in enumerate(CS):
        v = {f: OUT[(f, True)]['k'][ic][0] for f in FORMS}
        sp_phys = max(v[f] for f in phys) - min(v[f] for f in phys); sp_all = max(v[f] for f in FORMS if f != 'const') - min(v[f] for f in FORMS if f != 'const')
        md.append(f"* c={c}: theory-Gamma forms T0.636..T2.145 spread {sp_phys:.5f}; incl. lin, quad, Q1.636 spread {sp_all:.5f}; primary {PRIMARY} k1 = {v[PRIMARY]:.5f} +- {OUT[(PRIMARY, True)]['k'][ic][1]:.5f}")
    md.append('\n## Step 4: joint fit of both c (bootstrap covariance over shared configurations)\n')
    md.append('Common k1 (k1 and the two-loop coefficient are scheme independent; k2 is scheme dependent -> one k2 per c), GLS over 10 continuum values with the full 10x10 bootstrap covariance:\n')
    md.append('| form | k2 | k1 (common) +- sig | (k1-0)/sig | (k1-0.0026)/sig | chi2/dof | k2(0.3) | k2(0.4) | rho(k1_0.3, k1_0.4) bootstrap |'); md.append('|---|---|---|---|---|---|---|---|---|')
    JOUT = {}
    for form in FORMS:
        for k2free in (True, False):
            p, sg, chi2, dof = slopes(form, [0, 1], k2free, joint=True)
            rho = float(np.corrcoef(slopes(form, [0], k2free)[0][0, 1:], slopes(form, [1], k2free)[0][0, 1:])[0, 1])
            JOUT[(form, k2free)] = (float(p[0, 0]), float(sg[0]), chi2, dof)
            k2s = (f'{p[1,0]:+.4f}({sg[1]:.4f})', f'{p[2,0]:+.4f}({sg[2]:.4f})') if k2free else ('0', '0')
            md.append(f"| {form} | {'free' if k2free else '0'} | {p[0,0]:.5f} +- {sg[0]:.5f} | {p[0,0]/sg[0]:+.1f} | {(p[0,0]-K1_2L)/sg[0]:+.1f} | {chi2:.1f}/{dof} | {k2s[0]} | {k2s[1]} | {rho:+.2f} |")
    # also report bootstrap rho of per-u continuum values between schemes
    md.append('\nBootstrap correlation between the two schemes of the continuum shift at each u (form %s): ' % PRIMARY + ', '.join(f"{un}: {np.corrcoef(RES[PRIMARY]['cont'][0][un][1:], RES[PRIMARY]['cont'][1][un][1:])[0,1]:+.2f}" for un in UN))
    md.append('Bootstrap correlation of pair shifts between schemes (6->12, 8->16, 12->24), mean over u: ' + ', '.join(f"{L}: {np.mean([np.corrcoef(S[0][un][L][1:], S[1][un][L][1:])[0,1] for un in UN]):+.2f}" for L in LS))
    open(pref + '.md', 'w').write('\n'.join(md) + '\n'); print('\n'.join(md))
    json.dump({'k1': {f'{f}|{k}': v for (f, k), v in {(f, k): dict(k=[list(map(float, OUT[(f, k)]['k'][i])) for i in range(2)], d=OUT[(f, k)]['d'], dn=OUT[(f, k)]['dn'], ec=OUT[(f, k)]['ec'], cl=OUT[(f, k)]['cl']) for (f, k) in OUT}.items()},
               'joint': {f'{f}|{k}': v for (f, k), v in JOUT.items()}}, open(pref + '.json', 'w'), indent=1, default=float)

if __name__ == '__main__':
    pref = sys.argv[1]; NB = int(sys.argv[2]) if len(sys.argv) > 2 else 400
    pdg = len(sys.argv) > 3 and sys.argv[3] == 'pdg'
    dirs = sys.argv[4].split(',') if len(sys.argv) > 4 else DIRS
    main(pref, NB, dirs, pdg)
