#!/usr/bin/env python3
"""Joint (correlated) step-scaling analysis. One bootstrap replica draws the ensemble means of ALL (L,beta) at once
(independent Gaussians with the Gamma-method errors; chains at the same (L,beta) are combined by inverse variance first),
then for every replica: per-L interpolation fits of 1/g^2 - beta/4 = sum c_m (4/beta)^m, beta*(u) for each pair (L,2L),
Sigma = g^2(2L,beta*), shift s = 1/u - 1/Sigma.  The replicas give the full covariance of the shifts between pairs
(L=8 is shared by 4->8 and 8->16, L=12 by 6->12 and 12->24), which is used in generalised-least-squares continuum fits.
usage: see main(); library use: Data(dirs, obs, norm), Joint(data, c, M, pairs, targets, nboot)."""
import sys, os, glob, numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from gfana import *
from stepscale import fit_inv, inv_model, solve_beta, S0

class Data:
    def __init__(self, dirs, kind='su2', obs='clover', norm='lat', excl=('_cold', '_tau', '.alt'), only=None, ncol=None):
        self.runs = {}
        self.obs, self.norm, self.kind = obs, norm, kind
        ncol = ncol or (3 if kind == 'su2' else 2)
        for dr in dirs:
            for f in sorted(glob.glob(os.path.join(dr, '*.csv'))):
                n = os.path.basename(f)
                if not n.startswith(kind + '_') or any(x in n for x in excl): continue
                if only and not only(n): continue
                try:
                    r = load_run(f, ncol)
                except Exception:
                    continue
                if len(r['sweep']) < 20: continue
                self.runs.setdefault((r['L'], round(r['beta'], 6)), []).append((n, r))
        self._cache = {}

    def N(self, c, L):
        if self.kind == 'su2':
            if self.norm == 'cont': return N_cont(c)
            return N_lat(c, L) if self.obs == 'clover' else N_lat_plaq(c, L)
        raise NotImplementedError

    def g2(self, L, beta, c, qsel=None):
        """inverse-variance combination over chains: (mean, err, ntot, tau_samples)"""
        key = (L, beta, c, self.obs, self.norm)
        if key in self._cache: return self._cache[key]
        ms, es, ns, taus = [], [], 0, []
        for n, r in self.runs.get((L, beta), []):
            try:
                i = time_index(r, c)
            except AssertionError:
                continue
            t = r['times'][i]
            col = 0 if self.obs == 'clover' else 1
            x = t * t * r['E'][:, i, col] / self.N(c, L)
            m, e, tau, W = gamma_method(x)
            ms.append(m); es.append(e); ns += len(x); taus.append(tau)
        if not ms:
            self._cache[key] = None; return None
        w = 1 / np.array(es) ** 2
        m = float(np.sum(w * np.array(ms)) / w.sum()); e = float(1 / np.sqrt(w.sum()))
        self._cache[key] = (m, e, ns, float(np.mean(taus)))
        return self._cache[key]

    def betas(self, L, c):
        return sorted(b for (l, b) in self.runs if l == L and self.g2(l, b, c) is not None)

class Joint:
    def __init__(self, data, c, M, pairs, targets, nboot=800, seed=7, betarange=None):
        self.data, self.c, self.M, self.pairs, self.targets = data, c, M, pairs, targets
        rng = np.random.default_rng(seed)
        Ls = sorted({L for p in pairs for L in p})
        self.keys = {}  # per L: betas
        for L in Ls:
            self.keys[L] = [b for b in data.betas(L, c) if (betarange is None or betarange[0] <= b <= betarange[1])]
        self.mean = {L: np.array([data.g2(L, b, c)[0] for b in self.keys[L]]) for L in Ls}
        self.err = {L: np.array([data.g2(L, b, c)[1] for b in self.keys[L]]) for L in Ls}
        self.nboot = nboot
        self.S = np.full((nboot + 1, len(pairs), len(targets)), np.nan)   # shifts
        self.beta_star = np.full_like(self.S, np.nan)
        draws = {}
        for k in range(nboot + 1):
            draws[k] = {L: (self.mean[L] if k == 0 else self.mean[L] + rng.normal(size=len(self.mean[L])) * self.err[L]) for L in Ls}
        for ip, (L, L2) in enumerate(pairs):
            common = [b for b in self.keys[L] if b in self.keys[L2]]
            if len(common) < M + 2: continue
            i1 = [self.keys[L].index(b) for b in common]; i2 = [self.keys[L2].index(b) for b in common]
            lo, hi = min(common) - 1e-9, max(common) + 1e-9
            e1 = self.err[L][i1]; e2 = self.err[L2][i2]
            for k in range(nboot + 1):
                try:
                    c1 = fit_inv(common, draws[k][L][i1], e1, M); c2 = fit_inv(common, draws[k][L2][i2], e2, M)
                except Exception:
                    continue
                for iu, u in enumerate(targets):
                    try:
                        bs = solve_beta(c1, u, lo, hi)
                        sig = 1.0 / inv_model(c2, bs)
                    except Exception:
                        continue
                    self.S[k, ip, iu] = 1.0 / u - 1.0 / sig; self.beta_star[k, ip, iu] = bs

    def central(self): return self.S[0]
    def cov(self, iu, pidx):
        v = self.S[1:, pidx, iu]; v = v[~np.isnan(v).any(axis=1)]
        return np.cov(v.T) if len(v) > 20 else None, len(v)

# ---- continuum forms: basis functions of the smaller lattice size L (pair L->2L)
FORMS = {
    'a+bx':        lambda L: [1.0, 1 / L ** 2],
    'a+bx(3)':     lambda L: [1.0, 1 / L ** 2, 1 / L ** 4],              # x, x^2 (exact for 3 pairs)
    'a+bxlnx':     lambda L: [1.0, np.log(L) / L ** 2],                   # (a/L)^2 ln(L/a) only
    'a+bx+cxlnx':  lambda L: [1.0, 1 / L ** 2, np.log(L) / L ** 2],       # x and x ln: exact for 3 pairs
    'a+b/L':       lambda L: [1.0, 1 / L],                                # O(a)
    'a+b/L+cx':    lambda L: [1.0, 1 / L, 1 / L ** 2],
}

def gls(Ls, y, C, basis):
    A = np.array([basis(L) for L in Ls]); Ci = np.linalg.inv(C)
    cov = np.linalg.inv(A.T @ Ci @ A); p = cov @ A.T @ Ci @ y
    r = y - A @ p
    return p, cov, float(r @ Ci @ r), len(y) - A.shape[1]

def continuum(J, iu, pidx, form, diagonal=False):
    """GLS fit on the central shifts with the bootstrap covariance (or diagonal); error from refitting every replica."""
    Ls = [J.pairs[i][0] for i in pidx]
    S = J.S[:, pidx, iu]
    ok = ~np.isnan(S).any(axis=1)
    if ok[0] is False or not ok[0]: return None
    C, nvalid = J.cov(iu, pidx)
    if C is None: return None
    C = np.atleast_2d(C)
    if diagonal: C = np.diag(np.diag(C))
    basis = FORMS[form]
    p, cov, chi2, dof = gls(Ls, S[0], C, basis)
    reps = []
    for k in range(1, J.nboot + 1):
        if not ok[k]: continue
        pk, *_ = gls(Ls, S[k], C, basis); reps.append(pk[0])
    return dict(a=float(p[0]), err=float(np.std(reps)), chi2=chi2, dof=dof, par=p)
