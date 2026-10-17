"""Analysis helpers for the gradient-flow step-scaling study (MC measurement only).
Conventions: g^2_GF = t^2 <E(t)> / N,  t = c^2 L^2 / 8,  periodic torus (Fodor-Holland-Kuti-Nogradi-Wong, arXiv:1208.1051).
  N_cont(c) = 3 (Nc^2-1)/(128 pi^2) * (1+delta(c)),  delta(c) = -pi^2 c^4/3 + theta3(exp(-1/c^2))^4 - 1.
  N_lat(c,L): leading-order lattice perturbation theory for Wilson flow + clover E on L^4 (non-zero modes: lattice
              momentum sum; zero-mode contribution taken at its continuum value (Nc^2-1) c^4/64 -- an approximation).
"""
import numpy as np
from math import pi

def theta3(q, nmax=40):
    n = np.arange(-nmax, nmax + 1)
    return np.sum(q ** (n.astype(float) ** 2))

def N_cont(c, Nc=2):
    delta = -pi ** 2 * c ** 4 / 3.0 + theta3(np.exp(-1.0 / c ** 2)) ** 4 - 1.0
    return 3.0 * (Nc ** 2 - 1) / (128.0 * pi ** 2) * (1.0 + delta)

def N_cont_u1(c):
    # abelian: no zero-mode quartic term; non-zero modes only: (3/(128 pi^2)) (theta^4 - pi^2 c^4)
    return 3.0 / (128.0 * pi ** 2) * (theta3(np.exp(-1.0 / c ** 2)) ** 4 - pi ** 2 * c ** 4)

_cache = {}
def _lat_nonzero(c, L):
    key = (round(c, 9), L)
    if key in _cache:
        return _cache[key]
    t = c * c * L * L / 8.0
    n = np.arange(-L // 2, L // 2)
    N0, N1, N2, N3 = np.meshgrid(n, n, n, n, indexing='ij')
    ps = [2 * pi * x / L for x in (N0, N1, N2, N3)]
    ph = [2 * np.sin(p / 2) for p in ps]
    pr = [np.sin(p) for p in ps]
    cs2 = [np.cos(p / 2) ** 2 for p in ps]
    p2 = sum(x * x for x in ph)
    mask = p2 > 1e-14
    num = 0.0
    for mu in range(4):
        for nu in range(4):
            if mu != nu:
                num = num + pr[mu] ** 2 * cs2[nu]
    val = np.zeros_like(p2)
    val[mask] = np.exp(-2 * t * p2[mask]) * num[mask] / p2[mask]
    s = val.sum()
    res = t * t * s / (2.0 * L ** 4)  # per color: t^2 * (1/2V) sum ...
    _cache[key] = res
    return res

def N_lat(c, L, Nc=2):
    return (Nc ** 2 - 1) * (_lat_nonzero(c, L) + c ** 4 / 64.0)

def N_lat_u1(c, L):
    return _lat_nonzero(c, L)

# ---------------- statistics ----------------
def gamma_method(x, S=1.5, wmax=None):
    """Wolff (2004) Gamma-method with automatic windowing. Returns mean, error, tau_int, window
    (tau_int in units of the sample spacing; tau_int=0.5 means uncorrelated)."""
    x = np.asarray(x, float)
    n = len(x)
    m = x.mean()
    d = x - m
    if wmax is None:
        wmax = max(2, n // 2)
    f = np.fft.rfft(d, 2 * n)
    ac = np.fft.irfft(f * np.conj(f))[:n] / n
    g0 = ac[0]
    if g0 <= 0:
        return m, 0.0, 0.5, 0
    rho = ac / g0
    W = 1
    for w in range(1, wmax):
        tau = 0.5 + rho[1:w + 1].sum()
        W = w
        if tau <= 0.5:
            break
        taue = S / np.log((tau + 1.0) / tau)
        if np.exp(-w / taue) - taue / np.sqrt(w * n) < 0:
            break
    tau_f = max(0.5, 0.5 + rho[1:W + 1].sum())
    # Wolff's bias correction of the window truncation
    gW = ac[:W + 1].copy()
    cvar = (g0 + 2 * ac[1:W + 1].sum()) * (1 + (2 * W + 1) / n) / 1.0
    err = np.sqrt(max(cvar, 0.0) / n)
    return m, err, tau_f, W

def jackknife_binned(x, nb=20, f=np.mean):
    x = np.asarray(x, float)
    n = len(x)
    b = max(1, n // nb)
    k = n // b
    xs = x[:k * b].reshape(k, b)
    full = f(xs.reshape(-1))
    jk = np.array([f(np.delete(xs, i, axis=0).reshape(-1)) for i in range(k)])
    err = np.sqrt((k - 1) / k * np.sum((jk - jk.mean()) ** 2))
    return full, err, b

# ---------------- file loading ----------------
import re
def load_run(path, ncol_per_t):
    """returns dict(L,beta,sep,eps,times, sweep, plaq, E (nmeas,ntimes,ncol))"""
    hdr = open(path).readline()
    L = int(re.search(r'L=(\d+)', hdr).group(1))
    beta = float(re.search(r'beta=([\d.eE+-]+)', hdr).group(1))
    sep = int(re.search(r'sep=(\d+)', hdr).group(1))
    therm = int(re.search(r'therm=(\d+)', hdr).group(1))
    eps = float(re.search(r' eps=([\d.eE+-]+)', hdr).group(1))
    times = [float(x) for x in re.search(r'times=\[(.*?)\]', hdr).group(1).split(',')]
    rows = {}
    nt = len(times)
    for line in open(path):
        if line.startswith('#') or not line.strip():
            continue
        f = line.split()
        if len(f) != 3 + nt * ncol_per_t:  # truncated line after an interruption
            continue
        rows[int(f[0])] = [float(v) for v in f]  # duplicates after resume are bit-identical; keep last
    d = np.array([rows[k] for k in sorted(rows)])
    E = d[:, 3:3 + nt * ncol_per_t].reshape(len(d), nt, ncol_per_t)
    return dict(L=L, beta=beta, sep=sep, therm=therm, eps=eps, times=np.array(times), sweep=d[:, 1], plaq=d[:, 2], E=E)

def time_index(run, c):
    t = c * c * run['L'] ** 2 / 8.0
    i = int(np.argmin(np.abs(run['times'] - t)))
    assert abs(run['times'][i] - t) < 1e-9, (t, run['times'])
    return i
