#!/usr/bin/env python3
"""Independent check of the abelian tree-level normalisation N_lat_u1(c,L) (gfana.py) by an exact Gaussian sampler of the
free lattice U(1) theory (beta -> infinity limit of the compact action): A_mu(p) = (1/sqrt(beta)) (1 - e e^+) xi / |q|, q_mu = e^{i p_mu}-1,
Wilson flow of the free theory = exp(-t |q|^2) on transverse modes, clover field strength G = (1/4) sum of the four plaquette
leaves, E = (1/2) sum_{mu<nu} G^2 (theta units), so that t^2 <E> * beta = N_lat_u1(c,L).
usage: free_field_u1.py L nsamples [seed]   (single thread numpy)"""
import os
os.environ.setdefault('OMP_NUM_THREADS', '1'); os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
import sys, numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from gfana import N_lat_u1, N_cont_u1

def run(L, ns, seed=1, cs=(0.3, 0.4, 0.5), beta=1.0):
    rng = np.random.default_rng(seed)
    p = 2 * np.pi * np.fft.fftfreq(L) * 1.0  # p = 2 pi n / L, n in [-L/2, L/2)
    P = np.meshgrid(p, p, p, p, indexing='ij')
    q = [np.exp(1j * x) - 1 for x in P]
    q2 = sum(np.abs(x) ** 2 for x in q)
    zero = q2 < 1e-14
    q2s = np.where(zero, 1.0, q2)
    e = [x / np.sqrt(q2s) for x in q]
    cl = {}
    out = {c: [] for c in cs}
    for _ in range(ns):
        xi = [np.fft.fftn(rng.standard_normal((L,) * 4)) / L ** 2 for _ in range(4)]  # unitary FFT: E|xi|^2 = 1
        proj = sum(np.conj(e[m]) * xi[m] for m in range(4))
        A = [(xi[m] - e[m] * proj) / np.sqrt(q2s * beta) for m in range(4)]
        for m in range(4): A[m][zero] = 0.0
        for c in cs:
            t = c * c * L * L / 8.0
            f = np.exp(-t * q2)
            Af = [a * f for a in A]
            E = 0.0
            for mu in range(4):
                for nu in range(mu + 1, 4):
                    F = q[mu] * Af[nu] - q[nu] * Af[mu]
                    clov = np.cos(P[mu] / 2) * np.cos(P[nu] / 2)  # |average of 4 leaf shifts|
                    E += 0.5 * np.sum(np.abs(F * clov) ** 2) / L ** 4
            out[c].append(t * t * E * beta)
    res = []
    for c in cs:
        v = np.array(out[c]); m = v.mean(); er = v.std(ddof=1) / np.sqrt(len(v))
        Nf = N_lat_u1(c, L)
        res.append((c, m, er, Nf, m / Nf, er / Nf, N_cont_u1(c)))
    return res

def exact(L, cs=(0.3, 0.4, 0.5)):
    """Deterministic mode sum of the same Gaussian model: <|F_{mu nu}|^2> per mode from the transverse propagator."""
    p = 2 * np.pi * np.fft.fftfreq(L)
    P = np.meshgrid(p, p, p, p, indexing='ij')
    q = [np.exp(1j * x) - 1 for x in P]
    q2 = sum(np.abs(x) ** 2 for x in q); zero = q2 < 1e-14; q2s = np.where(zero, 1.0, q2)
    e = [x / np.sqrt(q2s) for x in q]
    res = []
    for c in cs:
        t = c * c * L * L / 8.0
        tot = 0.0
        for mu in range(4):
            for nu in range(mu + 1, 4):
                Pnn = 1 - np.abs(e[nu]) ** 2; Pmm = 1 - np.abs(e[mu]) ** 2; Pnm = -e[nu] * np.conj(e[mu])
                FF = (np.abs(q[mu]) ** 2 * Pnn + np.abs(q[nu]) ** 2 * Pmm - 2 * np.real(q[mu] * np.conj(q[nu]) * Pnm)) / q2s
                clov = (np.cos(P[mu] / 2) * np.cos(P[nu] / 2)) ** 2
                v = 0.5 * FF * clov * np.exp(-2 * t * q2)
                v[zero] = 0.0
                tot += v.sum() / L ** 4
        res.append((c, t * t * tot, N_lat_u1(c, L)))
    return res

if __name__ == '__main__':
    if sys.argv[1] == 'exact':
        print('# L c  exact-mode-sum  N_lat_u1(formula)  ratio   (deterministic check, independent code path)')
        for L in map(int, sys.argv[2].split(',')):
            for c, a, b in exact(L): print(f'{L} {c} {a:.10e} {b:.10e} {a/b:.12f}')
        sys.exit()
    L = int(sys.argv[1]); ns = int(sys.argv[2]); seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    print('# L c  MC(t^2<E>beta)  err  N_lat_u1(formula)  ratio MC/formula  err  N_cont_u1')
    for r in run(L, ns, seed):
        print(f'{L} {r[0]} {r[1]:.6e} {r[2]:.1e} {r[3]:.6e} {r[4]:.5f} {r[5]:.5f} {r[6]:.6e}')
