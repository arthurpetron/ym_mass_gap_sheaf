#!/usr/bin/env python3
"""Tree-level (free-field) lattice normalisation N(c,L) of g2_GF = t^2<E_clover>/N for the ZEUTHEN flow (Ramos-Sint arXiv:1508.05552, eq. (5)):
Wilson-action ensembles (propagator H_W^+), flow  dA/dt = -D H_LW A,  D = diag(1 - phat_mu^2/12) [(1 + a^2/12 nabla* nabla) in momentum space],
H_LW = sum_{mu<nu} w_{mu nu} B^+ B, w = c0 + c1 (|1+e^{ip_mu}|^2 + |1+e^{ip_nu}|^2) = 1 + (phat_mu^2 + phat_nu^2)/12 (c0=5/3, c1=-1/12),
B_{mu nu}.A = (e^{ip_mu}-1) A_nu - (e^{ip_nu}-1) A_mu; clover E per mode: cos^2(p_mu/2) cos^2(p_nu/2) |B_{mu nu}.A|^2.
Zero mode as in gfana.N_lat (continuum value c^4/64 per colour, an approximation shared with the Wilson normalisation).
mode='wilson' reproduces gfana.N_lat (checked).  Cached.  usage: python3 zeuthen_norm.py  (runs the self-check and prints a table)"""
import numpy as np
from math import pi
try: from gfana import N_lat, _lat_nonzero
except ImportError: pass
_cache = {}
def nz_sum(c, L, mode='zeuthen'):
    key = (round(c, 9), L, mode)
    if key in _cache: return _cache[key]
    t = c * c * L * L / 8.0
    p = 2 * pi * np.fft.fftfreq(L)
    P = np.stack(np.meshgrid(p, p, p, p, indexing='ij'), -1).reshape(-1, 4)
    keep = np.any(np.abs(P) > 1e-12, axis=1); P = P[keep]
    ph2 = 4 * np.sin(P / 2) ** 2                       # phat_mu^2
    q = np.exp(1j * P) - 1                              # (e^{ip}-1)
    n = len(P)
    Bm = np.zeros((n, 6, 4), complex); planes = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    for k, (m, v) in enumerate(planes):
        Bm[:, k, v] = q[:, m]; Bm[:, k, m] = -q[:, v]
    cc = np.stack([np.cos(P[:, m] / 2) ** 2 * np.cos(P[:, v] / 2) ** 2 for m, v in planes], 1)       # n x 6
    HW = np.einsum('nka,nkb->nab', Bm.conj(), Bm)       # sum B^+ B  (B row vector: A -> B.A)
    if mode == 'wilson':
        HF = HW; D = np.ones((n, 4))
    else:
        w = np.stack([1 + (ph2[:, m] + ph2[:, v]) / 12 for m, v in planes], 1)
        HF = np.einsum('nk,nka,nkb->nab', w, Bm.conj(), Bm); D = 1 - ph2 / 12
    # e^{-tK}, K = D HF = D^{1/2} S D^{-1/2},  S = D^{1/2} HF D^{1/2} hermitian
    sd = np.sqrt(D)
    S = sd[:, :, None] * HF * sd[:, None, :]
    lam, V = np.linalg.eigh(S)
    G = (V * np.exp(-t * lam)[:, None, :]) @ V.conj().transpose(0, 2, 1)
    G = sd[:, :, None] * G / sd[:, None, :]
    # initial covariance: pseudo-inverse of Wilson Hessian
    lw, Vw = np.linalg.eigh(HW)
    inv = np.where(lw > 1e-9, 1 / np.where(lw > 1e-9, lw, 1), 0.0)
    S0 = (Vw * inv[:, None, :]) @ Vw.conj().transpose(0, 2, 1)
    Sig = G @ S0 @ G.conj().transpose(0, 2, 1)
    # E_mode = sum_k cc_k B_k Sig B_k^+
    Em = np.einsum('nk,nka,nab,nkb->n', cc, Bm, Sig, Bm.conj()).real
    res = t * t * Em.sum() / (2.0 * L ** 4)
    _cache[key] = res
    return res

def N_zeu(c, L, Nc=2):
    return (Nc ** 2 - 1) * (nz_sum(c, L, 'zeuthen') + c ** 4 / 64.0)

if __name__ == '__main__':
    for L in (4, 6):
        for c in (0.3, 0.4):
            print(f'L={L} c={c}: wilson-check {nz_sum(c, L, "wilson"):.12f} vs gfana {_lat_nonzero(c, L):.12f}; zeuthen nonzero {nz_sum(c, L):.8f}')
    print('N_lat vs N_zeu (SU(2), incl. zero mode), ratio N_zeu/N_lat:')
    for L in (4, 6, 8, 12, 16, 24):
        print(L, ' '.join(f'c={c}: {N_lat(c, L):.6f} {N_zeu(c, L):.6f} ({N_zeu(c, L)/N_lat(c, L):.4f})' for c in (0.3, 0.4, 0.5)))
