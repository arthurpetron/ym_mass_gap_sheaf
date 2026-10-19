#!/usr/bin/env python3
"""Tree-level normalisation of the twisted gradient-flow coupling (Ramos, arXiv:1409.1445, eqs. (50), (66), (70), (72)) for SU(2), twist n_12 = 1.
Momenta P_mu = 2 pi (n_mu + ntilde_mu / N) / L, ntilde in {0..N-1}^2 for the twisted directions (code dirs 0,1), ntilde != (0,0); no zero modes.
Lattice (Wilson action + Wilson flow + clover E):  Nhat_T(c, L) = t^2/(2 L^4) sum'_P exp(-2 t Phat^2) [sum_{mu!=nu} Pring_mu^2 C_nu^2] / Phat^2,
  Phat_mu = 2 sin(P_mu/2), Pring_mu = sin P_mu, C_mu = cos(P_mu/2)   (= Ramos' c^4/128 sum' ... at t = c^2 L^2/8).
Continuum:  N_T(c) = 3 c^4/128 sum_{n in Z^4} sum'_{ntilde} exp(-pi^2 c^2 (n + ntilde/N)^2).
g2_TGF = t^2 <E_clover> / Nhat_T(c, L).  usage: python3 twist_norm.py (self-checks and table)"""
import numpy as np
from math import pi
_c = {}
def N_twist_lat(c, L, Nc=2):
    key = (round(c, 9), L)
    if key in _c: return _c[key]
    t = c * c * L * L / 8.0; tot = 0.0
    n = np.arange(L)
    for a in range(Nc):
        for b in range(Nc):
            if a == 0 and b == 0: continue
            p0 = 2 * pi * (n + a / Nc) / L; p1 = 2 * pi * (n + b / Nc) / L; p2 = 2 * pi * n / L
            P = np.meshgrid(p0, p1, p2, p2, indexing='ij')
            ph2 = sum(4 * np.sin(x / 2) ** 2 for x in P)
            pr = [np.sin(x) for x in P]; C = [np.cos(x / 2) for x in P]
            num = sum(pr[m] ** 2 * C[v] ** 2 for m in range(4) for v in range(4) if m != v)   # clover-E numerator (same as gfana._lat_nonzero)
            tot += np.sum(np.exp(-2 * t * ph2) * num / ph2)
    _c[key] = t * t * tot / (2.0 * L ** 4)
    return _c[key]

def N_twist_cont(c, Nc=2, nmax=12):
    n = np.arange(-nmax, nmax + 1).astype(float); tot = 0.0
    for a in range(Nc):
        for b in range(Nc):
            if a == 0 and b == 0: continue
            s1 = np.exp(-pi ** 2 * c * c * (n + a / Nc) ** 2).sum(); s2 = np.exp(-pi ** 2 * c * c * (n + b / Nc) ** 2).sum(); s0 = np.exp(-pi ** 2 * c * c * n ** 2).sum()
            tot += s1 * s2 * s0 * s0
    return 3 * c ** 4 / 128 * tot

if __name__ == '__main__':
    # check: lattice / continuum -> 1 as O(a^2) for L -> inf; continuum -> infinite-volume value 3(N^2-1)/(128 pi^2) for small c
    print('continuum check: L->inf infinite-volume value 3(N^2-1)/(128 pi^2) =', 9 / (128 * pi ** 2))
    for c in (0.3, 0.4, 0.5):
        Nc_ = N_twist_cont(c)
        print(f'c={c}: N_T cont = {Nc_:.8f};  lattice Nhat/Ncont - 1: ' + ', '.join(f'L={L}: {N_twist_lat(c, L)/Nc_-1:+.5f}' for L in (6, 8, 12, 16, 24, 32, 48)))
