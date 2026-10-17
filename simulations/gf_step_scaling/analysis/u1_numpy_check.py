#!/usr/bin/env python3
"""Independent (numpy) implementation of compact U(1) Wilson-action MC + Wilson flow + clover E, to cross-check the Rust u1gf pipeline at
moderate beta (where r = t^2<E>beta/N_lat_u1 != 1). Checkerboard Metropolis (independent code path from the Rust von-Mises heatbath/OR),
classical RK4 for the flow ODE d theta/dt = -(1/beta) dS/d theta, clover E = (1/2) sum_{mu<nu} G^2, G = (1/4) sum_leaves sin(theta_leaf).
usage: u1_numpy_check.py L beta nmeas sep therm seed   (single thread, nice it)"""
import os
os.environ.setdefault('OMP_NUM_THREADS', '1'); os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
import sys, numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from gfana import N_lat_u1, gamma_method

def plaq_angles(th, mu, nu):
    # theta_p(x; mu,nu) = th_mu(x) + th_nu(x+mu) - th_mu(x+nu) - th_nu(x)
    return th[mu] + np.roll(th[nu], -1, axis=mu) - np.roll(th[mu], -1, axis=nu) - th[nu]

def leaf_sum_sin(th, mu, nu):
    p = plaq_angles(th, mu, nu)
    # four plaquettes around x in the (mu,nu) plane: shifts (0,0), (-mu), (-nu), (-mu-nu)
    return 0.25 * (np.sin(p) + np.sin(np.roll(p, 1, axis=mu)) + np.sin(np.roll(p, 1, axis=nu)) + np.sin(np.roll(np.roll(p, 1, axis=mu), 1, axis=nu)))

def energy_clover(th):
    E = 0.0
    for mu in range(4):
        for nu in range(mu + 1, 4):
            G = leaf_sum_sin(th, mu, nu)
            E += 0.5 * np.mean(G * G)
    return E

def force(th):
    """dS/dtheta_mu(x) / beta = sum_nu [sin theta_p(x;mu,nu) - sin theta_p(x-nu;mu,nu)]  (nu != mu, with orientation signs)"""
    f = np.zeros_like(th)
    for mu in range(4):
        for nu in range(4):
            if nu == mu: continue
            if mu < nu:
                p = plaq_angles(th, mu, nu)
                f[mu] += np.sin(p) - np.roll(np.sin(p), 1, axis=nu)
            else:
                p = plaq_angles(th, nu, mu)  # plaquette (nu,mu): contains th_mu with opposite sign
                f[mu] += -np.sin(p) + np.roll(np.sin(p), 1, axis=nu)
    return f

def flow_to(th, t, eps=0.02):
    ns = max(1, int(np.ceil(t / eps - 1e-9))); h = t / ns
    th = th.copy()
    for _ in range(ns):
        k1 = -force(th); k2 = -force(th + 0.5 * h * k1); k3 = -force(th + 0.5 * h * k2); k4 = -force(th + h * k3)
        th = th + h * (k1 + 2 * k2 + 2 * k3 + k4) / 6.0
    return th

def metropolis_sweep(th, beta, rng, delta):
    L = th.shape[1]
    par = (np.add.outer(np.add.outer(np.arange(L), np.arange(L)), np.add.outer(np.arange(L), np.arange(L))) ) % 2
    for mu in range(4):
        for pr in (0, 1):
            mask = (np.indices((L,) * 4).sum(axis=0) % 2) == pr
            # local action of link (mu,x): beta * sum over planes containing it of (1 - cos) ; compute via staple
            def local(thx):
                s = np.zeros_like(thx)
                for nu in range(4):
                    if nu == mu: continue
                    # plaquettes containing link: forward (x;mu,nu) and backward (x-nu; mu,nu)
                    # theta_p(x;mu,nu) = th_mu(x) + th_nu(x+mu) - th_mu(x+nu) - th_nu(x)
                    stf = np.roll(th[nu], -1, axis=mu) - np.roll(th[mu], -1, axis=nu) - th[nu]
                    # backward plaquette (x-nu; mu,nu): th_mu(x-nu) + th_nu(x-nu+mu) - th_mu(x) - th_nu(x-nu)  (link appears with minus)
                    stb = np.roll(th[mu], 1, axis=nu) + np.roll(np.roll(th[nu], -1, axis=mu), 1, axis=nu) - np.roll(th[nu], 1, axis=nu)
                    if mu < nu:
                        s += (1 - np.cos(thx + stf)) + (1 - np.cos(stb - thx))
                    else:
                        s += (1 - np.cos(thx + stf * 0 + 0)) * 0  # placeholder replaced below
                return s
            # to keep orientation bookkeeping simple use brute-force local action through full plaquette angles for both orderings
            def action_local(thx):
                th2 = th.copy(); th2[mu] = thx
                s = np.zeros_like(thx)
                for nu in range(4):
                    if nu == mu: continue
                    a, b = (mu, nu) if mu < nu else (nu, mu)
                    p = plaq_angles(th2, a, b)
                    s += (1 - np.cos(p)) + (1 - np.cos(np.roll(p, 1, axis=nu)))
                return s
            old = th[mu].copy(); S0 = action_local(old)
            new = np.where(mask, old + (rng.random(old.shape) * 2 - 1) * delta, old)
            S1 = action_local(new)
            acc = (rng.random(old.shape) < np.exp(-beta * (S1 - S0))) & mask
            th[mu] = np.where(acc, new, old)
    return th

def main(L, beta, nmeas, sep, therm, seed, cs=(0.3, 0.4)):
    rng = np.random.default_rng(seed)
    th = np.zeros((4,) + (L,) * 4)
    delta = min(np.pi, 2.4 / np.sqrt(beta))
    for _ in range(therm): th = metropolis_sweep(th, beta, rng, delta)
    xs = {c: [] for c in cs}; pl = []
    for k in range(nmeas):
        for _ in range(sep): th = metropolis_sweep(th, beta, rng, delta)
        pl.append(np.mean([np.cos(plaq_angles(th, m, n)).mean() for m in range(4) for n in range(m + 1, 4)]))
        for c in cs:
            t = c * c * L * L / 8.0
            xs[c].append(t * t * energy_clover(flow_to(th, t)) * beta / N_lat_u1(c, L))
    pm, pe, pt, _ = gamma_method(np.array(pl))
    print(f'L={L} beta={beta} nmeas={nmeas} sep={sep}: plaq={pm:.5f}({pe*1e5:.0f}e-5) tau={pt:.2f}')
    for c in cs:
        m, e, tau, W = gamma_method(np.array(xs[c])); print(f'  r(c={c}) = {m:.4f}({e*1e4:.0f})  tau_int={tau:.2f}')

if __name__ == '__main__':
    a = sys.argv[1:]
    main(int(a[0]), float(a[1]), int(a[2]), int(a[3]), int(a[4]), int(a[5]))
