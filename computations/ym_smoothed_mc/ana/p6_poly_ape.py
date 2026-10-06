"""APE-smeared (4D, alpha=0.5, SU(2) projection by normalization) Polyakov loops on final checkpoint configs. Read-only, single thread, float32."""
import numpy as np, sys, json, time
from p6_poly import qmul
def dag(a): return np.concatenate([a[..., :1], -a[..., 1:]], -1)
def ape(L, alpha, n, log=None):
    # L: (4, Lt, Ls, Ls, Ls, 4) ; axis of direction mu in lattice array = mu (t,z,y,x)
    for it in range(n):
        new = np.empty_like(L)
        for mu in range(4):
            S = np.zeros_like(L[0])
            for nu in range(4):
                if nu == mu: continue
                # up staple: U_nu(x) U_mu(x+nu) U_nu(x+mu)^dag
                Umu_xnu = np.roll(L[mu], -1, axis=nu); Unu_xmu = np.roll(L[nu], -1, axis=mu)
                S += qmul(qmul(L[nu], Umu_xnu), dag(Unu_xmu))
                # down staple: U_nu(x-nu)^dag U_mu(x-nu) U_nu(x-nu+mu)
                Unu_m = np.roll(L[nu], 1, axis=nu); Umu_m = np.roll(L[mu], 1, axis=nu); Unu_mmu = np.roll(Unu_m, -1, axis=mu)
                S += qmul(qmul(dag(Unu_m), Umu_m), Unu_mmu)
            V = (1-alpha)*L[mu] + (alpha/6)*S
            new[mu] = V/np.linalg.norm(V, axis=-1, keepdims=True)
        L = new
    return L
def polys(L):
    r = {}
    for mu, nm in [(0, 't'), (1, 'z'), (2, 'y'), (3, 'x')]:
        U = np.moveaxis(L[mu], mu, 0); P = U[0].copy()
        for k in range(1, U.shape[0]): P = qmul(P, U[k])
        p = P[..., 0].astype(np.float64); r[nm] = [float(p.mean()), float(p.std()), float(np.abs(p).mean())]
    return r
if __name__ == '__main__':
    steps = [int(x) for x in sys.argv[1].split(',')]; out = {}
    for spec in sys.argv[2:]:
        path, Ls, Lt = spec.split(':'); Ls, Lt = int(Ls), int(Lt)
        raw = np.fromfile(path, dtype='<f8', offset=16).reshape(Lt, Ls, Ls, Ls, 4, 4).astype(np.float32)
        L = np.ascontiguousarray(np.moveaxis(raw, 4, 0)); del raw
        done = 0; out[path] = {}; t0 = time.time()
        for n in steps:
            L = ape(L, 0.5, n-done); done = n; r = polys(L); out[path][n] = r
            print(path, f"n_APE={n}", ' '.join(f"P_{k}={v[0]:+.4f} sd={v[1]:.3f}" for k, v in r.items()), f"{time.time()-t0:.0f}s", flush=True)
        json.dump(out, open('/workspace/ymmc/p4_smoothed/runs/p6/polyakov_ape.json', 'w'), indent=1)
