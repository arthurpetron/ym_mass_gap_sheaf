"""Spatial/temporal Polyakov loops on the final checkpointed configuration (read-only). Single-threaded."""
import numpy as np, sys, json
def qmul(a, b):
    return np.stack([a[...,0]*b[...,0]-a[...,1]*b[...,1]-a[...,2]*b[...,2]-a[...,3]*b[...,3],
        a[...,0]*b[...,1]+b[...,0]*a[...,1]-(a[...,2]*b[...,3]-a[...,3]*b[...,2]),
        a[...,0]*b[...,2]+b[...,0]*a[...,2]-(a[...,3]*b[...,1]-a[...,1]*b[...,3]),
        a[...,0]*b[...,3]+b[...,0]*a[...,3]-(a[...,1]*b[...,2]-a[...,2]*b[...,1])], -1)
def poly(path, Ls, Lt):
    raw = np.fromfile(path, dtype='<f8', offset=16).reshape(Lt, Ls, Ls, Ls, 4, 4)  # t,z,y,x,mu,quat
    res = {}
    for mu, name in [(0, 't'), (1, 'z'), (2, 'y'), (3, 'x')]:
        U = np.moveaxis(raw[..., mu, :], mu, 0)  # direction axis first
        P = U[0].copy()
        for k in range(1, U.shape[0]): P = qmul(P, U[k])
        p = P[..., 0]; res[name] = (float(p.mean()), float(p.std()/np.sqrt(p.size)), float(np.abs(p).mean()))
    return res
if __name__ == '__main__':
    out = {}
    for path, Ls, Lt in [(a, int(b), int(c)) for a, b, c in (x.split(':') for x in sys.argv[1:])]:
        r = poly(path, Ls, Lt); out[path] = r
        print(path, ' '.join(f"P_{k}={v[0]:+.4f}({v[1]:.4f}) |P|={v[2]:.4f}" for k, v in r.items()), flush=True)
    json.dump(out, open('runs/p6/polyakov_final_configs.json', 'w'), indent=1)
