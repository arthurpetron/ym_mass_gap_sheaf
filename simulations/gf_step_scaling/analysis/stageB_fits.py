#!/usr/bin/env python3
"""Stage B: continuum-form variants on existing SU(2) data (joint bootstrap, GLS with full covariance).
usage: stageB_fits.py OUT.md OBS(clover|plaq) NBOOT DIR[,DIR...] [pairs=4:8,6:12,8:16] [cs=0.3,0.4]"""
import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from joint_fit import *

def table(dirs, obs, nboot, pairs, cs, Ms=(2, 3), targets=(1.3, 1.6, 2.0, 2.4)):
    d = Data(dirs, obs=obs, norm='lat')
    out = []
    one = f'one-loop {S0:.4f}'
    for c in cs:
        for M in Ms:
            J = Joint(d, c, M, pairs, list(targets), nboot=nboot)
            out.append(f'\n### obs={obs} c={c} M={M}  (pairs {", ".join(f"{a}->{b}" for a,b in pairs)}; {one}; (xx)=err in last digits)\n')
            out.append('| u | ' + ' | '.join(f'{a}->{b}' for a, b in pairs) + ' | ' + ' | '.join(['x (3 pairs) a|chi2', 'x ln x (3p)|chi2', '1/L (3p)|chi2', 'x+x^2 exact', 'x+x ln x exact', f'x, drop {pairs[0][0]}->{pairs[0][1]} (exact)']) + ' |')
            out.append('|---|' + '---|' * (len(pairs) + 6))
            n = len(pairs)
            for iu, u in enumerate(targets):
                row = [f'{u:g}']
                S = J.S[:, :, iu]
                for ip in range(n):
                    v = S[1:, ip]; v = v[~np.isnan(v)]
                    row.append(f'{S[0, ip]:.4f}({np.std(v)*1e4:.0f})' if not np.isnan(S[0, ip]) else '-')
                def fmt(form, idx, chi=True):
                    r = continuum(J, iu, idx, form)
                    if r is None: return '-'
                    s = f"{r['a']:.4f}({r['err']*1e4:.0f})"
                    if chi and r['dof'] > 0: s += f"|{r['chi2']:.1f}"
                    return s
                allp = list(range(n))
                if n >= 3:
                    row += [fmt('a+bx', allp), fmt('a+bxlnx', allp), fmt('a+b/L', allp), fmt('a+bx(3)', allp, False), fmt('a+bx+cxlnx', allp, False), fmt('a+bx', allp[1:], False)]
                else:
                    row += ['-'] * 5 + [fmt('a+bx', allp, False)]
                out.append('| ' + ' | '.join(row) + ' |')
    return '\n'.join(out)

if __name__ == '__main__':
    outf, obs, nb, dirs = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4].split(',')
    pairs = [tuple(map(int, p.split(':'))) for p in (sys.argv[5] if len(sys.argv) > 5 else '4:8,6:12,8:16').split(',')]
    cs = [float(x) for x in (sys.argv[6] if len(sys.argv) > 6 else '0.3,0.4').split(',')]
    t = table(dirs, obs, nb, pairs, cs)
    open(outf, 'w').write(t + '\n'); print(t)
