import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from window_analyze import analyze, fmt
print('| run | beta | side | rho | W=R(s+1)/R(s/2) | 2(1-W)/W | -2 log W | eps*side |')
print('|---|---|---|---|---|---|---|---|')
for d in sys.argv[1:]:
    r = analyze(d + '/data.bin'); h = r['hdr']; sm = r['smain']
    for v in r['levels'].values():
        if v['side'] != sm or abs(v['rho']-1.0) > 0.01 and abs(v['rho']-0.75)>0.01: continue
        D, De = v['D'], v['De']; f = lambda i: fmt(D[i], De[i])
        print(f"| {os.path.basename(d)} | {h['beta']} | {sm} | {v['rho']:.2f} | {f(16)} | {f(17)} | {f(18)} | {f(1)} |")
