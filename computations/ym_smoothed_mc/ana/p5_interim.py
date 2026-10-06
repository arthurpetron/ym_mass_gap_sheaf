import sys, os, subprocess
sys.path.insert(0, os.path.dirname(__file__))
from analyze import analyze, fmt
from summary import sqrt_t0
d = sys.argv[1]; r = analyze(d + '/data.bin'); h = r['hdr']; s = r['smain']
print(f"# P5 interim: {os.path.basename(d)} (auto-generated)\n")
print(f"beta={h['beta']} {h['Ls']}^3x{h['Lt']} side={s}; side*a/sqrt(t0)={s/sqrt_t0(h['beta']):.3f} (t0 extrapolated from Hirakida fit); Ls*a/sqrt(t0)={h['Ls']/sqrt_t0(h['beta']):.2f}; N={r['N']} bin={r['binsize']} nbins={r['nbins']} plaq={r['plaq']:.5f}; tau_int={r['taus']}\n")
print('| rho | eps | eps*side | R(2u)/R(0) | R(4u)/R(2u) | kappa_b | eps_shift*side | eps_half*side | eps_box*side | a m_eff |')
print('|---|---|---|---|---|---|---|---|---|---|')
for v in r['levels'].values():
    if v['side'] != s: continue
    D, De = v['D'], v['De']; f = lambda i: fmt(D[i], De[i])
    print(f"| {v['rho']:.2f} | {f(0)} | {f(1)} | {f(2)} | {f(3)} | {f(4)} | {f(9)} | {f(11)} | {f(13)} | {f(7)} |")
print('\nResources:'); print(subprocess.run(['python3', os.path.join(os.path.dirname(__file__), 'ressum.py'), d], capture_output=True, text=True).stdout)
