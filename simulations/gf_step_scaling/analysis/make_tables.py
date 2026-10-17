#!/usr/bin/env python3
"""Markdown tables from stepscale.py outputs. usage: make_tables.py RESDIR NORM  -> prints markdown.
Rows: (c, pair, u): beta*, Sigma (M=2), 1/u-1/Sigma (M=2) and (M=3), one-loop shift. Then the (a/L)^2 extrapolation rows."""
import sys, csv, os
res, norm = sys.argv[1], sys.argv[2]
rows = list(csv.DictReader(open(os.path.join(res, f'stepscaling_{norm}.csv'))))
f = lambda r, k: float(r[k])
out = ['| c | pair | u | beta* (L) | Sigma (M=2) | 1/u-1/Sigma (M=2) | 1/u-1/Sigma (M=3) | one-loop 0.0644 ratio (M=2) | chi2/dof L, 2L (M=2) |', '|---|---|---|---|---|---|---|---|---|']
key = lambda r: (r['c'], r['pair'], r['u'])
m3 = {key(r): r for r in rows if r['M'] == '3'}
for r in rows:
    if r['M'] != '2': continue
    r3 = m3.get(key(r))
    s3 = f"{f(r3,'inv_shift'):.4f}({f(r3,'inv_shift_err')*1e4:.0f})" if r3 else '-'
    out.append(f"| {r['c']} | {r['pair']} | {f(r,'u'):.1f} | {f(r,'beta'):.3f} | {f(r,'Sigma'):.4f}({f(r,'Sigma_err')*1e4:.0f}) | {f(r,'inv_shift'):.4f}({f(r,'inv_shift_err')*1e4:.0f}) | {s3} | {f(r,'inv_shift')/f(r,'one_loop_shift'):.2f} | {f(r,'chi_L'):.1f}, {f(r,'chi_2L'):.1f} |")
print('\n'.join(out)); print()
cf = os.path.join(res, f'continuum_{norm}.csv')
if os.path.exists(cf):
    ext = list(csv.DictReader(open(cf)))
    print('| c | M | #pairs | u | Sigma(a/L->0) | 1/u-1/Sigma(a/L->0) | one-loop | note |'); print('|---|---|---|---|---|---|---|---|')
    for r in ext:
        print(f"| {r['c']} | {r['M']} | {r['npairs']} | {f(r,'u'):.1f} | {f(r,'Sigma_cont'):.4f}({f(r,'Sigma_cont_err')*1e4:.0f}) | {f(r,'inv_shift'):.4f}({f(r,'inv_shift_err')*1e4:.0f}) | {f(r,'one_loop_shift'):.4f} | {r['note']} |")
