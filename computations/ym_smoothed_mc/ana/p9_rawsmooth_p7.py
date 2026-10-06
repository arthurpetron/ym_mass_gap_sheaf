"""P9 item 5: raw vs smoothed effective masses on the P7 Ls=48 records (same format as P6_RAW_VS_SMOOTH). usage: p9_rawsmooth_p7.py <out.md>"""
import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(__file__)); os.environ['P6_SKIP'] = '0'
from p6_window import analyze
def f(v, e):
    if v is None or not np.isfinite(v) or not np.isfinite(e): return 'n/a'
    ed = min(max(1, int(np.ceil(-np.log10(e)))+1), 5) if e > 0 else 3; return f"{v:.{ed}f}({int(round(e*10**ed))})"
r = analyze('p7_rawsmooth', ['runs/b2.95_L48x48_s8/data.bin'], do_fit=False)
L = ["# P9 item 5: raw vs smoothed effective masses, P7 beta 2.95 48^3x48 side 8 (240 meas, bin %d)\n" % r['binsize'],
     "m_eff(n) = ln C(n)/C(n+1), E1, jackknife. 'drown' = first lag with C(n) < 2σ (m_eff shown only before it). [D] = differenced (subtraction-free). Same layout as P6_RAW_VS_SMOOTH.md (Ls=32).\n"]
lv0 = r['levels']['0.00']; nmax = len(lv0['meff'])
L.append("| rho | drown lag | " + " | ".join(f"n={n}" for n in range(nmax)) + " |"); L.append("|---|---|" + "---|"*nmax)
for rho, lv in r['levels'].items():
    C = np.array(lv['C']); Ce = np.array(lv['Ce']); dr = next((n for n in range(len(C)) if C[n] < 2*Ce[n]), None)
    L.append(f"| {rho} | {dr if dr is not None else '>'+str(len(C)-1)} | " + " | ".join(f(m, e) if (dr is None or n+1 < dr) else '–' for n, (m, e) in enumerate(zip(lv['meff'], lv['meffe']))) + " |")
for rho in ['0.00', '1.00']:
    lv = r['levels'][rho]; L.append(f"| {rho} [D] | | " + " | ".join(f(m, e) if np.isfinite(m) and e < 1 else '–' for m, e in zip(lv['meffD'], lv['meffDe'])) + " |")
L.append("\nReading: as at Ls=32 (P6), the raw side-8 loop (rho=0) drowns at lag 2 (only m_eff(0) = 3.16(27) ≈ the Ls=32 raw value), so it has no plateau; the smoothed loops give m_eff ≈ 0.40→0.27 over n=0..4 at rho=1, falling slowly (no clean plateau). Cheap re-analysis of existing records only.")
open(sys.argv[1], 'w').write('\n'.join(L) + '\n'); print('\n'.join(L))
