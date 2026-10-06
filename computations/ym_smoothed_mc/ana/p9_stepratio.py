"""P9: step-ratio constant c(k) = side*(1 - R(k+1)/R(k)) from the P5/P6 m_eff tables.
This is the open input of 9cb9f1e2/9d58a5df (ExprStepRatioAnyC): window survival follows from
side_j*(1-rho_j) <= c <= C at SOME lag k_j <= side_j/2. Since R(k+1)/R(k) = exp(-m_eff(k)),
c(k) = side*(1-exp(-m_eff(k))). Uses only existing runs/p6/*.json (no new MC).
CAVEAT: these are the flow-smoothed / raw Wilson-loop operators of the MC, NOT the exact Lean anchor Y_j.
usage: p9_stepratio.py <p6_json_dir> <out.md>"""
import json, math, os, sys, time
d0, outp = sys.argv[1], sys.argv[2]
runs = [('p5_b2.50_s2.json', 2.50), ('p5_b2.60_s3.json', 2.60), ('p5_b2.70_s4.json', 2.70),
        ('p5_b2.85_s6.json', 2.85), ('b2.95_s8.json', 2.95), ('b3.00_s10_AB.json', 3.00)]
def fmt(m, e, s):
    if m is None or not math.isfinite(m): return 'n/a'
    c = s*(1-math.exp(-m)); ce = s*math.exp(-m)*e if (e is not None and math.isfinite(e)) else float('nan')
    return f"{c:.2f}({ce:.2f})" if math.isfinite(ce) else f"{c:.2f}(?)"
L = [f"# P9 step-ratio constant c(k) = side*(1 - R(k+1)/R(k)) — {time.strftime('%Y-%m-%d %H:%M %Z')}\n",
     "Source: existing P5/P6 effective masses (runs/p6/*.json); c(k) = side*(1-exp(-m_eff(k))), error by linear propagation.",
     "Lean consumer: `expr_windowSurvivalFrom_of_stepRatio_anyC` (9cb9f1e2) needs side_j*(1-rho_j) <= c <= C at ONE lag k_j <= side_j/2.",
     "Because R is log-convex, R(k+1)/R(k) is nondecreasing in k, so the most favorable admissible lag is k = side/2.\n",
     "**Caveat:** MC operators only (rho = flow radius / side; rho=0 is the raw loop). NOT the exact Lean anchor Y_j, whose W is still unresolved (P8). Numerics, not proof.\n",
     "| beta | side | rho | " + " | ".join(f"c(k={k})" for k in range(6)) + " |", "|---|---|---|" + "---|"*6]
for f, b in runs:
    d = json.load(open(os.path.join(d0, f))); s = d['smain']
    for key in ['0.00', '0.50', '1.00', '1.50']:
        lv = d['levels'].get(key)
        if not lv: continue
        cells = [fmt(lv['meff'][k], lv['meffe'][k], s) if k <= s//2 and k < len(lv['meff']) else '' for k in range(6)]
        L.append(f"| {b} | {s} | {key} | " + " | ".join(cells) + " |")
L += ["\n## Reading",
      "* Smoothed loop (rho ~ 1): c(k) stays about 1.2-2.4 at every measured lag k <= side/2 for sides 2-10, with no growth in side. "
      "So on the smoothed operator the step-ratio input looks satisfied with C = 3 (theta_C = 2^-8, c0 = 2^9), consistent with eps*side ~ 2.",
      "* Raw loop (rho = 0): c(0) ~ side (1.75, 2.68, 3.61, 5.72, 7.99, 9.90) and larger lags are noise. This is consistent with the 9d58a5df docstring "
      "caveat that the lag-0 H-ray version on raw slab vectors is vacuous.",
      "* Consistency check: log-convexity forces c(k) to be NONINCREASING in k. Sides 2-8 obey this. Side 10 (beta 3.0) rises with k at rho 1.0-1.5 "
      "(e.g. 1.68(8) -> 2.36(46) at rho 1.5, about 1.5 sigma), another sign that side 10 is not thermalized (P6) and that its streams disagree "
      "(WINDOW_SURVIVAL_s10_streamB, slow modes / vacuum subtraction). Read that row loosely.",
      "* Nothing here touches the exact Lean anchor, the physical box, or the gap branch."]
open(outp, 'w').write("\n".join(L) + "\n"); print('wrote', outp)
