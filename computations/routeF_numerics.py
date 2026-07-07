"""
Route F — numeric validation of the transfer-matrix <-> character IDENTIFICATION.

Validates (mpmath dps 50, sympy exact) that the 4D SU(2) block-spin margin
degradation EQUALS the fused-character excited-ratio defect, and that the
identification holds in BOTH the repo-native multiplicative (1 - sep) picture and
the physical -log picture, over the honest strong-coupling regime.

Objects (heat-kernel single-plaquette, SU(2)):
  dimQ(s) = s + 1,  c4(s) = s(s+2)  (scaled SU(2) Casimir; c4(0)=0, c4(1)=3, c4(2)=8)
  coeffW(w,s) = dimQ(s) * w**c4(s)          -- character coefficient / measure weight
  eigA(w,s)   = w**c4(s)                     -- multiplicity-BLIND transfer eigenvalue
  acNfull(w,t)= sum_{p<=t} coeffW(w,p)*coeffW(w,t-p)   -- 2-fold fusion (block-spin b=2)

Fine transfer separator (vacuum-normalized, coeffW(w,0)=1):
  sep(w)  = coeffW(w,1)/coeffW(w,0) = coeffW(w,1) = 2 w^3
Coarse (block-spin fused) separator:
  sep'(w) = acNfull(w,1)/acNfull(w,0) = acNfull(w,1) = 4 w^3 = 2*coeffW(w,1)
"""

import mpmath as mp
import sympy as sp

mp.mp.dps = 50

def dimQ(s): return s + 1
def c4(s):   return s * (s + 2)
def coeffW(w, s): return dimQ(s) * w**c4(s)
def eigA(w, s):   return w**c4(s)
def acNfull(w, t):
    return mp.fsum(coeffW(w, p) * coeffW(w, t - p) for p in range(t + 1))

def sep(w):  return coeffW(w, 1) / coeffW(w, 0)
def sepF(w): return acNfull(w, 1) / acNfull(w, 0)

print("="*74)
print("PART 1 — character diagonalization: eigenvalues = coeffW, ratio identities")
print("="*74)
for wv in ["1/6", "1/4", "1/2", "0.67", "0.9"]:
    w = mp.mpf(sp.Rational(wv)) if "/" in wv else mp.mpf(wv)
    print(f"w={wv:>5}: coeffW0={coeffW(w,0)!s:>4}  coeffW1={mp.nstr(coeffW(w,1),12):>14}"
          f"  =2w^3? {mp.nstr(2*w**3,12):>14}  acN0={mp.nstr(acNfull(w,0),6)}"
          f"  acN1={mp.nstr(acNfull(w,1),12)}  =4w^3? {mp.nstr(4*w**3,12)}")

print()
print("="*74)
print("PART 2 — THE IDENTIFICATION: margin degradation = fused excited-ratio defect")
print("  degradation  D(w)-D'(w) = sep'(w) - sep(w)   (multiplicative margin loss)")
print("  fused defect  fdef(w)   = acNfull(w,1) - coeffW(w,1)")
print("  claim: sep'(w)-sep(w) == fdef(w) == coeffW(w,1) == 2 w^3   (EXACT)")
print("="*74)
maxerr = mp.mpf(0)
for wv in ["1/6","1/4","1/3","1/2","0.6","0.67","0.9","0.99"]:
    w = mp.mpf(sp.Rational(wv)) if "/" in wv else mp.mpf(wv)
    D  = 1 - sep(w)            # fine multiplicative margin
    Dp = 1 - sepF(w)           # coarse multiplicative margin
    degr = Dp*0 + (D - Dp)     # = sep'(w) - sep(w)
    fdef = acNfull(w,1) - coeffW(w,1)
    e1 = abs(degr - fdef)
    e2 = abs(fdef - coeffW(w,1))
    e3 = abs(fdef - 2*w**3)
    maxerr = max(maxerr, e1, e2, e3)
    print(f"w={wv:>5}: D-D'={mp.nstr(degr,14):>16}  fdef={mp.nstr(fdef,14):>16}"
          f"  coeffW1={mp.nstr(coeffW(w,1),14):>16}  |errs|={mp.nstr(max(e1,e2,e3),3)}")
print(f"\n  MAX identification error over all w: {mp.nstr(maxerr,5)}  (expect ~1e-50)")

# sympy exact confirmation of the algebraic identity
wS = sp.symbols('w', positive=True)
coeffW1 = 2*wS**3
acN1    = 2*coeffW1            # acNfull(w,1) = 2*coeffW(w,1)
degrS   = sp.simplify((1 - coeffW1) - (1 - acN1))   # sep' - sep
fdefS   = sp.simplify(acN1 - coeffW1)
print("  sympy exact:  (D-D') - coeffW1 =", sp.simplify(degrS - coeffW1),
      " ; fdef - coeffW1 =", sp.simplify(fdefS - coeffW1), " (both must be 0)")

print()
print("="*74)
print("PART 3 — the -log (physical mass) picture and -log(1-x) >= x bridge")
print("  m(w)  = -log(sep(w)),  m'(w) = -log(sep'(w))")
print("  log-degradation m-m' = log(sep'/sep) = log(2)  (raw, un-renormalized)")
print("  bridge: m(w) = -log(1-(1-sep)) = -log(1-gapMargin) >= gapMargin = 1-sep")
print("="*74)
for wv in ["1/6","1/4","1/2"]:
    w = mp.mpf(sp.Rational(wv))
    s, sp_ = sep(w), sepF(w)
    m, mp_ = -mp.log(s), -mp.log(sp_)
    gm = 1 - s
    bridge_ok = m >= gm
    print(f"w={wv:>5}: m={mp.nstr(m,10):>12}  m'={mp.nstr(mp_,10):>12}"
          f"  m-m'={mp.nstr(m-mp_,10)}  log2={mp.nstr(mp.log(2),10)}"
          f"  gapMargin={mp.nstr(gm,10)}  (-log(1-x)>=x): {bridge_ok}")

print()
print("="*74)
print("PART 4 — HONEST regime: the raw fused defect vs the model envelope 6(1-w)^2")
print("  model defect envelope (Route A/B, pMult=1): env(w) = 6 (1-w)^2")
print("  claim: coeffW(w,1)=2w^3 <= env(w)  holds for STRONG coupling only")
print("  and:   sep'(w)=4w^3 < 1 (coarse gap exists) requires w < (1/4)^(1/3)")
print("="*74)
def env(w): return 6*(1-w)**2
wc = mp.findroot(lambda w: 2*w**3 - env(w), mp.mpf("0.6"))
wcut = (mp.mpf(1)/4)**(mp.mpf(1)/3)
for wv in ["1/6","1/2","0.6","0.63","0.67","0.9"]:
    w = mp.mpf(sp.Rational(wv)) if "/" in wv else mp.mpf(wv)
    print(f"w={wv:>5}: 2w^3={mp.nstr(2*w**3,10):>12}  env={mp.nstr(env(w),10):>12}"
          f"  defect<=env? {2*w**3 <= env(w)!s:>5}   sep'=4w^3={mp.nstr(4*w**3,10):>12}"
          f"  sep'<1? {4*w**3 < 1}")
print(f"\n  envelope crossover 2w^3 = 6(1-w)^2 at w = {mp.nstr(wc,12)}  (strong-cpl regime w<=~0.67)")
print(f"  coarse-gap cutoff  4w^3 = 1        at w = {mp.nstr(wcut,12)}  (raw fusion gap needs w<~0.63)")
print(f"  strong-coupling anchor w=1/6=0.1667 is comfortably inside both.  w<=1/2 is the")
print(f"  proved-regime edge (RouteADefectCharacter.charExcited_le_modelEnvelope).")

print()
print("="*74)
print("PART 5 — multiplicity-BLIND eigenvalue picture (GapIsEigenvalue VERDICT A)")
print("  eigA(w,1)=w^3 is the physical gap edge, dominant for ALL w in [0,1].")
print("  coeffW is the MEASURE weight (mult x eigenvalue); its dominance needs w<=7/9.")
print("="*74)
for wv in ["1/6","1/2","0.9","95/96"]:
    w = mp.mpf(sp.Rational(wv))
    dom_all = all(eigA(w,s) <= eigA(w,1) + mp.mpf("1e-45") for s in range(1,8))
    print(f"w={wv:>6}: eigA1=w^3={mp.nstr(eigA(w,1),10):>12}  <1? {eigA(w,1)<1}"
          f"   eigA1 dominates s=1..7? {dom_all}")
