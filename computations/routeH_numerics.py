"""
Route H — renormalization / counterterm validation of FullRangeFusedDefect.
LEAN-CORE model (SU(2), pMult=1): dimQ1=2, C4(1)=3.

Objects:
  raw(w)   = coeffW(w,1)               = dimQ1 * w^3            = 2 w^3        (raw excited/vacuum ratio; RouteA/F 'raw fused defect')
  CT(w)    = dimQ1 * renormW(w)         = 2*(1 - 3*(1-w))       = 6w - 4       (marginal counterterm; renormW = retuned weight)
  ren(w)   = raw(w) - CT(w)             = 2w^3 - 6w + 4                        (RENORMALIZED / counterterm-subtracted defect)
           = bondMovingDeltaRen(1,1,w)  = dimQ1*(3(1-w) - (1-w^3)) = 2(1-w)^2(2+w)
  env(w)   = 6 (1-w)^2                                                        (transverse-quadratic envelope, pMult=1)
"""
import mpmath as mp, sympy as sp
mp.mp.dps = 50

def raw(w): return 2*w**3
def CT(w):  return 6*w - 4
def ren(w): return raw(w) - CT(w)
def env(w): return 6*(1-w)**2

print("=== EXACT (sympy) identities ===")
w = sp.symbols('w', real=True)
raw_s = 2*w**3
CT_s  = 6*w - 4
ren_s = sp.expand(raw_s - CT_s)
bmdr  = sp.expand(2*(3*(1-w) - (1 - w**3)))      # dimQ1*(C4(1)(1-w) - (1-w^3))
fac   = sp.expand(2*(1-w)**2*(2+w))
print(" raw - CT              =", ren_s)
print(" bondMovingDeltaRen    =", bmdr, "   ->  raw-CT == bmdr :", sp.simplify(ren_s-bmdr)==0)
print(" 2(1-w)^2(2+w)         =", fac, "   ->  == ren        :", sp.simplify(ren_s-fac)==0)
print(" DECOMPOSITION  raw == ren + CT :", sp.simplify(raw_s-(ren_s+CT_s))==0)
print(" ren <= env  <=>  2+w<=3  <=>  w<=1 :  env-ren =", sp.factor(sp.expand(6*(1-w)**2 - ren_s)))
print()

print("=== crossover: raw exceeds env  <=>  w^3 > 3(1-w)^2 ===")
poly = sp.Poly(w**3 - 3*w**2 + 6*w - 3, w)   # w^3 - 3(1-w)^2 = w^3 -3 +6w -3w^2
roots = [r for r in sp.nroots(poly) if abs(sp.im(r))<1e-30 and 0<sp.re(r)<1]
wstar = mp.mpf(str(sp.re(roots[0])))
print(" raw=env crossover  w* =", wstar, "  (raw>env for w>w*)")
print()

print("=== table: w | raw=2w^3 | CT=6w-4 | ren=raw-CT | env=6(1-w)^2 | ren<=env | raw<=env ===")
for wv in [mp.mpf(k)/mp.mpf(20) for k in range(1,20)] + [mp.mpf('0.95'), mp.mpf('0.99'), mp.mpf('0.999')]:
    r, c, rn, e = raw(wv), CT(wv), ren(wv), env(wv)
    print(f" w={float(wv):5.3f} | raw={float(r):7.4f} | CT={float(c):7.4f} | ren={float(rn):8.5f} | env={float(e):8.5f} | ren<=env:{rn<=e} | raw<=env:{r<=e}")

print()
print("=== adversarial: at w->1 does CT cancel the raw divergence? ===")
for wv in [mp.mpf('0.9'), mp.mpf('0.99'), mp.mpf('0.999'), mp.mpf('0.9999')]:
    print(f" w={float(wv):7.4f}: raw={float(raw(wv)):.6f} (->2)  CT={float(CT(wv)):.6f} (->2)  ren=raw-CT={float(ren(wv)):.8f} (->0)  env={float(env(wv)):.8f}")

print()
print("=== worst-case ratio ren/env over (0,1) (must stay <=1) ===")
mx = mp.mpf(0)
for i in range(1,1000):
    wv = mp.mpf(i)/mp.mpf(1000)
    mx = max(mx, ren(wv)/env(wv))
print(" max ren/env =", mx, " (=(2+w)/3, sup=1 at w->1)")

print()
print("=== the specific Lean witness w=9/10 (raw_ratio_exceeds_at_weak) ===")
wv = mp.mpf(9)/mp.mpf(10)
print(f" raw(9/10)={float(raw(wv))}  env={float(env(wv))}  -> raw>env: {raw(wv)>env(wv)} (RAW FAILS)")
print(f" ren(9/10)={float(ren(wv))}  env={float(env(wv))}  -> ren<=env: {ren(wv)<=env(wv)} (REN HOLDS)")
print(f" ren(9/10) exact = 2*(1/10)^2*(2+9/10) = {sp.Rational(2,1)*sp.Rational(1,10)**2*(2+sp.Rational(9,10))} ; env=6/100={sp.Rational(6,100)}")
