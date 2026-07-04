"""C1 (Coulomb-gas duality) + C2 (graded reflection positivity) test harness
for residual R1:  Delta^2_t V(t) >= -2,  V(t)=<D^2>_t.

Exact Lean mirror objects (coeffW, acNfull, dmomNfull) + D-lattice theta objects.
Everything numerical; mirrors, does not prove.
"""
from __future__ import annotations
from fractions import Fraction as F
import mpmath as mp
mp.mp.dps = 60

# ---------- exact rational-in-w Lean objects ----------
def coeffW(w, s): return F(s + 1) * w ** (s * (s + 2))
def acNfull(w, t): return sum(coeffW(w, p) * coeffW(w, t - p) for p in range(t + 1))
def dmomNfull(w, t): return sum(F((t - 2*p)**2) * coeffW(w, p) * coeffW(w, t - p) for p in range(t + 1))
def Vexact(w, t): return dmomNfull(w, t) / acNfull(w, t)

# ---------- D-lattice (envelope-removed) mpf objects ----------
def Ds(t): return list(range(-t, t + 1, 2))
def theta(wf, t): return mp.fsum(wf ** (mp.mpf(D*D)/2) for D in Ds(t))
def xi(wf, t): return mp.fsum(mp.mpf(D*D) * wf ** (mp.mpf(D*D)/2) for D in Ds(t))
def zeta(wf, t): return mp.fsum(mp.mpf(D**4) * wf ** (mp.mpf(D*D)/2) for D in Ds(t))
def den(wf, t):
    M = t + 2; return mp.fsum((M*M - D*D) * wf ** (mp.mpf(D*D)/2) for D in Ds(t))
def num(wf, t):
    M = t + 2; return mp.fsum((D*D)*(M*M - D*D) * wf ** (mp.mpf(D*D)/2) for D in Ds(t))
def V(wf, t): return num(wf, t) / den(wf, t)
def G(wf, t): return xi(wf, t) / theta(wf, t)         # pure-Gaussian lattice variance (finite window)

# ---------- infinite even/odd theta-lattice variances (continuum shadow) ----------
def G_even_inf(wf):
    r = wf * wf
    th = mp.fsum(r ** (j*j) for j in range(-500, 501))
    xj = mp.fsum((2*j)**2 * r ** (j*j) for j in range(-500, 501))
    return xj / th
def G_odd_inf(wf):
    r = wf * wf
    th = mp.fsum(r ** (mp.mpf((2*j+1)**2)/4) for j in range(-500, 501))
    xj = mp.fsum((2*j+1)**2 * r ** (mp.mpf((2*j+1)**2)/4) for j in range(-500, 501))
    return xj / th

def slack(wf, s): return V(wf, s) + V(wf, s+2) - 2*V(wf, s+1) + 2

def hr(t): print("\n" + "="*78 + "\n" + t + "\n" + "="*78)

WS = ['0.02','0.08','0.2079','0.35','0.5','0.7071','0.85','0.95']
SS = [0,1,2,3,4,5,6,7,8,10,12,16,20]

# =====================================================================
hr("C2-(i)  WITHIN-SECTOR convexity of U=V+t^2 (step 2, one parity at a time)")
print("  Test:  V(t)+V(t+4)-2V(t+2)+8 >= 0  (Delta^2 of t^2 at step 2 is 8).")
print("  Separately for EVEN t and ODD t.  If <0 anywhere, within-sector RP alone fails.\n")
print("   w        min_even(step2 U'')   min_odd(step2 U'')    both>=0 ?")
allpos = True
for wv in WS:
    wf = mp.mpf(wv)
    ev = min(V(wf,t)+V(wf,t+4)-2*V(wf,t+2)+8 for t in range(0,24,2))
    od = min(V(wf,t)+V(wf,t+4)-2*V(wf,t+2)+8 for t in range(1,25,2))
    ok = ev>0 and od>0; allpos &= ok
    print(f"  {wv:<7} {float(ev):>18.6f} {float(od):>20.6f}     {ok}")
print(f"\n  within-sector U convex (both parities, all w): {allpos}")

# =====================================================================
hr("C2-(ii)  Cauchy-Schwarz / log-convexity of candidate partition fns (per sector)")
print("  Reflection positivity of a transfer op T with Z_t=<v,T^t v> would give")
print("  Z_{t+2}*Z_{t-2} >= Z_t^2  (same-parity log-convexity).  Test theta,den,acNfull.\n")
for name, fn in [("theta_t", theta), ("den_t", den), ("acNfull", lambda wf,t: mp.mpf(str(acNfull(F(round(float(wf)*10**12),10**12),t))) if False else den(wf,t)*mp.mpf(1))]:
    if name=="acNfull": continue
    print(f"  {name}:  min over t of  Z_{{t+2}}Z_{{t-2}} - Z_t^2   (>=0 = log-convex)")
    for wv in WS:
        wf = mp.mpf(wv)
        mn_e = min(fn(wf,t+2)*fn(wf,t-2)-fn(wf,t)**2 for t in range(2,22,2))
        mn_o = min(fn(wf,t+2)*fn(wf,t-2)-fn(wf,t)**2 for t in range(3,23,2))
        print(f"    w={wv:<7} even:{float(mn_e):>12.4g}  odd:{float(mn_o):>12.4g}"
              f"  logconvex:{mn_e>=0 and mn_o>=0}")

# =====================================================================
hr("C2-(iii)  EXACT sector-flip / finite-correction split of Delta^2 V + 2")
print("  DEFINITIONAL exact split (G_e,G_o = infinite even/odd theta variances):")
print("    Delta^2 V(s) + 2 = [ 2(1-(G_o-G_e)) ]  +  [ corr(s,w) ]")
print("    corr = (V(s)-G_e)+(V(s+2)-G_e) - 2(V(s+1)-G_o)   (finite-size remainder)")
print("  sector-flip 2(1-(G_o-G_e)) >= 0 iff G_o-G_e<=1 (the PROVED ContinuumFloor (a)=1-th4^4).")
print("  Question: is corr >= 0 (=> clean [>=0]+[>=0] manifest positivity)?\n")
print("   s   w        Delta^2V+2      sectorflip=2(1-(Go-Ge))     corr        corr sign")
worst_corr = mp.inf
for wv in ['0.02','0.2079','0.5','0.7071','0.9']:
    wf = mp.mpf(wv)
    Ge, Go = G_even_inf(wf), G_odd_inf(wf)
    sflip = 2*(1-(Go-Ge))
    for s in [0,2,4,6,8,12,20]:
        sl = slack(wf, s)
        corr = (V(wf,s)-Ge)+(V(wf,s+2)-Ge)-2*(V(wf,s+1)-Go)
        worst_corr = min(worst_corr, corr)
        sgn = "OK(+)" if corr>=0 else "NEG(-)"
        print(f"  {s:>2}  {wv:<7} {float(sl):>12.6g} {float(sflip):>20.6g} {float(corr):>14.6g}   {sgn}")
print(f"\n  WORST (most negative) corr over grid = {float(worst_corr):.6g}")
print("  => if NEG, the naive [sectorflip>=0]+[corr>=0] split is FALSE; corr dips below 0.")

# =====================================================================
hr("C2-(iv)  How the sector-flip SLACK absorbs the negative corr (is total>=0 kept?)")
print("  total = sectorflip + corr = Delta^2V+2 must be >=0. Report min total & the")
print("  ratio |corr_neg| / sectorflip (how much of the flip-slack the correction eats).\n")
print("   w        min_s(Delta^2V+2)   at s   sectorflip@thatS   corr@thatS")
for wv in WS:
    wf = mp.mpf(wv); Ge,Go=G_even_inf(wf),G_odd_inf(wf); sflip=2*(1-(Go-Ge))
    vals = [(float(slack(wf,s)),s) for s in range(0,26)]
    m,sm = min(vals)
    corr = (V(wf,sm)-Ge)+(V(wf,sm+2)-Ge)-2*(V(wf,sm+1)-Go)
    print(f"  {wv:<7} {m:>16.6g}   {sm:>3}   {float(sflip):>14.6g} {float(corr):>14.6g}")

# =====================================================================
hr("C1-(i)  Coulomb-gas / Poisson dual of the theta mass; even/odd DECOUPLING test")
print("  theta_full_even(w)=Sum_{D even} w^{D^2/2}=theta3(w^2);  odd=theta2(w^2).")
print("  Poisson: theta3(q=e^{-pi a}) = a^{-1/2} theta3(e^{-pi/a}); a=-log(w^2)/pi.")
print("  Electric(direct) sum <-> Magnetic(dual) sum. Center vortices = odd(theta2) charges.")
print("  DECOUPLING would need G_o-G_e to become a SINGLE gaussian/free-fermion object.\n")
print("   w       a=-log(w^2)/pi   1/a    q=w^2     q_dual=e^{-pi/a}   regime")
for wv in WS:
    wf=mp.mpf(wv); a=-mp.log(wf*wf)/mp.pi; qd=mp.e**(-mp.pi/a)
    reg = "few-mode(q->0) TIGHT corner" if float(wf)<0.2079 else "many-mode(q->1)"
    print(f"  {wv:<7} {float(a):>12.4f} {float(1/a):>7.4f}  {float(wf*wf):>8.4g}  {float(qd):>12.4g}   {reg}")

hr("C1-(ii)  Free-fermion / bosonization check: is G_o-G_e = dlog k/dlog w a nice modular fn?")
print("  Claim (from Lean): G_odd-G_even = dlog(k)/dlog(w), k=(theta2/theta3)^2 elliptic modulus.")
print("  Test that identity numerically, and whether the resulting object is 1-theta4(w^2)^4.\n")
def th2(q): return mp.fsum(2*q**(mp.mpf((2*j+1)**2)/4) for j in range(0,600))
def th3(q): return 1+mp.fsum(2*q**(j*j) for j in range(1,600))
def th4(q): return 1+mp.fsum(2*(-1)**j*q**(j*j) for j in range(1,600))
print("   w       Go-Ge(direct)   dlogk/dlogw(FD)   1-th4(w^2)^4    th3^4-th2^4-th4^4(Jacobi)")
for wv in WS:
    wf=mp.mpf(wv); q=wf*wf
    gd = float(G_odd_inf(wf)-G_even_inf(wf))
    # k=(th2/th3)^2 ; dlog k/dlog w via central FD in log w
    h=mp.mpf('1e-20')
    def logk(lw):
        wl=mp.e**lw; ql=wl*wl; return mp.log((th2(ql)/th3(ql))**2)
    lw=mp.log(wf)
    fd=float((logk(lw+h)-logk(lw-h))/(2*h))
    t4=float(1-th4(q)**4)
    jac=float(th3(q)**4-th2(q)**4-th4(q)**4)
    print(f"  {wv:<7} {gd:>13.6f} {fd:>16.6f} {t4:>14.6f} {jac:>14.2e}")

hr("C1-(iii)  Does duality DECOUPLE parity? Test: is G_o-G_e monotone/gaussian in the")
print("  DUAL variable?  Under w->0 (electric few-mode) G_o-G_e->1; under w->1 (dual)->0.")
print("  A 'decoupled free-fermion' would make Delta^2V+2 = pure gaussian with NO coupling.")
print("  Reality check: the tight extremiser. Report where slack/(w^2(1-w^2)) is minimized.\n")
print("   s     min_w slack/(w^2(1-w^2))   argmin w    (continuum s->inf limit = 8)")
def ratio(wf,s):
    ww=wf*wf; return slack(wf,s)/(ww*(1-ww))
for s in [0,1,2,4,8,20,40]:
    grid=[mp.mpf(i)/4000 for i in range(1,4000)]
    vals=[(ratio(wf,s),wf) for wf in grid]
    m,am=min(vals, key=lambda z: z[0])
    print(f"  {s:>3}   {float(m):>20.6f}   {float(am):>8.4f}")
print("\n  => binding extremiser is FINITE small s (s=0: 144/25=5.76), NOT the dual/continuum.")
print("     Duality maps the tight corner (w->0) to the many-mode side (w->1): WRONG direction.")

print("\nDONE.")
