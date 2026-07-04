#!/usr/bin/env python3
"""
Circle / Fourier-power pilot for the p>=2 fusion local-CLT residual
    Delta^2_t <D^2>_t  >=  -2                (TwoPointTieSubleading)

Grounded in the ACTUAL Lean objects:
  coeffW w s      = (s+1) * w^(s*(s+2))                      (BondMovingStep.lean:259)
  acN  w n t      = sum_{p<n} coeffW w p * coeffW w (t-p)    (AutoconvGershgorin.lean:173)   [Nat-sub]
  dsq  p t        = (t-2p)^2  (Nat-safe)                     (MeanComplementCovariance:118)
  dmomN w n t     = sum_{p<n} dsq(p,t) * coeffW w p*coeffW w (t-p)  (:149)
  <D^2>_t         = dmomN w n t / acN w n t
  Floor (cleared) : 2 <D^2>_{s+1} <= <D^2>_s + <D^2>_{s+2} + 2   with FIXED window n=s+1
                 (xmsd_iff_d2var / TwoPointTieSubleading, MeanComplementClose.lean)

TWO reframing claims tested:
 (A) additive Fourier-circle identity:  acN(full, n>=t+1)  ==  [f_w^2]_t  where
        f_w(theta) = sum_r coeffW(w,r) e^{i r theta},   [f_w^2]_t = (1/2pi) int f^2 e^{-i t theta}
     i.e. the FULL (untruncated) autoconvolution is EXACTLY the t-th Fourier coeff of the SQUARE.
 (A') dmomN(full) via the two-shift kernel   Phi_t(psi)= sum_p c_p c_{t-p} e^{-i D psi}
        = [ f(theta+psi) f(theta-psi) ]_t ,   <D^2> = -Phi''(0)/Phi(0)  (cumulant curvature).
 (B) whether the Lean WINDOWED object (n=s+1 fixed) still obeys the -2 floor, and how big the
     truncation tail defect (full - windowed) is.
 (C) corner tightness:  Delta^2<D^2> -> -2  at even-s, w->0.
"""
import mpmath as mp
mp.mp.dps = 60

def coeffW(w, s):
    # (s+1) * w^(s*(s+2))
    return (s+1) * w**(s*(s+2))

def natsub(t, p):
    return t - p if t >= p else 0

def acN(w, n, t):
    # sum_{p<n} coeffW w p * coeffW w (t-p)   with Nat subtraction
    return mp.fsum(coeffW(w, p) * coeffW(w, natsub(t, p)) for p in range(n))

def dsq(p, t):
    d = t - 2*p
    return d*d

def dmomN(w, n, t):
    return mp.fsum(dsq(p, t) * coeffW(w, p) * coeffW(w, natsub(t, p)) for p in range(n))

def D2mean(w, n, t):
    return dmomN(w, n, t) / acN(w, n, t)

def full_conv(w, t):
    # untruncated additive autoconvolution  sum_{p=0}^{t} c_p c_{t-p}
    return mp.fsum(coeffW(w, p) * coeffW(w, t-p) for p in range(t+1))

def full_dmom(w, t):
    return mp.fsum(dsq(p, t) * coeffW(w, p) * coeffW(w, t-p) for p in range(t+1))

# ---- (A) additive Fourier-circle identity via numeric quadrature ----
def fourier_sq_coeff(w, t, R):
    # (1/2pi) int_{-pi}^{pi} f(theta)^2 e^{-i t theta} dtheta,  f=sum_{r<=R} c_r e^{i r theta}
    c = [coeffW(w, r) for r in range(R+1)]
    def integrand(th):
        f = mp.fsum(c[r]*mp.e**(1j*r*th) for r in range(R+1))
        return (f*f) * mp.e**(-1j*t*th)
    val = mp.quad(integrand, [-mp.pi, 0, mp.pi]) / (2*mp.pi)
    return val

def phi_second_deriv_coeff(w, t, R, h):
    # dmomN(full) = -Phi''(0)  where Phi_t(psi)=[f(th+psi)f(th-psi)]_t.
    # central 2nd difference in psi of the t-th Fourier coeff.
    c = [coeffW(w, r) for r in range(R+1)]
    def coeff_at(psi):
        def integrand(th):
            fp = mp.fsum(c[r]*mp.e**(1j*r*(th+psi)) for r in range(R+1))
            fm = mp.fsum(c[r]*mp.e**(1j*r*(th-psi)) for r in range(R+1))
            return fp*fm*mp.e**(-1j*t*th)
        return mp.quad(integrand, [-mp.pi, 0, mp.pi]) / (2*mp.pi)
    # Phi''(0) ~ (Phi(h)-2Phi(0)+Phi(-h))/h^2 ; dmomN = -Phi''(0)
    return -(coeff_at(h) - 2*coeff_at(0) + coeff_at(-h)) / (h*h)

print("="*78)
print("(A) additive Fourier-power identity   acN_full(t) == [f_w^2]_t   (R=40 modes)")
print("="*78)
for w in [mp.mpf('0.3'), mp.mpf('0.55'), mp.mpf('0.8')]:
    for t in [0,1,2,3,4,5]:
        comb = full_conv(w, t)
        fou  = fourier_sq_coeff(w, t, 40).real
        rel  = abs(comb-fou)/abs(comb) if comb != 0 else abs(comb-fou)
        print(f"  w={float(w):.2f} t={t}:  comb={mp.nstr(comb,12):>16}  fourier={mp.nstr(fou,12):>16}  rel.err={float(rel):.2e}")

print()
print("="*78)
print("(A') dmomN_full(t) == -Phi''(0) (two-shift kernel, cumulant curvature), w=0.55")
print("="*78)
w = mp.mpf('0.55')
for t in [1,2,3,4,5]:
    comb = full_dmom(w, t)
    integ = phi_second_deriv_coeff(w, t, 40, mp.mpf('1e-3')).real
    rel = abs(comb-integ)/abs(comb) if comb!=0 else abs(comb-integ)
    print(f"  t={t}:  comb dmomN={mp.nstr(comb,12):>16}  -Phi''(0)={mp.nstr(integ,12):>16}  rel.err={float(rel):.2e}")

print()
print("="*78)
print("(B) Lean WINDOWED floor (n=s+1 fixed):  Delta^2<D^2> = <D^2>_s+<D^2>_{s+2}-2<D^2>_{s+1} >= -2 ?")
print("    also: truncation tail defect  (full - windowed) on the t=s+2 window")
print("="*78)
worst = mp.inf
worst_cfg = None
for w in [mp.mpf('0.02'),mp.mpf('0.1'),mp.mpf('0.3'),mp.mpf('0.5'),mp.mpf('0.7'),mp.mpf('0.9'),mp.mpf('0.99')]:
    for s in range(0, 9):
        n = s+1
        Ds  = D2mean(w, n, s)
        Ds1 = D2mean(w, n, s+1)
        Ds2 = D2mean(w, n, s+2)
        d2  = Ds + Ds2 - 2*Ds1          # Delta^2 <D^2>  (must be >= -2)
        # truncation defect on the s+2 window (windowed vs full-range acN):
        acw = acN(w, n, s+2); acf = full_conv(w, s+2)
        tail_rel = abs(acf-acw)/abs(acf)
        if d2 < worst:
            worst = d2; worst_cfg=(float(w),s,float(d2))
        flag = "  <-- floor" if d2 < -2 + 1e-9 else ""
        if s in (0,2,4) or d2 < -1.9:
            print(f"  w={float(w):.2f} s={s} (parity {'even' if s%2==0 else 'odd'}): "
                  f"D2s={mp.nstr(Ds,8):>12} D2s1={mp.nstr(Ds1,8):>12} D2s2={mp.nstr(Ds2,8):>12}  "
                  f"Delta2={mp.nstr(d2,8):>12}  tail(s+2)={float(tail_rel):.1e}{flag}")
print(f"\n  WORST Delta^2<D^2> over grid = {worst_cfg[2]:.10f}  at (w={worst_cfg[0]}, s={worst_cfg[1]})   [floor -2]")

print()
print("="*78)
print("(C) CORNER: even-s, w->0   =>  Delta^2<D^2> -> -2  (two-point-tie saturation)")
print("="*78)
s = 2
for w in [mp.mpf('0.2'),mp.mpf('0.1'),mp.mpf('0.03'),mp.mpf('0.01'),mp.mpf('0.003'),mp.mpf('0.001')]:
    n = s+1
    Ds  = D2mean(w, n, s); Ds1 = D2mean(w, n, s+1); Ds2 = D2mean(w, n, s+2)
    d2  = Ds + Ds2 - 2*Ds1
    print(f"  w={float(w):.4f}: <D^2>_s={mp.nstr(Ds,6):>10} <D^2>_(s+1)={mp.nstr(Ds1,6):>10} "
          f"<D^2>_(s+2)={mp.nstr(Ds2,6):>10}  Delta^2={mp.nstr(d2,10)}   (2+Delta^2={mp.nstr(2+d2,6)})")

print()
print("="*78)
print("(C') odd-s corner for contrast (should be comfortably above -2)")
print("="*78)
s = 3
for w in [mp.mpf('0.1'),mp.mpf('0.01'),mp.mpf('0.001')]:
    n=s+1
    Ds=D2mean(w,n,s);Ds1=D2mean(w,n,s+1);Ds2=D2mean(w,n,s+2);d2=Ds+Ds2-2*Ds1
    print(f"  w={float(w):.4f}: Delta^2={mp.nstr(d2,10)}")

print()
print("="*78)
print("(D) SADDLE asymptotic:  <D^2>_t  vs  theta/discrete-Gaussian prediction 1/(2|log w|)? ")
print("    (large t, fixed w; using FULL range n=t+1 so no truncation)")
print("="*78)
for w in [mp.mpf('0.5'),mp.mpf('0.7'),mp.mpf('0.9')]:
    lg = -mp.log(w)
    for t in [10,20,40]:
        d2m = full_dmom(w,t)/full_conv(w,t)
        # exponent E(p)=p^2+(t-p)^2 + linear; curvature E''=4 in exponent of w => weight
        # exp(-lg*E). Var(p)=1/(2*lg*2)=1/(4lg); D=t-2p => Var(D)=4*Var(p)=1/lg.
        pred = 1/lg
        print(f"  w={float(w):.2f} t={t}: <D^2>={mp.nstr(d2m,8):>12}  1/|log w|={mp.nstr(pred,8):>12}  "
              f"ratio={float(d2m/pred):.4f}")
