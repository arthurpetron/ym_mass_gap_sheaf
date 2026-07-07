"""
Birkhoff / Hilbert-metric contraction of the positive SU(2) heat-kernel transfer.

Objects:
  coeffW(w,s) = (s+1) w^{s(s+2)}   (character heat-kernel coefficients, all > 0)
  Convolution (transfer) operator on L^2(SU(2)) by the class function
     K_w(theta) = sum_s (s+1) w^{s(s+2)} chi_s(theta),  chi_s(theta)=sin((s+1)theta)/sin theta
  Fourier (convolution) eigenvalue on rep s:  lambda_s = w^{s(s+2)}
    => spectral gap ratio  rho_step = lambda_1/lambda_0 = w^3.
  Character excited/vacuum ratio r1 = coeffW(1)/coeffW(0) = 2 w^3; gap indicator 2 - r1.

Birkhoff: for a positive kernel T, contraction kappa = tanh(Delta/4),
  Delta = projective diameter = sup log[ T(x1,y1)T(x2,y2)/(T(x1,y2)T(x2,y1)) ].
For the convolution kernel T(g,h)=K_w(g h^{-1}), Delta is controlled by
  Delta <= 2 log( maxK / minK ),   maxK ~ K_w(0), minK ~ min over classes.
"""
import mpmath as mp
mp.mp.dps = 50

def coeffW(w, s):
    return (s+1) * w**(s*(s+2))

def chi(s, theta):
    # character of spin s/2: sin((s+1)theta)/sin(theta)
    if abs(mp.sin(theta)) < mp.mpf(10)**(-40):
        return mp.mpf(s+1) * mp.cos((s+1)*theta) / mp.cos(theta)  # l'Hopital-ish; not used at exact 0
    return mp.sin((s+1)*theta)/mp.sin(theta)

def Kw(w, theta, S=4000):
    tot = mp.mpf(0)
    for s in range(S):
        term = coeffW(w, s) * chi(s, theta)
        tot += term
        if s > 20 and abs(coeffW(w,s)) < mp.mpf(10)**(-45):
            break
    return tot

def Kw0(w, S=6000):
    # K_w(0) = sum (s+1)^2 w^{s(s+2)}
    tot = mp.mpf(0)
    for s in range(S):
        term = (s+1)**2 * w**(s*(s+2))
        tot += term
        if s > 20 and term < mp.mpf(10)**(-48):
            break
    return tot

def Kwpi(w, S=6000):
    # K_w(pi) = sum (s+1)^2 (-1)^s w^{s(s+2)}
    tot = mp.mpf(0)
    for s in range(S):
        term = (-1)**s * (s+1)**2 * w**(s*(s+2))
        tot += term
        if s > 20 and (s+1)**2*w**(s*(s+2)) < mp.mpf(10)**(-48):
            break
    return tot

def minK_over_classes(w, ngrid=400):
    # minimise K_w(theta) over theta in (0,pi]; heat kernel positive but min near pi
    lo = mp.mpf(0)
    best = None
    for i in range(1, ngrid+1):
        th = mp.pi * i / ngrid
        v = Kw(w, th)
        if best is None or v < best:
            best = v
    return best

print(f"{'w':>8} {'1-w':>10} {'rho=w^3':>14} {'2-r1':>14} {'2-r1/(1-w)':>12} "
      f"{'K(0)':>14} {'K(pi)':>12} {'Delta~':>12} {'kappa':>14} {'1-kappa':>14} {'(1-k)/(1-w)^1.5':>14}")
for w in [mp.mpf('0.5'), mp.mpf('0.7'), mp.mpf('0.9'), mp.mpf('0.95'),
          mp.mpf('0.99'), mp.mpf('0.995'), mp.mpf('0.999'), mp.mpf('0.9999')]:
    eps = 1 - w
    rho = w**3
    r1 = 2*w**3
    gapind = 2 - r1
    k0 = Kw0(w)
    kpi = abs(Kwpi(w))
    mn = minK_over_classes(w, ngrid=200)
    # Delta bounded by 2 log(maxK/minK); maxK=K(0)
    Delta = 2*mp.log(k0/mn)
    kappa = mp.tanh(Delta/4)
    onemk = 1 - kappa
    print(f"{mp.nstr(w,6):>8} {mp.nstr(eps,4):>10} {mp.nstr(rho,8):>14} "
          f"{mp.nstr(gapind,8):>14} {mp.nstr(gapind/eps,6):>12} "
          f"{mp.nstr(k0,6):>14} {mp.nstr(mn,6):>12} {mp.nstr(Delta,6):>12} "
          f"{mp.nstr(kappa,10):>14} {mp.nstr(onemk,6):>14} {mp.nstr(onemk/eps**mp.mpf('1.5'),6):>14}")

print()
print("=== KEY: exact spectral gap ratio is w^3 -> 1;  character indicator 2-2w^3 -> 0 ~ 6(1-w) ===")
import sympy as sp
w = sp.symbols('w', positive=True)
ind = sp.simplify(2 - 2*w**3)
print("2 - 2w^3 =", sp.factor(ind), "  leading as w->1:", sp.series(ind.subs(w,1-sp.symbols('e')), sp.symbols('e'), 0, 2))
print("w^3 factor: gap ratio -> 1 as w->1.  1 - w^3 =", sp.factor(1-w**3),
      " ~ 3(1-w) at w->1.")
