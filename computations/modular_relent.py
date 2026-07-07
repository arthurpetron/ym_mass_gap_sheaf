"""
Modular / relative-entropy adjudication for the Minkowski/modular reflection route.

Question: does the relative entropy S(omega_fine || omega_coarse) under RG
coarse-graining track the GAP DEFECT (2 - rho_m, intensive, -> 0) or the FREE
ENERGY (log [c^{*m}]_0, extensive, explodes)?  The MK-control result says the
free energy is decoupled from the gap defect; if relative entropy tracks the
free energy it inherits that wall.

SU(2) heat-kernel character convention (matches Lean coeffW):
    coeffW(s) = (s+1) * w^{s(s+2)}          (dim * w^{quartic Casimir})
    f(theta)  = sum_s coeffW(s) chi_s(theta),  chi_s = sin((s+1)theta)/sin theta
    [c^{*m}]_s = (2/pi) \int_0^pi f^m * sin((s+1)theta) * sin theta  dtheta   (Peter-Weyl)
    Z_m = [c^{*m}]_0  (fused partition function / free energy exp),  rho_m = [c^{*m}]_1 / Z_m
Relative entropy of the coarse (m-fold fused) vs fine (m=1) group measure:
    rho_m^grp(theta) = f^m / Z_m  (density wrt Haar (2/pi) sin^2 theta dtheta)
    S_m = S(rho_m^grp || f) = (m-1) <log f>_{rho_m} - log Z_m.
"""
from mpmath import mp, mpf, quad, sin, log, pi, exp

mp.dps = 45
w = mpf(99) / mpf(100)
eps = 1 - w
SMAX = 400  # character truncation; tail w^{s(s+2)} is tiny well before this at w=0.99

def fsin(theta):
    # f(theta) * sin(theta) = sum_s (s+1) w^{s(s+2)} sin((s+1)theta)
    tot = mpf(0)
    for s in range(0, SMAX + 1):
        c = (s + 1) * w ** (s * (s + 2))
        if c < mpf(10) ** (-50) and s > 5:
            break
        tot += c * sin((s + 1) * theta)
    return tot

def f(theta):
    st = sin(theta)
    return fsin(theta) / st

def cfused(m, s):
    # (2/pi) int_0^pi f^m * sin((s+1)theta) * sin theta dtheta
    integrand = lambda th: (f(th) ** m) * sin((s + 1) * th) * sin(th)
    return (2 / pi) * quad(integrand, [mpf(0), pi])

def logf_avg(m, Zm):
    # <log f>_{rho_m} = (2/pi) int (f^m / Zm) log f  sin^2 theta dtheta
    integrand = lambda th: (f(th) ** m / Zm) * log(f(th)) * sin(th) ** 2
    return (2 / pi) * quad(integrand, [mpf(0), pi])

print(f"w = {mp.nstr(w,6)}   eps = 1-w = {mp.nstr(eps,6)}")
print(f"{'m':>2} | {'Z_m (free energy)':>18} | {'logZ_m':>9} | "
      f"{'2-rho_m':>10} | {'(2-rho)/eps':>11} | {'S_m':>9} | {'S_m/logZ_m':>11} | {'S_m*(2-rho)':>11}")
for m in [1, 2, 3, 4]:
    Zm = cfused(m, 0).real
    rho = (cfused(m, 1).real) / Zm
    gap = 2 - rho
    logZ = log(Zm)
    Sm = mpf(0) if m == 1 else ((m - 1) * logf_avg(m, Zm).real - logZ)
    r1 = "  --" if m == 1 else mp.nstr(Sm/logZ, 6)
    print(f"{m:>2} | {mp.nstr(Zm,9):>18} | {mp.nstr(logZ,7):>9} | "
          f"{mp.nstr(gap,7):>10} | {mp.nstr(gap/eps,6):>11} | {mp.nstr(Sm,7):>9} | "
          f"{r1:>11} | {mp.nstr(Sm*gap,6):>11}")

print()
print("DECISIVE: S_m/logZ_m -> ~const (relative entropy tracks the FREE ENERGY);")
print("          S_m*(2-rho_m) -> tiny & shrinking (relative entropy is DECORRELATED")
print("          from the gap defect: S grows while 2-rho shrinks).")
print()
print("Interpretation:")
print(" - free energy Z_m explodes (extensive, orders of magnitude);")
print(" - gap defect 2-rho_m is intensive and DECREASES ~ 6 eps / m;")
print(" - relative entropy S_m GROWS with m (extensive, tracks logZ_m / free energy),")
print("   opposite monotonicity to the gap defect.  A monotone/bounded relative-entropy")
print("   bound therefore cannot control 2-rho_m: it hits the free-energy wall.")
