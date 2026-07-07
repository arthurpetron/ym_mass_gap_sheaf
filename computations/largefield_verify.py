from mpmath import mp, mpf, quad, exp, sqrt, inf, log
mp.dps = 50

# 1) Single-mode Gaussian tail bound:  ∫_M^∞ e^{−φ²/g²} dφ  ≤  (g²/(2M)) e^{−M²/g²}
def tail(M, g):
    return quad(lambda x: exp(-x**2/g**2), [M, inf])
def bound(M, g):
    return (g**2/(2*M))*exp(-M**2/g**2)
print("=== 1) single-mode Gaussian tail  vs  (g^2/2M) e^{-M^2/g^2} ===")
for (M,g) in [(mpf(1),mpf(1)),(mpf(2),mpf(1)),(mpf(3),mpf('0.5')),(mpf(5),mpf(2))]:
    t=tail(M,g); b=bound(M,g)
    print(f"M={M} g={g}:  tail={mp.nstr(t,12)}  bound={mp.nstr(b,12)}  tail<=bound? {t<=b}")

# 2) Suppression vs entropy competition:  net exponent  E = M^2/g^2 - s*V
#    suppression beats entropy iff  M^2 > g^2 s V   (i.e. M > g sqrt(sV))
print("\n=== 2) net exponent  M^2/g^2 - s V ;  threshold M_c = g sqrt(sV) ===")
for (g,s,V) in [(mpf(1),mpf('0.5'),mpf(4)),(mpf('0.3'),mpf(1),mpf(10)),(mpf(2),mpf('0.7'),mpf(3))]:
    Mc = g*sqrt(s*V)
    for M in [Mc*mpf('0.9'), Mc, Mc*mpf('1.1')]:
        net = M**2/g**2 - s*V
        print(f"g={g} s={s} V={V} Mc={mp.nstr(Mc,8)} M={mp.nstr(M,8)}: net={mp.nstr(net,8)} pos? {net>0}")

# 3) Total large-field measure ~ exp(-M^2/g^2 + V*s): at M=Mc it's exp(0)=1 (marginal); M>Mc suppressed
print("\n=== 3) total LF measure exp(-M^2/g^2 + V s) at threshold and beyond ===")
g,s,V = mpf(1),mpf('0.5'),mpf(9)
Mc=g*sqrt(s*V)
for M in [Mc, mpf(3), mpf(4), mpf(6)]:
    val=exp(-M**2/g**2+V*s)
    print(f"M={mp.nstr(M,6)}: measure={mp.nstr(val,10)}")

# 4) No UNIFORM threshold across V->inf (multiscale): for any M, exists V with s V > M^2/g^2
print("\n=== 4) Archimedean: for fixed M,g,s, entropy sV eventually beats M^2/g^2 (need RG) ===")
g,s,M=mpf(1),mpf('0.5'),mpf(10)
thr = M**2/(g**2*s)
print(f"M={M} g={g} s={s}: need V > {mp.nstr(thr,8)} for entropy to win; e.g. V={float(thr)+1}: net={mp.nstr(M**2/g**2 - s*(thr+1),8)}")
