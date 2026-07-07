import mpmath as mp
mp.mp.dps = 50

# Library convention: exact SU(2) heat-kernel single-plaquette fundamental expectation
#   <(1/2) tr U_p> = w^{C4(1)} = w^3   (C4(1) = s(s+2)=1*3=3, the Casimir-scaled exponent)
# fieldActivity (the Lean obligation upper bound) = 1 - w
# g^2 (heat-kernel time proxy) = -log w, with bracket (1-w) <= -log w <= (1-w)/w

def report(name, f):
    print(f"\n=== candidate z1 = {name} ===")
    print(f"{'w':>8} {'z1':>14} {'1-w':>14} {'ratio z1/(1-w)':>16} {'<= 1-w?':>8}")
    worst = mp.mpf(0)
    worst_w = None
    ok_all = True
    for wv in [0.05,0.1,0.2,0.3,0.4,0.5,0.6,0.7,0.8,0.833,0.9,0.95,0.99,0.999,0.9999]:
        w = mp.mpf(wv)
        z = f(w)
        fa = 1-w
        ratio = z/fa
        ok = z <= fa
        ok_all = ok_all and ok
        if ratio > worst:
            worst = ratio; worst_w = wv
        print(f"{wv:>8} {mp.nstr(z,10):>14} {mp.nstr(fa,10):>14} {mp.nstr(ratio,10):>16} {str(ok):>8}")
    print(f"  worst ratio = {mp.nstr(worst,12)} at w={worst_w};  holds on all sampled: {ok_all}")

# 1. character deviation (library exact): 1 - w^3
report("1 - w^3  (exact fundamental deviation, library)", lambda w: 1 - w**3)

# 2. g^2 exact = -log w
report("-log w  (= g^2 exact)", lambda w: -mp.log(w))

# 3. (1 - w^3)/3   (deviation / Casimir C4(1)=3)
report("(1 - w^3)/3  (deviation / Casimir)", lambda w: (1-w**3)/3)

# 4. genuine single-mode flat SU(2) Gaussian: <cos|B|> = e^{-tau^2/2}(1-tau^2),
#    with tau^2 = g^2/2, g^2 = -log w  => deviation
def z1_gauss(w):
    g2 = -mp.log(w)
    tau2 = g2/2
    return 1 - mp.e**(-tau2/2)*(1-tau2)
report("1 - e^{-g^2/4}(1-g^2/2)  (single-mode flat su(2) Gaussian, tau^2=g^2/2)", z1_gauss)

# 5. what tau^2 makes the flat gaussian match exact heat kernel w^3?  solve e^{-tau^2/2}(1-tau^2)=w^3
# just informational: physical per-component variance
# 6. 1 - w  (fieldActivity itself, trivial equality)
report("1 - w  (fieldActivity, trivial)", lambda w: 1-w)

# second cumulant O(g^4) route
report("6(1-w)^2  (second cumulant envelope, O(g^4))", lambda w: 6*(1-w)**2)
